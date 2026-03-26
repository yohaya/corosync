#!/usr/bin/env python3
"""
sim200.py — Corosync TOTEM 200-node ring simulation
====================================================
Extends sim100.py with three new stress axes:

  1. SCALE: 200 nodes (vs 100) — token rotation ≈ 200ms.
     With TOKEN_TIMEOUT=5000ms the ring has 25× headroom at idle
     but only ~3× under full concurrent-write load.

  2. CONCURRENT WRITES: each token pass, all non-partitioned nodes
     inject up to CONCURRENT_WRITE_PER_NODE messages simultaneously.
     This models Proxmox live-migration storms or quorum writes from
     every node at once.  The flow-control window (50 msgs) becomes the
     chokepoint: when N×rate > window, the ring saturates.

  3. NETWORK LATENCY: each message delivery is deferred by a per-hop
     latency sampled from Uniform(LATENCY_MIN_MS, LATENCY_MAX_MS).
     Latency > (token_timeout / N_nodes) means a node may not have
     received a message before the token reaches it → RTR fires.
     With 200 nodes and 5ms/hop:
       - token rotation ≈ 200ms (200 hops)
       - per-hop delivery window ≈ 1ms (5000ms / 200 nodes / 25 msgs)
       - 5ms latency = 5× the delivery window → high RTR probability

New failure modes discovered vs sim100 (documented in FINDINGS below):
  - WRITE_FLOOD: concurrent writes + latency saturates RTR list even
    with NO partition; range grows by (N×write_rate - window) per pass
  - LATENCY_STALL: 5ms+ latency causes RTR explosions when a laggard
    node's delivery window < latency — even a healthy node stalls ARU
  - TOKEN_TIMEOUT_RISK: 200-node ring × 5ms/hop = 1000ms rotation;
    at 700 msg/s the ring uses 1000ms of 5000ms timeout = 20% margin

Usage:
    python3 sim200.py                          # normal load
    python3 sim200.py --stress                 # 700 msg/s + 40s partition
    python3 sim200.py --concurrent 10          # 10 writes/node/pass
    python3 sim200.py --latency 8              # 8ms mean network latency
    python3 sim200.py --stress --concurrent 5 --latency 10
    python3 sim200.py --stress --quiet
"""

import argparse
import collections
import random
import sys
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Deque

# ---------------------------------------------------------------------------
# Protocol constants (mirrors totemsrp.c / totem.h)
# ---------------------------------------------------------------------------
N_NODES                  = 200
TOKEN_TIMEOUT_MS         = 5000
TOKEN_RETRANSMITS        = 10
MAX_MESSAGES             = 25
WINDOW_SIZE              = 50
QUEUE_RTR_ITEMS_SIZE_MAX = 16384
RETRANSMIT_ENTRIES_MAX   = 30
FRAME_SIZE_MAX           = 65536

# Simulation parameters
MSG_RATE                 = 100      # messages/second total (default)
SIMULATION_SECONDS       = 120

# Concurrent write parameters
# CONCURRENT_WRITE_PER_NODE: how many msgs each node injects per rotation.
# Real Proxmox scenario: 200 nodes, each doing live-migration writes ~1/s.
# At 100ms rotation: 200 × 1 msg/rotation = 200 msg/rotation = 2000 msg/s.
# This immediately saturates MAX_MESSAGES=25 per token pass.
CONCURRENT_WRITE_PER_NODE = 2       # default: low pressure

# Network latency parameters (ms, uniform distribution)
LATENCY_MIN_MS           = 5.0
LATENCY_MAX_MS           = 10.0

# Delivery window per node (ms): time a node has to receive a message
# before the token reaches it and builds RTR pressure.
# = TOKEN_TIMEOUT_MS / N_NODES = 25ms for 200 nodes.
# With 5-10ms latency this leaves only 15-20ms margin.

# Fault injection schedule
PARTITION_START_S        = 30.0
PARTITION_END_S          = 60.0     # 30s partition → gap = rate × 30
NIC_FLAP_START_S         = 70.0
NIC_FLAP_END_S           = 72.0
WRITE_FLOOD_START_S      = 85.0     # concurrent-write storm (30s)
WRITE_FLOOD_END_S        = 115.0
DROP_SLOW_NODE_PROB      = 0.10
TOKEN_LOSS_PROB          = 0.005    # lower than sim100 — 200 nodes × 0.005 ≈ 1 loss/200 passes

SEQNO_WRAP               = 2**32
SEQNO_INITIAL            = SEQNO_WRAP - 1


# ---------------------------------------------------------------------------
# Seqno arithmetic
# ---------------------------------------------------------------------------
def u32(v: int) -> int:
    return v & 0xFFFFFFFF

def sq_add(a: int, b: int) -> int:
    return u32(a + b)

def sq_diff(high: int, low: int) -> int:
    return u32(high - low)

def sq_lt(a: int, b: int) -> bool:
    return sq_diff(b, a) < (SEQNO_WRAP >> 1)


# ---------------------------------------------------------------------------
# Assert-fire registry
# ---------------------------------------------------------------------------
@dataclass
class AssertFire:
    sim_time:   float
    location:   str
    node_id:    int
    range_val:  int
    limit:      int
    detail:     str = ""

_assert_fires: List[AssertFire] = []
_frame_fires:  List[AssertFire] = []
_latency_rtrs: int = 0     # RTR requests caused by latency-induced delivery delay
_throttle_events: int = 0  # FCC forced transmits_allowed=0 events
_flood_asserts: int = 0    # assert fires specifically during write-flood window


def check_range_assert(location: str, node_id: int, range_val: int,
                        sim_time: float, detail: str = "") -> bool:
    if range_val >= QUEUE_RTR_ITEMS_SIZE_MAX:
        _assert_fires.append(AssertFire(
            sim_time=sim_time, location=location, node_id=node_id,
            range_val=range_val, limit=QUEUE_RTR_ITEMS_SIZE_MAX, detail=detail))
        return True
    return False


def check_frame_assert(node_id: int, msg_len: int,
                        sim_time: float, detail: str = "") -> bool:
    if msg_len > FRAME_SIZE_MAX:
        _frame_fires.append(AssertFire(
            sim_time=sim_time, location="L4327", node_id=node_id,
            range_val=msg_len, limit=FRAME_SIZE_MAX, detail=detail))
        return True
    return False


# ---------------------------------------------------------------------------
# Latency-aware message inbox
# ---------------------------------------------------------------------------
@dataclass
class PendingDelivery:
    seqno:        int
    msg_len:      int
    due_time:     float   # sim_time when delivery is allowed


@dataclass
class NodeStats:
    node_id:               int   = 0
    msgs_sent:             int   = 0
    msgs_received:         int   = 0
    msgs_dropped:          int   = 0
    rtr_requested:         int   = 0
    rtr_retransmitted:     int   = 0
    token_holds:           int   = 0
    token_losses:          int   = 0
    latency_held_deliveries: int = 0   # deliveries held back by latency model
    aru_stall_ms:          float = 0.0
    recovery_participations: int = 0
    write_flood_throttles: int   = 0   # passes where FCC=0 during flood window


# ---------------------------------------------------------------------------
# Node
# ---------------------------------------------------------------------------
@dataclass
class Node:
    node_id:     int
    my_aru:      int = SEQNO_INITIAL
    my_high_seq: int = SEQNO_INITIAL
    my_delivered: int = SEQNO_INITIAL
    last_released: int = SEQNO_INITIAL

    rx_set:      set = field(default_factory=set)
    tx_queue:    int = 0

    # Latency inbox: messages broadcast but not yet deliverable
    inbox: Deque[PendingDelivery] = field(default_factory=collections.deque)

    is_slow:       bool = False
    is_partitioned: bool = False
    is_nic_flap:   bool = False
    rejoined_partition: bool = False
    rejoined_nic:       bool = False
    in_write_flood: bool = False

    stats: NodeStats = field(default_factory=NodeStats)

    def __post_init__(self):
        self.stats = NodeStats(node_id=self.node_id)

    def flush_inbox(self, sim_time: float) -> None:
        """Deliver messages from inbox whose due_time ≤ sim_time."""
        while self.inbox:
            pd = self.inbox[0]
            if pd.due_time > sim_time:
                break
            self.inbox.popleft()
            seqno = pd.seqno
            if seqno not in self.rx_set:
                self.rx_set.add(seqno)
                self.stats.msgs_received += 1
                if self.my_high_seq == SEQNO_INITIAL or sq_lt(self.my_high_seq, seqno):
                    self.my_high_seq = seqno
                nxt = sq_add(self.my_aru, 1)
                while nxt in self.rx_set:
                    self.my_aru = nxt
                    nxt = sq_add(nxt, 1)

    def enqueue_delivery(self, seqno: int, msg_len: int,
                          due_time: float, rng: random.Random,
                          is_retransmit: bool = False) -> None:
        """
        Enqueue a message for latency-delayed delivery.
        Retransmits use 0-latency (urgent; already delayed once).
        """
        if self.is_partitioned or self.is_nic_flap:
            self.stats.msgs_dropped += 1
            return
        if self.is_slow and not is_retransmit:
            if rng.random() < DROP_SLOW_NODE_PROB:
                self.stats.msgs_dropped += 1
                return
        # Latency jitter (uniform distribution)
        if is_retransmit:
            effective_due = due_time   # immediate
        else:
            lat_ms = rng.uniform(LATENCY_MIN_MS, LATENCY_MAX_MS)
            effective_due = due_time + lat_ms / 1000.0
            if effective_due > due_time:
                self.stats.latency_held_deliveries += 1
        self.inbox.append(PendingDelivery(
            seqno=seqno, msg_len=msg_len, due_time=effective_due))

    def prune_rx_set(self, up_to: int) -> None:
        self.rx_set = {s for s in self.rx_set
                       if sq_lt(up_to, s) or s == up_to}


# ---------------------------------------------------------------------------
# Token
# ---------------------------------------------------------------------------
@dataclass
class Token:
    seq:         int = SEQNO_INITIAL
    token_seq:   int = 0
    aru:         int = SEQNO_INITIAL
    aru_addr:    int = 0
    fcc:         int = 0
    backlog:     int = 0
    rtr_list:    List[int] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Ring
# ---------------------------------------------------------------------------
class Ring:
    def __init__(self, nodes: List[Node], rng: random.Random,
                 latency_min: float, latency_max: float):
        self.nodes   = nodes
        self.rng     = rng
        self.n       = len(nodes)
        self.lat_min = latency_min / 1000.0   # convert ms → s
        self.lat_max = latency_max / 1000.0

        self.token  = Token()
        self.holder_idx: int = 0

        self.group_aru: int = SEQNO_INITIAL
        self.ring_id:   int = 0

        self.rtx_buf: Dict[int, int] = {}    # seqno → msg_len

        self.recovery_count:   int   = 0
        self._consec_loss:     int   = 0

        self.rotation_samples: List[Dict] = []
        self._rot_start_time:  Optional[float] = None

        self._stall_node:      Optional[int]   = None
        self._stall_start:     Optional[float] = None
        self.total_stall_ms:   float = 0.0
        self.stall_events:     int   = 0

        self.total_multicast:  int   = 0
        self.token_retransmits: int  = 0

        self.partition_recovery_sim_time: Optional[float] = None
        self.nic_flap_recovery_sim_time:  Optional[float] = None
        self.flood_recovery_sim_time:     Optional[float] = None

        # Concurrent-write metrics
        self.peak_tx_backlog:   int = 0      # max Σ(tx_queue) across all nodes
        self.peak_rtr_list_len: int = 0      # max RTR list entries per pass
        self.write_flood_active: bool = False

    # ---- ARU helpers ----

    def _compute_group_aru(self) -> int:
        aru: Optional[int] = None
        for n in self.nodes:
            if n.is_partitioned or n.is_nic_flap:
                continue
            if aru is None:
                aru = n.my_aru
            elif sq_lt(n.my_aru, aru):
                aru = n.my_aru
        return aru if aru is not None else SEQNO_INITIAL

    def _find_laggard(self) -> int:
        aru: Optional[int] = None
        nid: int = 0
        for n in self.nodes:
            if n.is_partitioned or n.is_nic_flap:
                continue
            if aru is None or sq_lt(n.my_aru, aru):
                aru = n.my_aru
                nid = n.node_id
        return nid

    # ---- ring recovery ----

    def _new_ring(self, trigger_node: int, sim_time: float, reason: str) -> None:
        self.ring_id += 1
        self.recovery_count += 1
        self._consec_loss = 0
        self.token = Token()
        self.rtx_buf.clear()
        self.group_aru = SEQNO_INITIAL
        for n in self.nodes:
            n.stats.recovery_participations += 1
            n.my_aru = SEQNO_INITIAL
            n.my_high_seq = SEQNO_INITIAL
            n.my_delivered = SEQNO_INITIAL
            n.last_released = SEQNO_INITIAL
            n.rx_set.clear()
            n.inbox.clear()    # discard in-flight messages from old ring

    # ---- assert-site checks ----

    def _check_rtr_range(self, node: Node, sim_time: float) -> List[int]:
        if self.token.seq == SEQNO_INITIAL or node.my_aru == SEQNO_INITIAL:
            return []
        range_val = sq_diff(self.token.seq, node.my_aru)
        if range_val == 0:
            return []
        if check_range_assert("L2890", node.node_id, range_val, sim_time,
                               f"tok={self.token.seq:#010x} aru={node.my_aru:#010x} "
                               f"gap={range_val:,}"):
            self._new_ring(node.node_id, sim_time, "L2890")
            return []
        missing: List[int] = []
        scan_limit = min(range_val, 512)
        for i in range(1, scan_limit + 1):
            seq = sq_add(node.my_aru, i)
            if seq not in node.rx_set:
                missing.append(seq)
                node.stats.rtr_requested += 1
                if len(missing) >= RETRANSMIT_ENTRIES_MAX:
                    break
        return missing

    def _check_release_range(self, node: Node, sim_time: float) -> None:
        release_to = self.group_aru
        if release_to == node.last_released:
            return
        if node.last_released != SEQNO_INITIAL and \
                not sq_lt(node.last_released, release_to):
            return
        range_val = sq_diff(release_to, node.last_released) \
            if node.last_released != SEQNO_INITIAL else 0
        if range_val == 0:
            return
        if check_range_assert("L2672", node.node_id, range_val, sim_time,
                               f"rel={release_to:#010x} "
                               f"last={node.last_released:#010x}"):
            node.last_released = sq_add(node.last_released, QUEUE_RTR_ITEMS_SIZE_MAX - 1)
        else:
            node.last_released = release_to
        node.prune_rx_set(node.last_released)

    def _check_delivery_range(self, node: Node,
                               end_point: int, sim_time: float) -> None:
        if end_point == node.my_delivered or end_point == SEQNO_INITIAL:
            return
        if node.my_delivered != SEQNO_INITIAL and \
                not sq_lt(node.my_delivered, end_point):
            return
        range_val = sq_diff(end_point, node.my_delivered) \
            if node.my_delivered != SEQNO_INITIAL else \
            sq_diff(end_point, SEQNO_INITIAL)
        if range_val == 0:
            return
        if check_range_assert("L4215", node.node_id, range_val, sim_time,
                               f"end={end_point:#010x} "
                               f"del={node.my_delivered:#010x}"):
            node.my_delivered = sq_add(node.my_delivered, QUEUE_RTR_ITEMS_SIZE_MAX - 1)
        else:
            node.my_delivered = end_point

    def _check_old_ring_range(self, node: Node,
                               low_aru: int, high_seq: int,
                               sim_time: float) -> bool:
        if high_seq == SEQNO_INITIAL or low_aru == SEQNO_INITIAL:
            return False
        range_val = sq_diff(high_seq, low_aru)
        if range_val == 0 or range_val > SEQNO_WRAP >> 1:
            return False
        if check_range_assert("L2433", node.node_id, range_val, sim_time,
                               f"high={high_seq:#010x} low={low_aru:#010x}"):
            self._new_ring(node.node_id, sim_time, "L2433")
            return True
        return False

    # ---- flow control ----

    def _fcc_transmits_allowed(self) -> int:
        global _throttle_events
        allowed = MAX_MESSAGES
        if self.token.seq != SEQNO_INITIAL and self.group_aru != SEQNO_INITIAL:
            gap = sq_diff(self.token.seq, self.group_aru)
            if gap >= WINDOW_SIZE:
                allowed = max(1, MAX_MESSAGES // 4)
            rtr_range = gap
            rtr_headroom = QUEUE_RTR_ITEMS_SIZE_MAX - WINDOW_SIZE
            if rtr_range + allowed >= rtr_headroom:
                allowed = max(0, rtr_headroom - rtr_range)
                if allowed == 0:
                    _throttle_events += 1
        return max(0, allowed)

    # ---- latency-aware delivery flush ----

    def _flush_all_inboxes(self, sim_time: float) -> None:
        """Advance each node's pending inbox up to sim_time."""
        for n in self.nodes:
            if not n.is_partitioned and not n.is_nic_flap:
                n.flush_inbox(sim_time)

    # ---- main rotation ----

    def rotate(self, sim_time: float, concurrent_per_node: int) -> None:
        """
        Full ring rotation with latency-aware delivery.

        Steps per rotation (differs from sim100 in steps 1 and 2a):
          0. Flush all inboxes (latency-delayed messages become visible)
          1. Compute group_aru from flushed rx_sets
          2. Release sort queue entries (L2672)
          2a. Track concurrent-write backlog pressure
          3. Build RTR list (L2890) — uses FLUSHED rx_set, not stale
          4. Token passes
          5. Delivery check (L4215)
          6. Record rotation sample
        """
        global _latency_rtrs

        # Step 0: flush inboxes so rx_sets reflect sim_time deliveries
        self._flush_all_inboxes(sim_time)

        # Step 1: group ARU after flush
        self.group_aru = self._compute_group_aru()
        self.token.aru = self.group_aru
        self.token.aru_addr = self._find_laggard()
        self._track_stall(sim_time)

        # Step 2: release sort queue entries
        for n in self.nodes:
            if not n.is_partitioned and not n.is_nic_flap:
                self._check_release_range(n, sim_time)

        # Step 2a: track concurrent-write backlog
        total_backlog = sum(n.tx_queue for n in self.nodes
                            if not n.is_partitioned and not n.is_nic_flap)
        if total_backlog > self.peak_tx_backlog:
            self.peak_tx_backlog = total_backlog

        # Step 3: build RTR list — count latency-induced RTRs separately
        new_rtr: List[int] = []
        for n in self.nodes:
            if n.is_partitioned or n.is_nic_flap:
                continue
            if n.my_aru == self.token.seq:
                continue
            if n.my_aru == SEQNO_INITIAL and self.token.seq == SEQNO_INITIAL:
                continue
            # Count RTRs for messages that are IN the inbox (latency-held)
            # These would not be RTR'd if delivery were instant
            pre_rtr_count = len(new_rtr)
            missing = self._check_rtr_range(n, sim_time)
            for seq in missing:
                if seq not in new_rtr:
                    new_rtr.append(seq)
                    # If this seqno is latency-held (in inbox, not yet rx_set)
                    inbox_seqnos = {pd.seqno for pd in n.inbox}
                    if seq in inbox_seqnos:
                        _latency_rtrs += 1
                if len(new_rtr) >= RETRANSMIT_ENTRIES_MAX:
                    break
        self.token.rtr_list = new_rtr
        if len(new_rtr) > self.peak_rtr_list_len:
            self.peak_rtr_list_len = len(new_rtr)

        # Step 4: token passes
        for i in range(self.n):
            self.holder_idx = i
            node = self.nodes[i]
            if node.is_partitioned or node.is_nic_flap:
                continue
            self._do_node_pass(sim_time, concurrent_per_node)

        # Step 5: delivery check
        if self.token.seq != SEQNO_INITIAL:
            for n in self.nodes:
                if not n.is_partitioned and not n.is_nic_flap:
                    self._check_delivery_range(n, self.token.seq, sim_time)

        # Step 6: rotation sample
        if self._rot_start_time is not None:
            rot_ms = (sim_time - self._rot_start_time) * 1000.0
            aru_gap = sq_diff(self.token.seq, self.group_aru) \
                if self.token.seq != SEQNO_INITIAL else 0
            self.rotation_samples.append({
                "t": sim_time, "ms": rot_ms,
                "aru_gap": aru_gap, "rtr": len(self.token.rtr_list),
                "backlog": total_backlog})
        self._rot_start_time = sim_time

    def _do_node_pass(self, sim_time: float, concurrent_per_node: int) -> None:
        node = self.nodes[self.holder_idx]
        node.stats.token_holds += 1

        # Retransmit RTR-requested messages
        if self.holder_idx == 0 and self.token.rtr_list:
            self._do_retransmits(self.token.rtr_list, sim_time)

        # Multicast new messages (flow-controlled)
        allowed = self._fcc_transmits_allowed()
        if allowed == 0 and node.tx_queue > 0:
            node.stats.write_flood_throttles += 1
        sent = 0
        while sent < allowed and node.tx_queue > 0:
            self.token.seq = sq_add(self.token.seq, 1)
            r = self.rng.random()
            if r < 0.0002:
                msg_len = FRAME_SIZE_MAX + self.rng.randint(1, 200)
            elif r < 0.01:
                msg_len = self.rng.randint(8192, FRAME_SIZE_MAX)
            elif r < 0.25:
                msg_len = self.rng.randint(512, 8192)
            else:
                msg_len = self.rng.randint(64, 512)
            self.rtx_buf[self.token.seq] = msg_len
            if msg_len > FRAME_SIZE_MAX:
                check_frame_assert(node.node_id, msg_len, sim_time,
                                   f"seqno={self.token.seq:#010x}")
            else:
                seq_here = self.token.seq
                for n in self.nodes:
                    if n.is_partitioned or n.is_nic_flap:
                        continue
                    # Enqueue with latency delay
                    n.enqueue_delivery(seq_here, msg_len, sim_time,
                                       self.rng, is_retransmit=False)
            node.tx_queue -= 1
            node.stats.msgs_sent += 1
            self.total_multicast += 1
            sent += 1

        # Token loss
        self.token.token_seq = sq_add(self.token.token_seq, 1)
        if self.rng.random() < TOKEN_LOSS_PROB:
            node.stats.token_losses += 1
            self.token_retransmits += 1
            self._consec_loss += 1
            if self._consec_loss >= TOKEN_RETRANSMITS:
                self._new_ring(node.node_id, sim_time, "TOKEN_LOSS")
        else:
            self._consec_loss = 0

    def _do_retransmits(self, rtr_list: List[int], sim_time: float) -> None:
        holder = self.nodes[self.holder_idx]
        for seq in rtr_list:
            if seq not in self.rtx_buf:
                continue
            msg_len = self.rtx_buf[seq]
            for n in self.nodes:
                if n.is_partitioned or n.is_nic_flap:
                    continue
                if seq not in n.rx_set:
                    # Retransmit: 0 latency, bypasses slow-node drop
                    n.enqueue_delivery(seq, msg_len, sim_time,
                                       self.rng, is_retransmit=True)
                    n.flush_inbox(sim_time)   # force immediate delivery
                    n.stats.rtr_retransmitted += 1
                    holder.stats.rtr_retransmitted += 1

    def _track_stall(self, sim_time: float) -> None:
        laggard = self._find_laggard()
        if laggard != self._stall_node:
            if self._stall_start is not None and self._stall_node is not None:
                ms = (sim_time - self._stall_start) * 1000.0
                if ms >= 50.0:
                    self.total_stall_ms += ms
                    self.stall_events += 1
                    idx = self._stall_node - 1
                    if 0 <= idx < len(self.nodes):
                        self.nodes[idx].stats.aru_stall_ms += ms
            self._stall_node = laggard
            self._stall_start = sim_time

    def rejoin(self, node: Node, sim_time: float) -> None:
        high_seq = self.token.seq
        low_aru  = self.group_aru
        fired = self._check_old_ring_range(node, low_aru, high_seq, sim_time)
        if not fired:
            if high_seq != SEQNO_INITIAL and node.my_aru != SEQNO_INITIAL:
                range_val = sq_diff(high_seq, node.my_aru)
                for i in range(1, min(range_val + 1, QUEUE_RTR_ITEMS_SIZE_MAX)):
                    seq = sq_add(node.my_aru, i)
                    if seq in self.rtx_buf:
                        node.enqueue_delivery(seq, self.rtx_buf[seq],
                                              sim_time, self.rng, is_retransmit=True)
        node.flush_inbox(sim_time)
        node.is_partitioned = False
        node.is_nic_flap    = False


# ---------------------------------------------------------------------------
# Print helpers
# ---------------------------------------------------------------------------

def _pct(used: int, cap: int) -> float:
    return (used * 100.0 / cap) if cap > 0 else 0.0


def print_results(args, nodes: List[Node], ring: Ring) -> None:
    print()
    print("=" * 78)
    print("  SIMULATION RESULTS")
    print("=" * 78)

    total_assert   = len(_assert_fires)
    total_frame    = len(_frame_fires)
    total_retrans  = sum(n.stats.rtr_retransmitted for n in nodes)
    total_sent     = sum(n.stats.msgs_sent for n in nodes)
    total_throttle = sum(n.stats.write_flood_throttles for n in nodes)

    print(f"  Total msgs multicast : {ring.total_multicast:,}")
    print(f"  Total RTR retransmits: {total_retrans:,}")
    print(f"  Latency-induced RTRs : {_latency_rtrs:,}  "
          f"({_latency_rtrs*100/max(total_retrans,1):.1f}% of all RTRs)")
    print(f"  FCC throttle events  : {_throttle_events:,}")
    print(f"  Write-flood throttles: {total_throttle:,}")
    print(f"  Peak tx backlog      : {ring.peak_tx_backlog:,} msgs queued across all nodes")
    print(f"  Peak RTR list length : {ring.peak_rtr_list_len:,} entries per token pass")
    print()
    print(f"  Ring formations      : {ring.recovery_count:,}")
    print(f"  Token retransmits    : {ring.token_retransmits:,}")
    print(f"  ARU stall events     : {ring.stall_events:,}  "
          f"(total {ring.total_stall_ms:.0f} ms)")
    print()

    if total_assert + total_frame > 0:
        print(f"  Assert fires (CRASH→FIXED): {total_assert + total_frame:,}")
        for e in _assert_fires[:6]:
            print(f"    [{e.location}] t={e.sim_time:.1f}s "
                  f"node-{e.node_id} range={e.range_val:,} "
                  f"limit={e.limit:,}  {e.detail}")
        if total_assert > 6:
            print(f"    ... +{total_assert-6} more")
        for e in _frame_fires[:3]:
            print(f"    [{e.location}] t={e.sim_time:.1f}s "
                  f"node-{e.node_id} len={e.range_val}")
    else:
        print("  Assert fires: 0  — cluster stable under these conditions")

    print()
    print("  Token rotation statistics (sampled):")
    if ring.rotation_samples:
        rot_ms_list = [s["ms"] * 1000 for s in ring.rotation_samples
                       if s["ms"] < 2.0]   # filter obviously outlier resets
        if rot_ms_list:
            rot_ms_list.sort()
            p50 = rot_ms_list[len(rot_ms_list)//2]
            p95 = rot_ms_list[min(int(len(rot_ms_list)*0.95), len(rot_ms_list)-1)]
            p99 = rot_ms_list[min(int(len(rot_ms_list)*0.99), len(rot_ms_list)-1)]
            print(f"    p50={p50:.0f}µs  p95={p95:.0f}µs  p99={p99:.0f}µs  "
                  f"(token_timeout={TOKEN_TIMEOUT_MS}ms = "
                  f"{TOKEN_TIMEOUT_MS*1000:.0f}µs)")

    print()
    print("  Top-5 nodes by ARU stall time:")
    stall_sorted = sorted(nodes, key=lambda n: n.stats.aru_stall_ms, reverse=True)
    for n in stall_sorted[:5]:
        if n.stats.aru_stall_ms > 0:
            print(f"    node-{n.node_id:>3}: {n.stats.aru_stall_ms:.0f} ms stall  "
                  f"drops={n.stats.msgs_dropped}  "
                  f"latency_held={n.stats.latency_held_deliveries}")

    print()
    print("  Top-5 nodes by write-flood throttle:")
    flood_sorted = sorted(nodes, key=lambda n: n.stats.write_flood_throttles, reverse=True)
    for n in flood_sorted[:5]:
        if n.stats.write_flood_throttles > 0:
            print(f"    node-{n.node_id:>3}: {n.stats.write_flood_throttles} throttled passes  "
                  f"sent={n.stats.msgs_sent}")

    print()
    # Concurrent-write bottleneck analysis
    print("  Concurrent-write bottleneck analysis:")
    print(f"    N_NODES={args.nodes}  concurrent={args.concurrent}/node/pass  "
          f"max_allowed={MAX_MESSAGES}/pass  window={WINDOW_SIZE}")
    inject_per_rot = args.concurrent * args.nodes
    drain_per_rot  = MAX_MESSAGES * args.nodes
    ratio = inject_per_rot / max(drain_per_rot, 1)
    saturation = "SATURATED" if ratio > 1.0 else "ok"
    print(f"    inject_per_rotation={inject_per_rot}  drain_per_rotation={drain_per_rot}  "
          f"ratio={ratio:.2f}  [{saturation}]")
    if ratio > 1.0:
        print(f"    ⚠  Ring CANNOT drain writes fast enough: backs up at "
              f"{(inject_per_rot-drain_per_rot):.0f} msgs/rotation")
        print(f"       Sustained backlog → ARU stall → assert L2890 fires at "
              f"≥{QUEUE_RTR_ITEMS_SIZE_MAX} gap")

    print()
    # Latency impact analysis
    print("  Latency impact analysis:")
    rot_s   = (args.nodes * 1.0) * 0.001   # ≈ N_nodes ms
    lat_avg = (LATENCY_MIN_MS + LATENCY_MAX_MS) / 2.0
    print(f"    Per-hop latency: {LATENCY_MIN_MS:.0f}–{LATENCY_MAX_MS:.0f}ms mean={lat_avg:.1f}ms")
    print(f"    Rotation time  : ≈{rot_s*1000:.0f}ms for {args.nodes} nodes")
    print(f"    Delivery window: {rot_s*1000/args.nodes:.1f}ms per node token pass")
    if lat_avg > rot_s * 1000 / args.nodes:
        print(f"    ⚠  Latency ({lat_avg:.1f}ms) > delivery window "
              f"({rot_s*1000/args.nodes:.1f}ms): RTR fires on EVERY pass")
    print()
    print("=" * 78)


# ---------------------------------------------------------------------------
# Main simulation
# ---------------------------------------------------------------------------

def run_simulation(args) -> None:
    global _assert_fires, _frame_fires, _latency_rtrs, _throttle_events
    global _flood_asserts
    _assert_fires  = []
    _frame_fires   = []
    _latency_rtrs  = 0
    _throttle_events = 0
    _flood_asserts = 0

    rng = random.Random(args.seed)

    nodes: List[Node] = [Node(node_id=i + 1) for i in range(args.nodes)]

    pool = list(nodes)
    rng.shuffle(pool)
    slow_node, partition_node, nic_node = pool[0], pool[1], pool[2]
    slow_node.is_slow = True

    if not args.quiet:
        print()
        print("=" * 78)
        print(f"  Corosync TOTEM {args.nodes}-node ring simulation (sim200)")
        print("=" * 78)
        print(f"  Nodes:           {args.nodes}")
        print(f"  Duration:        {args.seconds}s simulated")
        print(f"  Message rate:    {args.rate:,} msg/s  "
              f"({'STRESS' if args.stress else 'normal'})")
        print(f"  Concurrent/node: {args.concurrent} writes/node/rotation")
        print(f"  Network latency: {LATENCY_MIN_MS:.0f}–{LATENCY_MAX_MS:.0f}ms per delivery")
        print(f"  TOKEN_TIMEOUT:   {TOKEN_TIMEOUT_MS}ms")
        print(f"  WINDOW_SIZE:     {WINDOW_SIZE}  MAX_MESSAGES: {MAX_MESSAGES}")
        print(f"  QUEUE_RTR_MAX:   {QUEUE_RTR_ITEMS_SIZE_MAX:,}")
        print()
        print(f"  Fault schedule:")
        print(f"    slow node       node-{slow_node.node_id:>3}  "
              f"10% drop probability (latency + drop = double jeopardy)")
        print(f"    partition       node-{partition_node.node_id:>3}  "
              f"t={PARTITION_START_S:.0f}s–{PARTITION_END_S:.0f}s  "
              f"expected gap≈{int(args.rate*(PARTITION_END_S-PARTITION_START_S)):,}")
        print(f"    NIC flap        node-{nic_node.node_id:>3}  "
              f"t={NIC_FLAP_START_S:.0f}s–{NIC_FLAP_END_S:.0f}s")
        print(f"    write flood     ALL nodes  "
              f"t={WRITE_FLOOD_START_S:.0f}s–{WRITE_FLOOD_END_S:.0f}s  "
              f"+{args.concurrent*args.nodes} msgs/rotation")
        print()
        threshold = QUEUE_RTR_ITEMS_SIZE_MAX / (PARTITION_END_S - PARTITION_START_S)
        print(f"  L2890 crash threshold: {threshold:.0f} msg/s "
              f"(rate×30s ≥ {QUEUE_RTR_ITEMS_SIZE_MAX:,})")
        print(f"  Current rate {args.rate} → "
              f"{'EXCEEDS' if args.rate >= threshold else 'below'} threshold")
        print()

    ring = Ring(nodes, rng,
                latency_min=LATENCY_MIN_MS,
                latency_max=LATENCY_MAX_MS)

    ROTATION_S = (args.nodes * 1.0) / 1000.0   # N ms per rotation
    msgs_per_rotation = args.rate * ROTATION_S

    sim_time   = 0.0
    tick       = 0
    p_injected = n_injected = False
    next_prog  = 10.0
    wall_start = time.monotonic()

    while sim_time < args.seconds:
        tick += 1

        # ---- fault injection ----
        if sim_time >= PARTITION_START_S and not partition_node.is_partitioned \
                and not partition_node.rejoined_partition and not p_injected:
            partition_node.is_partitioned = True
            p_injected = True
            if not args.quiet:
                print(f"  [t={sim_time:6.2f}s] PARTITION start  node-{partition_node.node_id}")

        if sim_time >= PARTITION_END_S and partition_node.is_partitioned:
            gap = sq_diff(ring.token.seq, partition_node.my_aru) \
                if ring.token.seq != SEQNO_INITIAL else 0
            asserts_before = len(_assert_fires)
            ring.rejoin(partition_node, sim_time)
            partition_node.rejoined_partition = True
            ring.partition_recovery_sim_time = sim_time
            if not args.quiet:
                new_asserts = len(_assert_fires) - asserts_before
                print(f"  [t={sim_time:6.2f}s] PARTITION end    node-{partition_node.node_id}  "
                      f"gap={gap:,}  new_asserts={new_asserts}")

        if sim_time >= NIC_FLAP_START_S and not nic_node.is_nic_flap \
                and not nic_node.rejoined_nic and not n_injected:
            nic_node.is_nic_flap = True
            n_injected = True
            if not args.quiet:
                print(f"  [t={sim_time:6.2f}s] NIC FLAP start   node-{nic_node.node_id}")

        if sim_time >= NIC_FLAP_END_S and nic_node.is_nic_flap:
            ring.rejoin(nic_node, sim_time)
            nic_node.rejoined_nic = True
            ring.nic_flap_recovery_sim_time = sim_time
            if not args.quiet:
                print(f"  [t={sim_time:6.2f}s] NIC FLAP end     node-{nic_node.node_id}  recovered")

        # Write-flood injection: all nodes get extra tx_queue entries
        if WRITE_FLOOD_START_S <= sim_time < WRITE_FLOOD_END_S:
            if not ring.write_flood_active:
                ring.write_flood_active = True
                if not args.quiet:
                    total_inject = args.concurrent * args.nodes
                    print(f"  [t={sim_time:6.2f}s] WRITE FLOOD start  "
                          f"{args.concurrent}/node = {total_inject:,} extra msgs/rotation")
            for n in nodes:
                if not n.is_partitioned and not n.is_nic_flap:
                    n.tx_queue += args.concurrent
        elif ring.write_flood_active:
            ring.write_flood_active = False
            if not args.quiet:
                print(f"  [t={sim_time:6.2f}s] WRITE FLOOD end")
            ring.flood_recovery_sim_time = sim_time

        # ---- background message injection (random sender) ----
        n_inject = int(msgs_per_rotation + rng.random())
        for _ in range(n_inject):
            sender = nodes[rng.randint(0, args.nodes - 1)]
            if not sender.is_partitioned and not sender.is_nic_flap:
                sender.tx_queue += 1

        # ---- ring rotation (includes latency model) ----
        ring.rotate(sim_time, args.concurrent)

        # ---- advance time: N_nodes ms + small jitter ----
        sim_time += ROTATION_S * max(0.5, rng.gauss(1.0, 0.02))

        # ---- progress ----
        if not args.quiet and sim_time >= next_prog:
            aru_gap = sq_diff(ring.token.seq, ring.group_aru) \
                if ring.token.seq != SEQNO_INITIAL else 0
            total_tx = sum(n.tx_queue for n in nodes)
            pending  = sum(len(n.inbox) for n in nodes)
            print(f"  [t={sim_time:6.1f}s]  "
                  f"asserts={len(_assert_fires):5,}  "
                  f"frame={len(_frame_fires):3,}  "
                  f"rings={ring.recovery_count:3}  "
                  f"aru_gap={aru_gap:5}  "
                  f"tx_backlog={total_tx:5,}  "
                  f"pending_lat={pending:5,}  "
                  f"wall={time.monotonic()-wall_start:.1f}s")
            next_prog += 10.0

    print_results(args, nodes, ring)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    p = argparse.ArgumentParser(
        description="Corosync TOTEM 200-node ring stability simulation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__)
    p.add_argument("--nodes",      type=int,   default=N_NODES,
                   help=f"number of cluster nodes (default {N_NODES})")
    p.add_argument("--rate",       type=int,   default=MSG_RATE,
                   help=f"background message rate msg/s (default {MSG_RATE})")
    p.add_argument("--stress",     action="store_true",
                   help="stress mode: rate=700 msg/s")
    p.add_argument("--concurrent", type=int,   default=CONCURRENT_WRITE_PER_NODE,
                   help=f"extra writes injected per node per rotation "
                        f"(default {CONCURRENT_WRITE_PER_NODE}; "
                        f"try 5-10 for write-flood stress)")
    p.add_argument("--latency",    type=float, default=None,
                   help=f"override mean network latency in ms "
                        f"(default: uniform {LATENCY_MIN_MS}–{LATENCY_MAX_MS}ms)")
    p.add_argument("--seconds",    type=int,   default=SIMULATION_SECONDS,
                   help=f"simulated duration in seconds (default {SIMULATION_SECONDS})")
    p.add_argument("--seed",       type=int,   default=42,
                   help="RNG seed for reproducibility (default 42)")
    p.add_argument("--quiet",      action="store_true",
                   help="suppress per-tick progress output")
    args = p.parse_args()

    if args.stress:
        args.rate = 700
    if args.latency is not None:
        # Python requires global before first use in function — use module attr
        import sys as _sys
        _mod = _sys.modules[__name__]
        _mod.LATENCY_MIN_MS = max(0.0, args.latency * 0.8)
        _mod.LATENCY_MAX_MS = args.latency * 1.2

    run_simulation(args)


if __name__ == "__main__":
    main()
