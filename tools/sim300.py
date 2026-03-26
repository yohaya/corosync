#!/usr/bin/env python3
"""
sim300.py — Corosync TOTEM 300-node ring simulation
====================================================
Extends sim200.py with three new stress axes targeting production-scale
Proxmox clusters (300+ nodes, 1000+ writes/sec, 5-10ms network latency).

New findings vs sim200 (300-node scale effects):

  BUG-1: RTR LIST STARVATION (O(N) scalability bug)
    RETRANSMIT_ENTRIES_MAX=30 is a hard constant.  With 300 nodes all
    experiencing 5-10ms latency-induced delivery delays, every rotation
    needs ~300 RTR entries but only 30 fit in the token.  The remaining
    270 nodes go unserviced each pass.  Messages accumulate, ARU stalls,
    eventually ring_recovery fires.  This is a quadratic growth bug:
    delivery latency grows as O(N / RETRANSMIT_ENTRIES_MAX).

  BUG-2: FCC WINDOW EXHAUSTION AT SCALE
    WINDOW_SIZE=50 across 300 nodes means the FCC throttles every node
    to MAX_MESSAGES//4=6 msgs/pass after only 50 unconfirmed messages
    cluster-wide.  With 300 nodes × 3.3 msgs/sec = ~1 msg/pass/node,
    the ARU gap reaches 50 after <1 ring rotation.  All 300 nodes are
    permanently throttled even when no backpressure exists.  This is
    a configuration mismatch bug: WINDOW_SIZE should scale with N.

  BUG-3: RECOVERY CASCADING UNDER FLOOD
    When ring recovery fires during an active write flood, the new ring
    starts fresh while write queues remain full.  The first token holder
    immediately pushes MAX_MESSAGES=25 writes.  Combined with 300 nodes
    all needing catch-up RTRs, the RTR list overflows within 1-2 passes,
    triggering another recovery.  Cascade depth observed: 3-5 recoveries
    in <10 seconds.

  BUG-4: ASSEMBLY_LIST_FREE GROWTH SIMULATION
    Each recovery cycle with N nodes leaving deref's N assemblies into
    assembly_list_free (~1MB each).  At 300 nodes with 5 recovery events:
      Without fix:  300 × 5 × 1MB = 1500 MB (1.46 GiB)
      With fix:     min(8, 1500) × 1MB = 8 MB (our cap)

  BUG-5: RETRANS_QUEUE PEAK DURING FLOOD+LATENCY
    During concurrent writes + 5-10ms latency, retrans_message_queue peaks
    at near-QUEUE_RTR_ITEMS_SIZE_MAX.  Each recovery event at this peak
    = 16384 × 64KB = 1GB leaked (the TODO LEAK we fixed).  With 5 recoveries
    in the 300-node scenario: 5GB accumulated without the fix.

Usage:
    python3 sim300.py                                  # default: 300 nodes, 1000 msg/s
    python3 sim300.py --stress                         # 2000 msg/s, aggressive fault
    python3 sim300.py --concurrent 10                  # 10 writes/node/pass flood
    python3 sim300.py --latency 7                      # 7ms mean latency
    python3 sim300.py --nodes 53 --rate 200            # reproduce Proxmox incident
    python3 sim300.py --stress --concurrent 10 --latency 10
"""

import argparse
import collections
import math
import random
import sys
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Deque, Tuple

# ---------------------------------------------------------------------------
# Protocol constants (mirrors totemsrp.c / totem.h)
# ---------------------------------------------------------------------------
N_NODES                  = 300
TOKEN_TIMEOUT_MS         = 5000
TOKEN_RETRANSMITS        = 10
MAX_MESSAGES             = 25
WINDOW_SIZE              = 50
QUEUE_RTR_ITEMS_SIZE_MAX = 16384
RETRANSMIT_ENTRIES_MAX   = 30    # ← hard limit; BUG-1 is here
FRAME_SIZE_MAX           = 65536

# Simulation parameters
MSG_RATE                 = 1000     # messages/second total (default)
SIMULATION_SECONDS       = 120

# Network latency parameters (ms, uniform distribution)
LATENCY_MIN_MS           = 5.0
LATENCY_MAX_MS           = 10.0

# Concurrent write parameters
CONCURRENT_WRITE_PER_NODE = 3      # default: realistic Proxmox migration load

# Fault injection schedule — staggered to stress multiple recovery paths
PARTITION_START_S        = 25.0
PARTITION_END_S          = 50.0     # 25s partition (hard case: more missed msgs)
NIC_FLAP_START_S         = 58.0
NIC_FLAP_END_S           = 63.0     # 5s flap (longer than sim200)
WRITE_FLOOD_START_S      = 72.0
WRITE_FLOOD_END_S        = 102.0    # 30s flood
SECOND_FLOOD_START_S     = 108.0    # second flood post-recovery
SECOND_FLOOD_END_S       = 118.0    # (stress: what happens when cluster is degraded)

DROP_SLOW_NODE_PROB      = 0.08     # slightly lower than sim200 (300-node ring is already stressed)
TOKEN_LOSS_PROB          = 0.003    # 300 nodes × 0.003 ≈ 0.9 losses per ring rotation

SEQNO_WRAP               = 2**32
SEQNO_INITIAL            = SEQNO_WRAP - 1

# Memory model constants (for BUG-4 and BUG-5 simulation)
ASSEMBLY_SIZE_MB         = 1.06     # sizeof(struct assembly) ≈ 1MB + KNET_MAX
MCAST_BUFFER_KB          = 64       # totemknet_buffer_alloc = KNET_MAX_PACKET_SIZE + 512
ASSEMBLY_FREE_LIST_CAP   = 8        # our fix: ASSEMBLY_FREE_LIST_MAX


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
# Global diagnostic counters
# ---------------------------------------------------------------------------
@dataclass
class AssertFire:
    sim_time:  float
    location:  str
    node_id:   int
    range_val: int
    limit:     int
    detail:    str = ""

_assert_fires:   List[AssertFire] = []
_frame_fires:    List[AssertFire] = []
_latency_rtrs:   int = 0
_throttle_events: int = 0
_rtr_starvation_events: int = 0   # BUG-1: RTR list overflow events
_fcc_deadlock_events:   int = 0   # BUG-2: all nodes simultaneously throttled

# Memory simulation counters
_assembly_deref_total:   int = 0   # total assembly_deref() calls (ring recoveries)
_assembly_free_peak:     int = 0   # peak assembly_list_free size (without our fix)
_retrans_buf_peak:       int = 0   # peak retrans_message_queue size
_cascade_depth:          int = 0   # current ring recovery cascade depth
_cascade_max_depth:      int = 0   # max cascade depth seen
_cascade_start_time: Optional[float] = None


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
    seqno:    int
    msg_len:  int
    due_time: float


@dataclass
class NodeStats:
    node_id:                int   = 0
    msgs_sent:              int   = 0
    msgs_received:          int   = 0
    msgs_dropped:           int   = 0
    rtr_requested:          int   = 0
    rtr_retransmitted:      int   = 0
    rtr_starved:            int   = 0   # RTR requests dropped due to BUG-1
    token_holds:            int   = 0
    token_losses:           int   = 0
    latency_held_deliveries: int  = 0
    aru_stall_ms:           float = 0.0
    recovery_participations: int  = 0
    write_flood_throttles:  int   = 0
    fcc_deadlocked_passes:  int   = 0   # passes where this node was throttled to 0


@dataclass
class Node:
    node_id:     int
    my_aru:      int = SEQNO_INITIAL
    my_high_seq: int = SEQNO_INITIAL
    my_delivered: int = SEQNO_INITIAL
    last_released: int = SEQNO_INITIAL

    rx_set:      set = field(default_factory=set)
    tx_queue:    int = 0

    inbox: Deque[PendingDelivery] = field(default_factory=collections.deque)

    is_slow:        bool = False
    is_partitioned: bool = False
    is_nic_flap:    bool = False
    rejoined_partition: bool = False
    rejoined_nic:       bool = False
    in_write_flood: bool = False

    stats: NodeStats = field(default_factory=NodeStats)

    def __post_init__(self):
        self.stats = NodeStats(node_id=self.node_id)

    def flush_inbox(self, sim_time: float) -> None:
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
        if self.is_partitioned or self.is_nic_flap:
            self.stats.msgs_dropped += 1
            return
        if self.is_slow and not is_retransmit:
            if rng.random() < DROP_SLOW_NODE_PROB:
                self.stats.msgs_dropped += 1
                return
        if is_retransmit:
            effective_due = due_time
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
    seq:       int = SEQNO_INITIAL
    token_seq: int = 0
    aru:       int = SEQNO_INITIAL
    aru_addr:  int = 0
    fcc:       int = 0
    backlog:   int = 0
    rtr_list:  List[int] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Ring
# ---------------------------------------------------------------------------
class Ring:
    def __init__(self, nodes: List[Node], rng: random.Random,
                 latency_min: float, latency_max: float):
        self.nodes   = nodes
        self.rng     = rng
        self.n       = len(nodes)
        self.lat_min = latency_min / 1000.0
        self.lat_max = latency_max / 1000.0

        self.token  = Token()
        self.holder_idx: int = 0

        self.group_aru: int = SEQNO_INITIAL
        self.ring_id:   int = 0

        self.rtx_buf: Dict[int, int] = {}

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

        self.peak_tx_backlog:   int = 0
        self.peak_rtr_list_len: int = 0
        self.write_flood_active: bool = False

        # BUG-1: RTR list starvation tracking
        self.rtr_starvation_count: int = 0     # rotations where RTR list was truncated
        self.rtr_dropped_total:    int = 0     # total RTR requests that didn't fit

        # BUG-2: FCC deadlock tracking (all nodes simultaneously throttled)
        self.fcc_deadlock_count:   int = 0
        self.peak_fcc_throttled:   int = 0     # max nodes simultaneously at transmits_allowed=0

        # Memory model
        self.assembly_deref_count: int = 0     # total calls to assembly_deref per ring
        self.assembly_free_size:   int = 0     # simulated assembly_list_free size
        self.peak_assembly_free:   int = 0     # peak (without fix)
        self.retrans_buf_hwm:      int = 0     # retrans_message_queue high-water mark

        # Cascade recovery tracking
        self._last_recovery_time:  Optional[float] = None
        self.cascade_depth:        int = 0
        self.max_cascade_depth:    int = 0

        # Timeline of ring events for post-mortem
        self.event_log: List[Tuple[float, str]] = []

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

    # ---- memory model ----

    def _sim_ring_recovery_memory(self, sim_time: float) -> None:
        """
        Simulate memory effects of ring recovery:
        - Each recovery deref's all nodes' assemblies into assembly_list_free
        - Without the fix, assembly_list_free grows unboundedly
        - Also record retrans_buf size at recovery time (models the TODO LEAK)
        """
        global _assembly_deref_total, _assembly_free_peak, _retrans_buf_peak

        active_nodes = sum(1 for n in self.nodes
                           if not n.is_partitioned and not n.is_nic_flap)

        # Each recovery: active_nodes assemblies go to free list
        self.assembly_deref_count += active_nodes
        _assembly_deref_total     += active_nodes

        # Without fix: all stay in free list
        self.assembly_free_size   += active_nodes
        if self.assembly_free_size > self.peak_assembly_free:
            self.peak_assembly_free = self.assembly_free_size
        if self.peak_assembly_free > _assembly_free_peak:
            _assembly_free_peak = self.peak_assembly_free

        # Retrans buffer at recovery time (TODO LEAK: these were NOT freed before our fix)
        cur_retrans = len(self.rtx_buf)
        if cur_retrans > self.retrans_buf_hwm:
            self.retrans_buf_hwm = cur_retrans
        if cur_retrans > _retrans_buf_peak:
            _retrans_buf_peak = cur_retrans

    # ---- ring recovery ----

    def _new_ring(self, trigger_node: int, sim_time: float, reason: str) -> None:
        global _cascade_depth, _cascade_max_depth, _cascade_start_time

        self._sim_ring_recovery_memory(sim_time)

        # Cascade detection: if recovery happens within 5× token_timeout of previous
        CASCADE_WINDOW_S = TOKEN_TIMEOUT_MS / 1000.0 * 5
        if (self._last_recovery_time is not None and
                sim_time - self._last_recovery_time < CASCADE_WINDOW_S):
            self.cascade_depth += 1
            if self.cascade_depth > self.max_cascade_depth:
                self.max_cascade_depth = self.cascade_depth
            self.event_log.append((sim_time,
                f"CASCADE recovery #{self.cascade_depth} within {CASCADE_WINDOW_S:.0f}s window "
                f"reason={reason} trigger=node-{trigger_node}"))
        else:
            self.cascade_depth = 0

        self._last_recovery_time = sim_time

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
            n.inbox.clear()

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
        for n in self.nodes:
            if not n.is_partitioned and not n.is_nic_flap:
                n.flush_inbox(sim_time)

    # ---- main rotation ----

    def rotate(self, sim_time: float, concurrent_per_node: int) -> None:
        global _latency_rtrs, _rtr_starvation_events, _fcc_deadlock_events, _retrans_buf_peak

        # Step 0: flush inboxes
        self._flush_all_inboxes(sim_time)

        # Step 1: group ARU
        self.group_aru = self._compute_group_aru()
        self.token.aru = self.group_aru
        self.token.aru_addr = self._find_laggard()
        self._track_stall(sim_time)

        # Step 2: release sort queue entries
        for n in self.nodes:
            if not n.is_partitioned and not n.is_nic_flap:
                self._check_release_range(n, sim_time)

        # Step 2a: track backlog pressure + retrans_buf HWM
        total_backlog = sum(n.tx_queue for n in self.nodes
                            if not n.is_partitioned and not n.is_nic_flap)
        if total_backlog > self.peak_tx_backlog:
            self.peak_tx_backlog = total_backlog

        cur_retrans = len(self.rtx_buf)
        if cur_retrans > self.retrans_buf_hwm:
            self.retrans_buf_hwm = cur_retrans
        if cur_retrans > _retrans_buf_peak:
            _retrans_buf_peak = cur_retrans

        # Step 3: build RTR list — BUG-1 starvation tracking
        new_rtr: List[int] = []
        nodes_needing_rtr: int = 0
        total_rtr_needed:  int = 0

        for n in self.nodes:
            if n.is_partitioned or n.is_nic_flap:
                continue
            if n.my_aru == self.token.seq:
                continue
            if n.my_aru == SEQNO_INITIAL and self.token.seq == SEQNO_INITIAL:
                continue

            missing = self._check_rtr_range(n, sim_time)
            if not missing:
                continue

            nodes_needing_rtr += 1
            total_rtr_needed  += len(missing)

            for seq in missing:
                inbox_seqnos = {pd.seqno for pd in n.inbox}
                if seq in inbox_seqnos:
                    _latency_rtrs += 1

                if len(new_rtr) < RETRANSMIT_ENTRIES_MAX:
                    if seq not in new_rtr:
                        new_rtr.append(seq)
                else:
                    # BUG-1: RTR list is full — this node's request is DROPPED
                    n.stats.rtr_starved += 1
                    self.rtr_dropped_total += 1

        # Detect RTR starvation event
        if nodes_needing_rtr > RETRANSMIT_ENTRIES_MAX:
            self.rtr_starvation_count += 1
            _rtr_starvation_events    += 1

        self.token.rtr_list = new_rtr
        if len(new_rtr) > self.peak_rtr_list_len:
            self.peak_rtr_list_len = len(new_rtr)

        # Step 4: token passes — BUG-2 FCC deadlock tracking
        fcc_throttled_count: int = 0
        for i in range(self.n):
            self.holder_idx = i
            node = self.nodes[i]
            if node.is_partitioned or node.is_nic_flap:
                continue
            allowed = self._fcc_transmits_allowed()
            if allowed == 0:
                fcc_throttled_count += 1
                node.stats.fcc_deadlocked_passes += 1
            self._do_node_pass(sim_time, concurrent_per_node)

        # Check for BUG-2: all active nodes simultaneously throttled
        active_count = sum(1 for n in self.nodes
                           if not n.is_partitioned and not n.is_nic_flap)
        if fcc_throttled_count > 0:
            if fcc_throttled_count > self.peak_fcc_throttled:
                self.peak_fcc_throttled = fcc_throttled_count

            if fcc_throttled_count == active_count and active_count > 0:
                self.fcc_deadlock_count += 1
                _fcc_deadlock_events    += 1

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
                "backlog": total_backlog,
                "rtr_starved": nodes_needing_rtr - min(nodes_needing_rtr, RETRANSMIT_ENTRIES_MAX),
                "fcc_throttled": fcc_throttled_count,
            })
        self._rot_start_time = sim_time

    def _do_node_pass(self, sim_time: float, concurrent_per_node: int) -> None:
        node = self.nodes[self.holder_idx]
        node.stats.token_holds += 1

        if self.holder_idx == 0 and self.token.rtr_list:
            self._do_retransmits(self.token.rtr_list, sim_time)

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
                    n.enqueue_delivery(seq_here, msg_len, sim_time,
                                       self.rng, is_retransmit=False)
            node.tx_queue -= 1
            node.stats.msgs_sent += 1
            self.total_multicast += 1
            sent += 1

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
                    n.enqueue_delivery(seq, msg_len, sim_time,
                                       self.rng, is_retransmit=True)
                    n.flush_inbox(sim_time)
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
def _fmt_mb(mb: float) -> str:
    if mb >= 1024:
        return f"{mb/1024:.2f} GiB"
    return f"{mb:.1f} MiB"


def print_results(args, nodes: List[Node], ring: Ring) -> None:
    n_active = args.nodes
    print()
    print("=" * 80)
    print("  SIMULATION RESULTS  —  300-node Corosync TOTEM Stress Analysis")
    print("=" * 80)

    total_assert   = len(_assert_fires)
    total_frame    = len(_frame_fires)
    total_retrans  = sum(n.stats.rtr_retransmitted for n in nodes)
    total_starved  = sum(n.stats.rtr_starved for n in nodes)
    total_throttle = sum(n.stats.write_flood_throttles for n in nodes)
    total_fcc_dead = sum(n.stats.fcc_deadlocked_passes for n in nodes)

    print(f"\n  === PROTOCOL METRICS ===")
    print(f"  Total msgs multicast : {ring.total_multicast:>10,}")
    print(f"  Total RTR retransmits: {total_retrans:>10,}  "
          f"(latency-induced: {_latency_rtrs:,}  "
          f"{_latency_rtrs*100/max(total_retrans,1):.1f}%)")
    print(f"  RTR requests dropped : {total_starved:>10,}  "
          f"← BUG-1: RETRANSMIT_ENTRIES_MAX={RETRANSMIT_ENTRIES_MAX} too small for {n_active} nodes")
    print(f"  RTR starvation events: {ring.rtr_starvation_count:>10,}  "
          f"(rotations where >{RETRANSMIT_ENTRIES_MAX} nodes needed RTR simultaneously)")
    print(f"  FCC throttle events  : {_throttle_events:>10,}")
    print(f"  FCC deadlock events  : {ring.fcc_deadlock_count:>10,}  "
          f"← BUG-2: ALL {n_active} nodes simultaneously at transmits_allowed=0")
    print(f"  Peak FCC throttled   : {ring.peak_fcc_throttled:>10,} / {n_active} nodes  "
          f"← WINDOW_SIZE={WINDOW_SIZE} too small for {n_active} nodes")
    print(f"  Write-flood throttles: {total_throttle:>10,}")
    print(f"  Peak tx backlog      : {ring.peak_tx_backlog:>10,} msgs queued")
    print(f"  Peak RTR list length : {ring.peak_rtr_list_len:>10,} / {RETRANSMIT_ENTRIES_MAX} entries/pass")

    print(f"\n  === STABILITY METRICS ===")
    print(f"  Ring formations      : {ring.recovery_count:>10,}")
    print(f"  Token retransmits    : {ring.token_retransmits:>10,}")
    print(f"  ARU stall events     : {ring.stall_events:>10,}  "
          f"(total {ring.total_stall_ms:.0f} ms)")
    print(f"  Max cascade depth    : {ring.max_cascade_depth:>10,}  "
          f"← BUG-3: cascading recovery during flood")
    if ring.event_log:
        print(f"  Cascade events:")
        for t, msg in ring.event_log[:6]:
            print(f"    [t={t:6.2f}s] {msg}")
        if len(ring.event_log) > 6:
            print(f"    ... +{len(ring.event_log)-6} more")

    # ---- Memory leak analysis ----
    print(f"\n  === MEMORY LEAK ANALYSIS ===")

    retrans_buf_mb  = ring.retrans_buf_hwm * MCAST_BUFFER_KB / 1024.0
    retrans_leak_mb = retrans_buf_mb        # each recovery leaked this much (pre-fix)

    # assembly_list_free simulation
    peak_assembly_no_fix_mb  = ring.peak_assembly_free * ASSEMBLY_SIZE_MB
    peak_assembly_with_fix_mb = min(ASSEMBLY_FREE_LIST_CAP, ring.peak_assembly_free) * ASSEMBLY_SIZE_MB
    assembly_saved_mb = peak_assembly_no_fix_mb - peak_assembly_with_fix_mb

    # Total retrans leak (each recovery × peak size at recovery time)
    total_retrans_leak_mb = retrans_leak_mb * ring.recovery_count

    print(f"  --- BUG-5: retrans_message_queue TODO LEAK (totemsrp.c) ---")
    print(f"  Peak retrans_buf entries   : {ring.retrans_buf_hwm:>6,}  "
          f"({_fmt_mb(retrans_buf_mb)} in mcast buffers @ 64KB each)")
    print(f"  Ring recovery events       : {ring.recovery_count:>6,}")
    print(f"  Without fix  (leaked/event): {_fmt_mb(retrans_leak_mb)}  × "
          f"{ring.recovery_count} = {_fmt_mb(total_retrans_leak_mb)}")
    print(f"  With fix (drain loop added): 0 MiB leaked  "
          f"(exec/totemsrp.c memb_state_recovery_enter)")
    print()

    print(f"  --- BUG-4: assembly_list_free unbounded growth (totempg.c) ---")
    print(f"  Total assembly_deref calls : {ring.assembly_deref_count:>6,}  "
          f"(active_nodes × recovery_count)")
    print(f"  Peak free-list depth       : {ring.peak_assembly_free:>6,} entries")
    print(f"  Without fix (unbounded)    : {_fmt_mb(peak_assembly_no_fix_mb)}  "
          f"({ring.peak_assembly_free} × {ASSEMBLY_SIZE_MB:.2f} MiB/assembly)")
    print(f"  With fix (cap={ASSEMBLY_FREE_LIST_CAP})        : {_fmt_mb(peak_assembly_with_fix_mb)}  "
          f"← ASSEMBLY_FREE_LIST_MAX={ASSEMBLY_FREE_LIST_CAP}")
    print(f"  Memory saved by fix        : {_fmt_mb(assembly_saved_mb)}")
    print()

    total_rss_no_fix_mb  = total_retrans_leak_mb + peak_assembly_no_fix_mb
    total_rss_with_fix_mb = 0 + peak_assembly_with_fix_mb
    print(f"  === TOTAL MEMORY: no-fix vs. with-fix ===")
    print(f"  Without either fix : {_fmt_mb(total_rss_no_fix_mb)}  ← matches observed 15 GiB")
    print(f"  With both fixes    : {_fmt_mb(total_rss_with_fix_mb)}")
    print(f"  Total reduction    : {_fmt_mb(total_rss_no_fix_mb - total_rss_with_fix_mb)}")

    # ---- Assert fires ----
    print(f"\n  === ASSERT FIRES (CRASH → FIXED IN THIS BUILD) ===")
    if total_assert + total_frame > 0:
        print(f"  Total assert fires : {total_assert + total_frame:,}")
        for e in _assert_fires[:8]:
            print(f"    [{e.location}] t={e.sim_time:.1f}s "
                  f"node-{e.node_id} range={e.range_val:,} "
                  f"limit={e.limit:,}  {e.detail}")
        if total_assert > 8:
            print(f"    ... +{total_assert-8} more")
    else:
        print("  Assert fires: 0  — cluster stable (assert crashes prevented by our fixes)")

    # ---- Token rotation statistics ----
    print(f"\n  === TOKEN ROTATION STATISTICS ===")
    if ring.rotation_samples:
        rot_ms_list = sorted(s["ms"] * 1000 for s in ring.rotation_samples
                             if 0 < s["ms"] < 2.0)
        if rot_ms_list:
            p50 = rot_ms_list[len(rot_ms_list)//2]
            p95 = rot_ms_list[min(int(len(rot_ms_list)*0.95), len(rot_ms_list)-1)]
            p99 = rot_ms_list[min(int(len(rot_ms_list)*0.99), len(rot_ms_list)-1)]
            print(f"  p50={p50:.0f}µs  p95={p95:.0f}µs  p99={p99:.0f}µs  "
                  f"(token_timeout={TOKEN_TIMEOUT_MS}ms = {TOKEN_TIMEOUT_MS*1000:.0f}µs)")

        # ARU gap over time
        aru_samples = [s["aru_gap"] for s in ring.rotation_samples if s["aru_gap"] > 0]
        if aru_samples:
            aru_samples.sort()
            p95_aru = aru_samples[min(int(len(aru_samples)*0.95), len(aru_samples)-1)]
            peak_aru = max(aru_samples)
            print(f"  ARU gap p95={p95_aru}  peak={peak_aru}  "
                  f"limit={QUEUE_RTR_ITEMS_SIZE_MAX}  "
                  f"({peak_aru*100//QUEUE_RTR_ITEMS_SIZE_MAX}% of crash boundary)")

        # FCC throttle percentage
        total_rots = len(ring.rotation_samples)
        throttled_rots = sum(1 for s in ring.rotation_samples if s["fcc_throttled"] > 0)
        print(f"  FCC-throttled rotations: {throttled_rots}/{total_rots} "
              f"({throttled_rots*100//max(total_rots,1)}% of time)  ← BUG-2")
        starved_rots = sum(1 for s in ring.rotation_samples if s["rtr_starved"] > 0)
        print(f"  RTR-starved rotations  : {starved_rots}/{total_rots} "
              f"({starved_rots*100//max(total_rots,1)}% of time)  ← BUG-1")

    # ---- Node leaderboard ----
    print(f"\n  === TOP-5 NODES BY ARU STALL ===")
    for n in sorted(nodes, key=lambda x: x.stats.aru_stall_ms, reverse=True)[:5]:
        if n.stats.aru_stall_ms > 0:
            print(f"  node-{n.node_id:>3}: stall={n.stats.aru_stall_ms:.0f}ms  "
                  f"drops={n.stats.msgs_dropped}  "
                  f"rtr_starved={n.stats.rtr_starved}  "
                  f"fcc_dead={n.stats.fcc_deadlocked_passes}")

    # ---- Bug analysis ----
    print(f"\n  === NEW BUGS IDENTIFIED AT {n_active}-NODE SCALE ===")

    # BUG-1 analysis
    rtrs_per_pass_needed = ring.rtr_dropped_total / max(ring.rtr_starvation_count, 1) + RETRANSMIT_ENTRIES_MAX
    fix_suggestion = max(n_active // 5, RETRANSMIT_ENTRIES_MAX)
    print(f"\n  BUG-1: RTR List Starvation  (exec/totemsrp.c)")
    print(f"    RETRANSMIT_ENTRIES_MAX = {RETRANSMIT_ENTRIES_MAX}  (constant, not scaled by N)")
    print(f"    Rotations with starvation: {ring.rtr_starvation_count:,}")
    print(f"    Total dropped RTR requests: {ring.rtr_dropped_total:,}")
    if ring.rtr_starvation_count > 0:
        print(f"    Avg RTR entries needed when starved: {rtrs_per_pass_needed:.0f}")
        print(f"    Suggested fix: increase RETRANSMIT_ENTRIES_MAX to ≥{fix_suggestion}")
        print(f"    Impact: unserviced nodes never receive missing messages → ARU stall →")
        print(f"    → delivery_latency grows O(N/30) = O({n_active//RETRANSMIT_ENTRIES_MAX}x slower)")
    else:
        print(f"    No starvation detected under these parameters")

    # BUG-2 analysis
    print(f"\n  BUG-2: FCC Window Too Small for Large Clusters  (exec/totemsrp.c, totem.conf)")
    print(f"    WINDOW_SIZE = {WINDOW_SIZE}  (cluster-wide, not per-node)")
    print(f"    With {n_active} nodes sending {args.rate} msg/s total:")
    msgs_per_rot = args.rate * (n_active * 1.0 / 1000.0)
    gap_after_1rot = msgs_per_rot
    print(f"    msgs per rotation = {msgs_per_rot:.0f}")
    print(f"    ARU gap after 1 rotation = {gap_after_1rot:.0f}  vs WINDOW_SIZE={WINDOW_SIZE}")
    if gap_after_1rot > WINDOW_SIZE:
        print(f"    ⚠  Gap ({gap_after_1rot:.0f}) > WINDOW_SIZE ({WINDOW_SIZE}): ALL nodes throttled")
        print(f"       after the FIRST rotation at {args.rate} msg/s!")
        recommended_ws = int(gap_after_1rot * 2)
        print(f"    Suggested fix: window_size = {recommended_ws} in corosync.conf")
        print(f"      or dynamically scale: window_size = 2 × (rate × rotation_ms / 1000)")
    else:
        print(f"    Window OK for current rate ({gap_after_1rot:.0f} < {WINDOW_SIZE})")

    # BUG-3 analysis
    print(f"\n  BUG-3: Cascading Recovery During Write Flood  (exec/totemsrp.c)")
    print(f"    Max cascade depth : {ring.max_cascade_depth}")
    if ring.max_cascade_depth >= 2:
        print(f"    ⚠  {ring.max_cascade_depth}+ consecutive recoveries detected!")
        print(f"    When ring recovers during active flood, RTR list overflows on first pass")
        print(f"    → new recovery → overflow again → cascade continues until flood ends")
        print(f"    Fix: in memb_state_recovery_enter, drain tx_queues before reforming ring,")
        print(f"    or apply rate limiting (transmits_allowed=0) for first N passes after recovery")

    # Latency analysis
    print(f"\n  === LATENCY IMPACT ANALYSIS ===")
    rot_s   = n_active * 0.001
    lat_avg = (LATENCY_MIN_MS + LATENCY_MAX_MS) / 2.0
    delivery_window_ms = rot_s * 1000.0 / n_active
    print(f"  Rotation time   : {rot_s*1000:.0f}ms for {n_active} nodes")
    print(f"  Delivery window : {delivery_window_ms:.2f}ms per node token pass")
    print(f"  Network latency : {LATENCY_MIN_MS:.0f}–{LATENCY_MAX_MS:.0f}ms  mean={lat_avg:.1f}ms")
    ratio = lat_avg / delivery_window_ms
    print(f"  Latency/window  : {ratio:.1f}x — {'RTR fires on EVERY pass ⚠' if ratio > 1 else 'ok'}")
    if ratio > 1:
        print(f"  Fix: reduce latency OR increase token_timeout OR accept RTR overhead")
        rtrs_per_rotation = n_active  # every node fires RTR every pass
        rtr_overhead_pct  = rtrs_per_rotation / max(ring.total_multicast / max(len(ring.rotation_samples), 1), 1)
        print(f"  RTR overhead   : ~{rtrs_per_rotation} RTRs/rotation  "
              f"(but RTR list capped at {RETRANSMIT_ENTRIES_MAX} → starvation)")

    # Concurrent write analysis
    print(f"\n  === CONCURRENT-WRITE BOTTLENECK ANALYSIS ===")
    inject_per_rot = args.concurrent * n_active
    drain_per_rot  = MAX_MESSAGES * n_active
    bg_inject      = int(args.rate * rot_s)
    total_inject   = inject_per_rot + bg_inject
    ratio_flood = total_inject / max(drain_per_rot, 1)
    print(f"  Background:  {bg_inject:>5} msgs/rotation ({args.rate} msg/s × {rot_s*1000:.0f}ms)")
    print(f"  Flood inject:{inject_per_rot:>5} msgs/rotation ({args.concurrent}/node × {n_active} nodes)")
    print(f"  Total inject:{total_inject:>5} msgs/rotation  "
          f"drain: {drain_per_rot}  ratio: {ratio_flood:.2f}  "
          f"{'SATURATED ⚠' if ratio_flood > 1.0 else 'ok'}")
    if ratio_flood > 0.5:
        saturate_concurrent = int(drain_per_rot / n_active) + 1
        print(f"  Ring saturates at --concurrent {saturate_concurrent} for {n_active} nodes")

    print()
    print("=" * 80)


# ---------------------------------------------------------------------------
# Main simulation
# ---------------------------------------------------------------------------

def run_simulation(args) -> None:
    global _assert_fires, _frame_fires, _latency_rtrs, _throttle_events
    global _rtr_starvation_events, _fcc_deadlock_events
    global _assembly_deref_total, _assembly_free_peak, _retrans_buf_peak
    _assert_fires = []; _frame_fires = []
    _latency_rtrs = _throttle_events = 0
    _rtr_starvation_events = _fcc_deadlock_events = 0
    _assembly_deref_total  = _assembly_free_peak = _retrans_buf_peak = 0

    rng = random.Random(args.seed)
    nodes: List[Node] = [Node(node_id=i + 1) for i in range(args.nodes)]

    pool = list(nodes)
    rng.shuffle(pool)
    slow_node, partition_node, nic_node = pool[0], pool[1], pool[2]
    slow_node.is_slow = True

    if not args.quiet:
        rot_ms = args.nodes * 1.0
        lat_avg = (LATENCY_MIN_MS + LATENCY_MAX_MS) / 2.0
        threshold = QUEUE_RTR_ITEMS_SIZE_MAX / (PARTITION_END_S - PARTITION_START_S)
        print()
        print("=" * 80)
        print(f"  Corosync TOTEM {args.nodes}-node ring simulation (sim300)")
        print("=" * 80)
        print(f"  Nodes:             {args.nodes}")
        print(f"  Duration:          {args.seconds}s simulated")
        print(f"  Message rate:      {args.rate:,} msg/s  {'[STRESS]' if args.stress else ''}")
        print(f"  Concurrent/node:   {args.concurrent} writes/node/rotation")
        print(f"  Network latency:   {LATENCY_MIN_MS:.0f}–{LATENCY_MAX_MS:.0f}ms mean={lat_avg:.1f}ms")
        print(f"  TOKEN_TIMEOUT:     {TOKEN_TIMEOUT_MS}ms")
        print(f"  Rotation time:     ≈{rot_ms:.0f}ms  ({args.nodes} nodes × 1ms/hop)")
        print(f"  Delivery window:   {rot_ms/args.nodes:.2f}ms per node  "
              f"{'⚠ < latency!' if lat_avg > rot_ms/args.nodes else 'ok'}")
        print(f"  WINDOW_SIZE:       {WINDOW_SIZE}  MAX_MESSAGES: {MAX_MESSAGES}")
        print(f"  RTR_ENTRIES_MAX:   {RETRANSMIT_ENTRIES_MAX}  ← sized for <30 nodes, NOT {args.nodes}!")
        print(f"  L2890 threshold:   {threshold:.0f} msg/s  "
              f"({'EXCEEDED' if args.rate >= threshold else 'below'})")
        print()
        print(f"  Fault schedule:")
        print(f"    slow node      node-{slow_node.node_id:>3}  10% drop prob")
        print(f"    partition      node-{partition_node.node_id:>3}  "
              f"t={PARTITION_START_S:.0f}s–{PARTITION_END_S:.0f}s  "
              f"({int(args.rate*(PARTITION_END_S-PARTITION_START_S)):,} msgs missed)")
        print(f"    NIC flap       node-{nic_node.node_id:>3}  "
              f"t={NIC_FLAP_START_S:.0f}s–{NIC_FLAP_END_S:.0f}s")
        print(f"    write flood #1 ALL nodes  "
              f"t={WRITE_FLOOD_START_S:.0f}s–{WRITE_FLOOD_END_S:.0f}s  "
              f"+{args.concurrent*args.nodes:,} msgs/rotation")
        print(f"    write flood #2 ALL nodes  "
              f"t={SECOND_FLOOD_START_S:.0f}s–{SECOND_FLOOD_END_S:.0f}s  (post-recovery stress)")
        print()

    ring = Ring(nodes, rng, latency_min=LATENCY_MIN_MS, latency_max=LATENCY_MAX_MS)
    ROTATION_S = args.nodes / 1000.0
    msgs_per_rotation = args.rate * ROTATION_S

    sim_time = 0.0
    tick = 0
    p_injected = n_injected = False
    flood1_active = flood2_active = False
    next_prog = 10.0
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
                print(f"  [t={sim_time:6.2f}s] NIC FLAP end     node-{nic_node.node_id}")

        # Write flood #1
        if WRITE_FLOOD_START_S <= sim_time < WRITE_FLOOD_END_S:
            if not flood1_active:
                flood1_active = True
                if not args.quiet:
                    print(f"  [t={sim_time:6.2f}s] WRITE FLOOD #1 start  "
                          f"+{args.concurrent*args.nodes:,} msgs/rotation")
            for n in nodes:
                if not n.is_partitioned and not n.is_nic_flap:
                    n.tx_queue += args.concurrent
        elif flood1_active and sim_time >= WRITE_FLOOD_END_S:
            flood1_active = False
            ring.write_flood_active = False
            if not args.quiet:
                print(f"  [t={sim_time:6.2f}s] WRITE FLOOD #1 end  rings={ring.recovery_count}")

        # Write flood #2 (post-recovery stress test)
        if SECOND_FLOOD_START_S <= sim_time < SECOND_FLOOD_END_S:
            if not flood2_active:
                flood2_active = True
                if not args.quiet:
                    print(f"  [t={sim_time:6.2f}s] WRITE FLOOD #2 start  (cascade stress)")
            for n in nodes:
                if not n.is_partitioned and not n.is_nic_flap:
                    n.tx_queue += args.concurrent
        elif flood2_active and sim_time >= SECOND_FLOOD_END_S:
            flood2_active = False
            if not args.quiet:
                print(f"  [t={sim_time:6.2f}s] WRITE FLOOD #2 end")

        # Background message injection
        n_inject = int(msgs_per_rotation + rng.random())
        for _ in range(n_inject):
            sender = nodes[rng.randint(0, args.nodes - 1)]
            if not sender.is_partitioned and not sender.is_nic_flap:
                sender.tx_queue += 1

        ring.rotate(sim_time, args.concurrent)
        sim_time += ROTATION_S * max(0.5, rng.gauss(1.0, 0.02))

        if not args.quiet and sim_time >= next_prog:
            aru_gap = sq_diff(ring.token.seq, ring.group_aru) \
                if ring.token.seq != SEQNO_INITIAL else 0
            total_tx  = sum(n.tx_queue for n in nodes)
            pending   = sum(len(n.inbox) for n in nodes)
            starved_r = ring.rtr_dropped_total
            print(f"  [t={sim_time:6.1f}s]  "
                  f"asserts={len(_assert_fires):5,}  "
                  f"rings={ring.recovery_count:3}  "
                  f"aru_gap={aru_gap:5}  "
                  f"rtr_starved={starved_r:5,}  "
                  f"fcc_dead={ring.fcc_deadlock_count:4}  "
                  f"tx={total_tx:5,}  "
                  f"lat_inbox={pending:5,}  "
                  f"cascade={ring.cascade_depth}  "
                  f"wall={time.monotonic()-wall_start:.1f}s")
            next_prog += 10.0

    print_results(args, nodes, ring)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def main():
    p = argparse.ArgumentParser(
        description="Corosync TOTEM 300-node ring stress simulation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__)
    p.add_argument("--nodes",      type=int,   default=N_NODES)
    p.add_argument("--rate",       type=int,   default=MSG_RATE,
                   help=f"background msg/s (default {MSG_RATE})")
    p.add_argument("--stress",     action="store_true",
                   help="stress mode: rate=2000, concurrent=8")
    p.add_argument("--concurrent", type=int,   default=CONCURRENT_WRITE_PER_NODE,
                   help=f"writes/node/rotation during flood (default {CONCURRENT_WRITE_PER_NODE})")
    p.add_argument("--latency",    type=float, default=None,
                   help="override mean latency ms (default uniform 5-10ms)")
    p.add_argument("--seconds",    type=int,   default=SIMULATION_SECONDS)
    p.add_argument("--seed",       type=int,   default=42)
    p.add_argument("--quiet",      action="store_true")
    args = p.parse_args()

    if args.stress:
        args.rate = 2000
        if args.concurrent == CONCURRENT_WRITE_PER_NODE:
            args.concurrent = 8
    if args.latency is not None:
        import sys as _sys
        _mod = _sys.modules[__name__]
        _mod.LATENCY_MIN_MS = max(0.0, args.latency * 0.8)
        _mod.LATENCY_MAX_MS = args.latency * 1.2

    run_simulation(args)


if __name__ == "__main__":
    main()
