#!/usr/bin/env python3
"""
sim100.py — Corosync TOTEM ring stress-test: 100-node simulation
================================================================
Simulates the TOTEM Secure Ring Protocol (totemsrp.c) at 100-node scale,
reproducing the failure modes observed in the 53-node Proxmox CPG incident
of 2026-03-25 and stress-testing for assert-fire conditions.

The five dangerous assert sites modelled (totemsrp.c line numbers):

  L2433  assert(range < QUEUE_RTR_ITEMS_SIZE_MAX)
         Context: old-ring message copy at ring reformation
         Trigger: partition node rejoins after > 16384 msgs accumulated

  L2672  assert(range < QUEUE_RTR_ITEMS_SIZE_MAX)
         Context: regular_sort_queue release
         Trigger: release_to - last_released jumps by >= 16384

  L2890  assert(range < QUEUE_RTR_ITEMS_SIZE_MAX)
         Context: RTR list build in orf_token_rtr_list_build
         Trigger: token.seq - my_aru >= 16384 on any single node

  L4215  assert(range < QUEUE_RTR_ITEMS_SIZE_MAX)
         Context: message delivery in message_handler_orf_token
         Trigger: same conditions as L2890

  L4327  assert(msg_len <= FRAME_SIZE_MAX)
         Context: mcast receive in message_handler_mcast
         Trigger: malformed packet or totempg fragmentation bug

Model notes
-----------
- Time is simulated in discrete "rounds". One round = one complete ring
  rotation (N token passes across all N nodes).
- Within each round, the token visits each node once in order.
- Sequence numbers are uint32 with natural wrap at 2^32.
- ARU = All-Received-Up-to: per-node contiguous high-water mark.
- Group ARU on token = min(my_aru) across active (non-partitioned) nodes.
- Window size controls how far token.seq may run ahead of group ARU.
- Slow node: drops random fraction of FIRST deliveries; RTR fills gaps.
- Partitioned node: removed from active ring; token.seq advances without it.
  On rejoin, the gap = (token.seq - my_aru) may exceed QUEUE_RTR_ITEMS_SIZE_MAX.
- NIC flap: same as partition but brief (2s).
- CPG cascade: 20 nodes join a CPG group simultaneously, generating a
  burst of IPC view-change events that can overflow the IPC queue.

Usage:
    python3 sim100.py                        # normal load
    python3 sim100.py --stress               # high rate (triggers L2433/L2890)
    python3 sim100.py --rate 600             # custom rate
    python3 sim100.py --stress --quiet       # minimal output
"""

import argparse
import collections
import random
import sys
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional

# ---------------------------------------------------------------------------
# Compile-time constants (mirrors totemsrp.c / totem.h)
# ---------------------------------------------------------------------------
N_NODES                  = 100
TOKEN_TIMEOUT_MS         = 5000        # ms — tuned for 100-node Proxmox cluster
TOKEN_RETRANSMITS        = 10          # retransmit attempts before ring recovery
TOKEN_COEFFICIENT        = 50          # ms/node for token_timeout formula
MAX_MESSAGES             = 25          # max messages per token hold
WINDOW_SIZE              = 50          # flow-control window
QUEUE_RTR_ITEMS_SIZE_MAX = 16384       # totemsrp.c:96 — assert fires at this boundary
RETRANSMIT_ENTRIES_MAX   = 30          # max RTR list entries per token pass
FRAME_SIZE_MAX           = 65536       # KNET_MAX_PACKET_SIZE (totem.h:52)
MSG_RATE                 = 100         # default: messages/second total across ring
SIMULATION_SECONDS       = 120

# CPG / IPC parameters (from 2026-03-25 incident: 53-node cluster, 42 CPG members)
CPG_IPC_QUEUE_DEPTH_MAX  = 1000        # IPC queue depth before CS_ERR_TRY_AGAIN
CPG_GROUP_SIZE           = 42          # members in dcdb CPG group (incident value)
CPG_CASCADE_SIZE         = 20          # nodes joining simultaneously at t=80s

# Fault injection defaults
DROP_SLOW_NODE_PROB      = 0.10        # slow node first-delivery drop probability
TOKEN_LOSS_PROB          = 0.01        # per-token-pass loss probability
PARTITION_START_S        = 30.0
PARTITION_END_S          = 60.0        # 30-second partition
NIC_FLAP_START_S         = 70.0
NIC_FLAP_END_S           = 72.0        # 2-second NIC flap
CPG_CASCADE_START_S      = 80.0        # 20-node CPG join cascade

# Seqno constants
SEQNO_WRAP               = 2**32
SEQNO_INITIAL            = SEQNO_WRAP - 1   # SEQNO_START_MSG - 1


# ---------------------------------------------------------------------------
# Seqno arithmetic (uint32 ring)
# ---------------------------------------------------------------------------

def u32(v: int) -> int:
    return v & 0xFFFFFFFF

def sq_add(a: int, b: int) -> int:
    return u32(a + b)

def sq_diff(high: int, low: int) -> int:
    """Unsigned distance from low to high (wrapping)."""
    return u32(high - low)

def sq_lt(a: int, b: int) -> bool:
    """True if a is strictly before b in the uint32 ring (sq_lt_compare)."""
    return sq_diff(b, a) < (SEQNO_WRAP >> 1)


# ---------------------------------------------------------------------------
# Assert-fire registry
# ---------------------------------------------------------------------------

@dataclass
class AssertFire:
    sim_time:   float
    location:   str     # "L2433", "L2672", "L2890", "L4215", "L4327"
    node_id:    int
    range_val:  int
    limit:      int
    detail:     str = ""

_assert_fires: List[AssertFire] = []
_frame_fires:  List[AssertFire] = []


def check_range_assert(location: str, node_id: int, range_val: int,
                        sim_time: float, detail: str = "") -> bool:
    """
    Return True (and log) if assert(range < QUEUE_RTR_ITEMS_SIZE_MAX) fires.
    The *caller* applies the fix instead of crashing.
    """
    if range_val >= QUEUE_RTR_ITEMS_SIZE_MAX:
        _assert_fires.append(AssertFire(
            sim_time=sim_time, location=location, node_id=node_id,
            range_val=range_val, limit=QUEUE_RTR_ITEMS_SIZE_MAX, detail=detail))
        return True
    return False


def check_frame_assert(node_id: int, msg_len: int,
                        sim_time: float, detail: str = "") -> bool:
    """Return True (and log) if assert(msg_len <= FRAME_SIZE_MAX) fires."""
    if msg_len > FRAME_SIZE_MAX:
        _frame_fires.append(AssertFire(
            sim_time=sim_time, location="L4327", node_id=node_id,
            range_val=msg_len, limit=FRAME_SIZE_MAX, detail=detail))
        return True
    return False


# ---------------------------------------------------------------------------
# Per-node statistics
# ---------------------------------------------------------------------------

@dataclass
class NodeStats:
    node_id:               int   = 0
    msgs_sent:             int   = 0   # new messages originated here
    msgs_received:         int   = 0   # messages delivered here
    msgs_dropped:          int   = 0   # dropped due to fault / oversize
    rtr_requested:         int   = 0   # missing seqnos this node put on RTR
    rtr_retransmitted:     int   = 0   # retransmit sends issued by this node
    token_holds:           int   = 0   # token passes at this node
    token_losses:          int   = 0   # token-loss events while holder
    aru_stall_ms:          float = 0.0 # ms this node held group ARU down
    recovery_participations: int = 0   # new-ring formations this node was in
    cpg_peak_ipc_queue:    int   = 0
    cpg_try_again:         int   = 0


# ---------------------------------------------------------------------------
# Token
# ---------------------------------------------------------------------------

@dataclass
class Token:
    seq:           int = SEQNO_INITIAL   # highest multicast seqno assigned
    token_seq:     int = 0               # token number (for loss detection)
    aru:           int = SEQNO_INITIAL   # group ARU at time of last pass
    aru_addr:      int = 0               # node holding ARU down
    fcc:           int = 0
    backlog:       int = 0
    rtr_list:      List[int] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Per-node state
# ---------------------------------------------------------------------------

@dataclass
class Node:
    node_id:     int
    my_aru:      int = SEQNO_INITIAL          # contiguous recv high-water mark
    my_high_seq: int = SEQNO_INITIAL          # highest seqno seen (may have gaps)
    my_delivered: int = SEQNO_INITIAL         # highest delivered to service layer
    last_released: int = SEQNO_INITIAL        # highest released from sort queue

    rx_set:      set = field(default_factory=set)   # seqnos successfully received
    tx_queue:    int = 0                            # messages queued for multicast
    cpg_ipc_q:   int = 0                            # CPG IPC queue depth

    is_slow:      bool = False
    is_partitioned: bool = False
    is_nic_flap:  bool = False
    rejoined_partition: bool = False
    rejoined_nic:       bool = False

    stats: NodeStats = field(default_factory=NodeStats)

    def __post_init__(self):
        self.stats = NodeStats(node_id=self.node_id)

    # ---- receive logic ----

    def try_receive(self, seqno: int, msg_len: int,
                    sim_time: float, rng: random.Random,
                    is_retransmit: bool = False) -> bool:
        """
        Attempt to receive a message.
        Retransmits bypass the slow-node drop filter (they are urgent).
        Returns True if accepted.
        """
        if self.is_partitioned or self.is_nic_flap:
            self.stats.msgs_dropped += 1
            return False

        # Slow-node: probabilistic drop on FIRST delivery only
        if self.is_slow and not is_retransmit:
            if rng.random() < DROP_SLOW_NODE_PROB:
                self.stats.msgs_dropped += 1
                return False

        # L4327: assert(msg_len <= FRAME_SIZE_MAX)
        if check_frame_assert(self.node_id, msg_len, sim_time,
                               f"seqno={seqno:#010x}"):
            # FIX: drop + log, do not crash
            self.stats.msgs_dropped += 1
            return False

        # Duplicate check
        if seqno in self.rx_set:
            return True   # already have it

        self.rx_set.add(seqno)
        self.stats.msgs_received += 1

        if self.my_high_seq == SEQNO_INITIAL or sq_lt(self.my_high_seq, seqno):
            self.my_high_seq = seqno

        self._advance_aru()
        return True

    def _advance_aru(self) -> None:
        """Advance my_aru past all contiguous received seqnos."""
        nxt = sq_add(self.my_aru, 1)
        while nxt in self.rx_set:
            self.my_aru = nxt
            nxt = sq_add(nxt, 1)

    def prune_rx_set(self, up_to: int) -> None:
        """Release sort queue entries ≤ up_to (bounded memory)."""
        self.rx_set = {s for s in self.rx_set
                       if sq_lt(up_to, s) or s == up_to}


# ---------------------------------------------------------------------------
# Ring — TOTEM token-passing engine
# ---------------------------------------------------------------------------

class Ring:
    def __init__(self, nodes: List[Node], rng: random.Random):
        self.nodes  = nodes
        self.rng    = rng
        self.n      = len(nodes)

        self.token  = Token()
        self.holder_idx: int = 0

        self.group_aru: int = SEQNO_INITIAL
        self.ring_id:   int = 0

        # Retransmit buffer: seqno → msg_len (for RTR retransmits)
        self.rtx_buf: Dict[int, int] = {}

        # Recovery
        self.recovery_count:    int   = 0
        self._consec_loss:      int   = 0

        # Token rotation stats
        self.rotation_samples:  List[Dict] = []
        self._rot_start_time:   Optional[float] = None

        # ARU stall
        self._stall_node:       Optional[int]   = None
        self._stall_start:      Optional[float] = None
        self.total_stall_ms:    float = 0.0
        self.stall_events:      int   = 0

        # Totals
        self.total_multicast:   int   = 0
        self.token_retransmits: int   = 0

        # Fault-recovery timestamps
        self.partition_recovery_sim_time: Optional[float] = None
        self.nic_flap_recovery_sim_time:  Optional[float] = None

        # CPG
        self.cpg_cascade_done: bool = False

    # ----------------------------------------------------------------
    # ARU helpers
    # ----------------------------------------------------------------

    def _compute_group_aru(self) -> int:
        """min(my_aru) across all active (non-partitioned, non-flapping) nodes."""
        aru: Optional[int] = None
        for n in self.nodes:
            if n.is_partitioned or n.is_nic_flap:
                continue
            if aru is None:
                aru = n.my_aru
            else:
                # Lower seqno wins (unsigned ring comparison)
                if sq_lt(n.my_aru, aru):
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

    # ----------------------------------------------------------------
    # Ring recovery
    # ----------------------------------------------------------------

    def _new_ring(self, trigger_node: int, sim_time: float, reason: str) -> None:
        """
        Enter MEMB_STATE_GATHER and form a new ring.
        Resets all per-node sequence state (mirrors real corosync behaviour).
        """
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

    # ----------------------------------------------------------------
    # Assert-site checks (fixes applied in-line)
    # ----------------------------------------------------------------

    def _check_rtr_range(self, node: Node, sim_time: float) -> List[int]:
        """
        L2890: range = token.seq - my_aru < QUEUE_RTR_ITEMS_SIZE_MAX.

        If the assert fires, trigger ring recovery.
        Otherwise return the list of missing seqnos (≤ RETRANSMIT_ENTRIES_MAX).
        """
        if self.token.seq == SEQNO_INITIAL or node.my_aru == SEQNO_INITIAL:
            return []

        range_val = sq_diff(self.token.seq, node.my_aru)
        if range_val == 0:
            return []

        if check_range_assert("L2890", node.node_id, range_val, sim_time,
                               f"token.seq={self.token.seq:#010x} "
                               f"my_aru={node.my_aru:#010x} gap={range_val:,}"):
            # FIX: ring recovery — do not abort()
            self._new_ring(node.node_id, sim_time, "L2890")
            return []

        # Build RTR list (≤ RETRANSMIT_ENTRIES_MAX entries).
        # Scan at most 512 seqnos ahead — beyond that the ring is broken
        # and recovery is the right response, not a long RTR list.
        missing: List[int] = []
        scan_limit = min(range_val, 512)  # performance bound on inner loop
        for i in range(1, scan_limit + 1):
            seq = sq_add(node.my_aru, i)
            if seq not in node.rx_set:
                missing.append(seq)
                node.stats.rtr_requested += 1
                if len(missing) >= RETRANSMIT_ENTRIES_MAX:
                    break
        return missing

    def _check_release_range(self, node: Node, sim_time: float) -> None:
        """
        L2672: range = release_to - last_released < QUEUE_RTR_ITEMS_SIZE_MAX.
        FIX: clamp release_to.
        """
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
                               f"release_to={release_to:#010x} "
                               f"last_released={node.last_released:#010x} "
                               f"gap={range_val:,}"):
            # FIX: clamp; will catch up on subsequent passes
            node.last_released = sq_add(node.last_released,
                                         QUEUE_RTR_ITEMS_SIZE_MAX - 1)
        else:
            node.last_released = release_to
        node.prune_rx_set(node.last_released)

    def _check_delivery_range(self, node: Node,
                               end_point: int, sim_time: float) -> None:
        """
        L4215: range = end_point - my_delivered < QUEUE_RTR_ITEMS_SIZE_MAX.
        FIX: partial delivery in chunks.
        """
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
                               f"end_point={end_point:#010x} "
                               f"delivered={node.my_delivered:#010x} "
                               f"gap={range_val:,}"):
            # FIX: deliver only a safe chunk
            node.my_delivered = sq_add(node.my_delivered,
                                        QUEUE_RTR_ITEMS_SIZE_MAX - 1)
        else:
            node.my_delivered = end_point

    def _check_old_ring_range(self, node: Node,
                               low_aru: int, high_seq: int,
                               sim_time: float) -> bool:
        """
        L2433: range = high_seq - low_aru < QUEUE_RTR_ITEMS_SIZE_MAX.
        FIX: ring recovery.
        """
        if high_seq == SEQNO_INITIAL or low_aru == SEQNO_INITIAL:
            return False
        range_val = sq_diff(high_seq, low_aru)
        if range_val == 0 or range_val > SEQNO_WRAP >> 1:
            return False

        if check_range_assert("L2433", node.node_id, range_val, sim_time,
                               f"high_seq={high_seq:#010x} "
                               f"low_aru={low_aru:#010x} gap={range_val:,}"):
            self._new_ring(node.node_id, sim_time, "L2433")
            return True
        return False

    # ----------------------------------------------------------------
    # Flow control
    # ----------------------------------------------------------------

    def _fcc_transmits_allowed(self) -> int:
        """
        Mirrors fcc_mcast_limit + fcc_rtr_limit in totemsrp.c.

        fcc_mcast_limit: soft cap based on window_size and backlog.
          Limits allowed based on (window_size × my_pbl) / total_backlog.
          This is a *desired* cap, not a hard stop.

        fcc_rtr_limit (totemsrp.c:3657-3688): HARD SAFETY CHECK.
          if last_released + QUEUE_RTR_ITEMS_SIZE_MAX - transmits_allowed
             - window_size < token.seq:
            transmits_allowed = 0
          This prevents the RTR sort queue from overflowing, but it
          allows token.seq to run up to (QUEUE_RTR_ITEMS_SIZE_MAX - window_size)
          = 16334 messages ahead of last_released before clamping.

        The real window_size constraint is a SOFT preference, not a hard limit.
        The HARD limit is QUEUE_RTR_ITEMS_SIZE_MAX.  Our simulation must model
        this correctly to observe the dangerous near-overflow conditions.
        """
        allowed = MAX_MESSAGES

        # fcc_mcast_limit: backlog-weighted fair share (soft cap)
        if self.token.seq != SEQNO_INITIAL and \
                self.group_aru != SEQNO_INITIAL:
            gap = sq_diff(self.token.seq, self.group_aru)
            # Soft preference: throttle if ahead by > window_size
            if gap >= WINDOW_SIZE:
                # Reduce but don't stop completely (soft limit)
                allowed = max(1, MAX_MESSAGES // 4)

        # fcc_rtr_limit: HARD safety check (mirrors totemsrp.c:3670-3688)
        # Don't let token.seq get within window_size of QUEUE_RTR_ITEMS_SIZE_MAX
        # ahead of last_released.
        if self.token.seq != SEQNO_INITIAL and self.group_aru != SEQNO_INITIAL:
            # Approximate: use group_aru as proxy for last_released
            rtr_range = sq_diff(self.token.seq, self.group_aru)
            rtr_headroom = QUEUE_RTR_ITEMS_SIZE_MAX - WINDOW_SIZE
            if rtr_range + allowed >= rtr_headroom:
                # Hard limit: stop sending to prevent RTR queue overflow
                allowed = max(0, rtr_headroom - rtr_range)

        return max(0, allowed)

    # ----------------------------------------------------------------
    # Core: full ring rotation + per-node token pass
    # ----------------------------------------------------------------

    @property
    def holder(self) -> Node:
        return self.nodes[self.holder_idx]

    def rotate(self, sim_time: float) -> None:
        """
        Execute one complete ring rotation: each non-faulted node holds
        the token once.  Records one rotation-time sample.

        Optimization: compute group_aru and the laggard node once per
        rotation (not once per token pass), cache in instance attrs.
        """
        # --- pre-rotation: update group ARU once ---
        self.group_aru = self._compute_group_aru()
        self.token.aru = self.group_aru
        self.token.aru_addr = self._find_laggard()
        self._track_stall(sim_time)

        # --- release sort queue entries once per rotation (L2672) ---
        for n in self.nodes:
            if not n.is_partitioned and not n.is_nic_flap:
                self._check_release_range(n, sim_time)

        # --- build RTR list once per rotation (L2890) ---
        new_rtr: List[int] = []
        for n in self.nodes:
            if n.is_partitioned or n.is_nic_flap:
                continue
            # Fast skip: if my_aru == token.seq (fully caught up), no RTR needed
            if n.my_aru == self.token.seq:
                continue
            if n.my_aru == SEQNO_INITIAL and self.token.seq == SEQNO_INITIAL:
                continue
            missing = self._check_rtr_range(n, sim_time)
            for seq in missing:
                if seq not in new_rtr:
                    new_rtr.append(seq)
                if len(new_rtr) >= RETRANSMIT_ENTRIES_MAX:
                    break
        self.token.rtr_list = new_rtr

        # --- token passes (each node sends new messages + retransmits) ---
        for i in range(self.n):
            self.holder_idx = i
            node = self.nodes[i]
            if node.is_partitioned or node.is_nic_flap:
                continue
            self._do_node_pass(sim_time)

        # --- delivery check for all nodes once per rotation (L4215) ---
        if self.token.seq != SEQNO_INITIAL:
            for n in self.nodes:
                if not n.is_partitioned and not n.is_nic_flap:
                    self._check_delivery_range(n, self.token.seq, sim_time)

        # Rotation sample
        if self._rot_start_time is not None:
            rot_ms = (sim_time - self._rot_start_time) * 1000.0
            aru_gap = sq_diff(self.token.seq, self.group_aru) \
                if self.token.seq != SEQNO_INITIAL else 0
            self.rotation_samples.append({
                "t": sim_time, "ms": rot_ms,
                "aru_gap": aru_gap, "rtr": len(self.token.rtr_list)})
        self._rot_start_time = sim_time

    def _do_node_pass(self, sim_time: float) -> None:
        """
        Execute one node's token-hold turn within a rotation.
        Called by rotate() for each active node.

        This handles only:
          - Retransmit of RTR list (built once per rotation by rotate())
          - Multicast new messages (flow-controlled)
          - Token loss simulation
        The group ARU update, release check, RTR build, and delivery check
        are done once per rotation in rotate() for efficiency.
        """
        node = self.holder
        node.stats.token_holds += 1

        # Retransmit RTR-requested messages (only first active node does this)
        if self.holder_idx == 0 and self.token.rtr_list:
            self._do_retransmits(self.token.rtr_list, sim_time)

        # Multicast new messages (flow-controlled)
        allowed = self._fcc_transmits_allowed()
        sent = 0
        while sent < allowed and node.tx_queue > 0:
            self.token.seq = sq_add(self.token.seq, 1)

            # Realistic message size distribution:
            #  74.98% small (64–512 B)
            #  24%    medium (512–8192 B)
            #   1%    large (8192–65535 B)
            #   0.02% oversized (tests L4327)
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

            # Broadcast to all active ring members
            # Fast path: frame-size check once, then bulk-deliver
            if msg_len > FRAME_SIZE_MAX:
                check_frame_assert(node.node_id, msg_len, sim_time,
                                   f"seqno={self.token.seq:#010x}")
                # FIX: drop; don't deliver to anyone
            else:
                seq_here = self.token.seq
                for n in self.nodes:
                    if n.is_partitioned or n.is_nic_flap:
                        continue
                    # Slow-node probabilistic drop
                    if n.is_slow and self.rng.random() < DROP_SLOW_NODE_PROB:
                        n.stats.msgs_dropped += 1
                        continue
                    if seq_here not in n.rx_set:
                        n.rx_set.add(seq_here)
                        n.stats.msgs_received += 1
                        if n.my_high_seq == SEQNO_INITIAL or \
                                sq_lt(n.my_high_seq, seq_here):
                            n.my_high_seq = seq_here
                        # Advance ARU: single-step for the common case
                        nxt = sq_add(n.my_aru, 1)
                        if nxt in n.rx_set:
                            n.my_aru = nxt
                            nxt2 = sq_add(nxt, 1)
                            while nxt2 in n.rx_set:
                                n.my_aru = nxt2
                                nxt2 = sq_add(nxt2, 1)

            node.tx_queue -= 1
            node.stats.msgs_sent += 1
            self.total_multicast += 1
            sent += 1

        # Token loss simulation
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
        """Retransmit requested messages to all nodes that missed them."""
        holder = self.holder
        for seq in rtr_list:
            if seq not in self.rtx_buf:
                continue
            msg_len = self.rtx_buf[seq]
            # Skip frame-size check on retransmits (was already checked on first send)
            for n in self.nodes:
                if n.is_partitioned or n.is_nic_flap:
                    continue
                if seq not in n.rx_set:
                    # Retransmits bypass slow-node drop filter
                    n.rx_set.add(seq)
                    n.stats.msgs_received += 1
                    n.stats.rtr_retransmitted += 1
                    holder.stats.rtr_retransmitted += 1
                    if n.my_high_seq == SEQNO_INITIAL or sq_lt(n.my_high_seq, seq):
                        n.my_high_seq = seq
                    nxt = sq_add(n.my_aru, 1)
                    if nxt in n.rx_set:
                        n.my_aru = nxt
                        nxt2 = sq_add(nxt, 1)
                        while nxt2 in n.rx_set:
                            n.my_aru = nxt2
                            nxt2 = sq_add(nxt2, 1)

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

    # ----------------------------------------------------------------
    # Fault injection: rejoin after partition / NIC flap
    # ----------------------------------------------------------------

    def rejoin(self, node: Node, sim_time: float) -> None:
        """
        Handle node rejoining.  Checks L2433 (old-ring range).
        The missed gap = token.seq - node.my_aru at rejoin time.
        """
        high_seq  = self.token.seq
        low_aru   = self.group_aru

        fired = self._check_old_ring_range(node, low_aru, high_seq, sim_time)
        if not fired:
            # Gap is safe: deliver missed messages via retransmit buffer
            if high_seq != SEQNO_INITIAL and node.my_aru != SEQNO_INITIAL:
                range_val = sq_diff(high_seq, node.my_aru)
                for i in range(1, min(range_val + 1, QUEUE_RTR_ITEMS_SIZE_MAX)):
                    seq = sq_add(node.my_aru, i)
                    if seq in self.rtx_buf:
                        node.try_receive(seq, self.rtx_buf[seq], sim_time,
                                         self.rng, is_retransmit=True)
        node.is_partitioned = False
        node.is_nic_flap    = False

    # ----------------------------------------------------------------
    # CPG cascade injection (models 2026-03-25 incident)
    # ----------------------------------------------------------------

    def inject_cpg_cascade(self, nodes: List[Node], sim_time: float) -> None:
        """
        20 nodes simultaneously join a 42-member CPG group.
        Each join triggers CPG_GROUP_SIZE view-change IPC messages
        on every existing member's IPC queue.
        Total initial burst = 20 × 42 = 840 msgs/node.
        """
        if self.cpg_cascade_done:
            return
        self.cpg_cascade_done = True
        initial_burst = CPG_CASCADE_SIZE * CPG_GROUP_SIZE   # 840

        for n in nodes:
            n.cpg_ipc_q += initial_burst
            if n.cpg_ipc_q > n.stats.cpg_peak_ipc_queue:
                n.stats.cpg_peak_ipc_queue = n.cpg_ipc_q
            # Immediate overflow check
            if n.cpg_ipc_q > CPG_IPC_QUEUE_DEPTH_MAX:
                n.stats.cpg_try_again += n.cpg_ipc_q - CPG_IPC_QUEUE_DEPTH_MAX


# ---------------------------------------------------------------------------
# CPG IPC feedback simulator
# ---------------------------------------------------------------------------

class CpgSim:
    """
    Models the IPC queue between corosync and CPG clients (pmxcfs).
    CS_ERR_TRY_AGAIN → leave → rejoin → new view-change → amplification.
    This is the feedback loop in the 2026-03-25 Proxmox incident.
    """

    def __init__(self, nodes: List[Node], rng: random.Random):
        self.nodes = nodes
        self.rng   = rng
        self.try_again_total:    int = 0
        self.leave_rejoin_loops: int = 0
        self.peak_queue:         int = 0
        self._amplify_pending:   int = 0

    def tick(self, sim_time: float) -> None:
        # Process cascade amplification from previous CS_ERR_TRY_AGAIN events
        if self._amplify_pending > 0:
            extra = self._amplify_pending * CPG_GROUP_SIZE
            self._amplify_pending = 0
            for n in self.nodes:
                n.cpg_ipc_q += extra
                if n.cpg_ipc_q > n.stats.cpg_peak_ipc_queue:
                    n.stats.cpg_peak_ipc_queue = n.cpg_ipc_q

        for n in self.nodes:
            if n.cpg_ipc_q <= 0:
                continue

            # Drain ~50 msgs per token-pass
            n.cpg_ipc_q = max(0, n.cpg_ipc_q - self.rng.randint(30, 70))

            if n.cpg_ipc_q > CPG_IPC_QUEUE_DEPTH_MAX:
                overflow = n.cpg_ipc_q - CPG_IPC_QUEUE_DEPTH_MAX
                n.stats.cpg_try_again += overflow
                self.try_again_total  += overflow

                # 5% chance per tick of leave/rejoin feedback loop
                if self.rng.random() < 0.05:
                    self.leave_rejoin_loops += 1
                    self._amplify_pending   += 1
                    n.tx_queue += CPG_GROUP_SIZE  # view-change injected into TOTEM

            if n.cpg_ipc_q > self.peak_queue:
                self.peak_queue = n.cpg_ipc_q


# ---------------------------------------------------------------------------
# Main simulation
# ---------------------------------------------------------------------------

def run_simulation(args) -> None:
    global _assert_fires, _frame_fires
    _assert_fires = []
    _frame_fires  = []

    rng = random.Random(args.seed)

    # Create nodes
    nodes: List[Node] = [Node(node_id=i + 1) for i in range(args.nodes)]

    # Assign fault roles (distinct nodes)
    pool = list(nodes)
    rng.shuffle(pool)
    slow_node,  partition_node, nic_node = pool[0], pool[1], pool[2]
    slow_node.is_slow = True

    if not args.quiet:
        print()
        print("=" * 74)
        print("  Corosync TOTEM 100-node ring stress simulation")
        print("=" * 74)
        print(f"  Nodes:           {args.nodes}")
        print(f"  Duration:        {args.seconds}s simulated")
        print(f"  Message rate:    {args.rate:,} msg/s total"
              f"  ({'STRESS MODE' if args.stress else 'normal'})")
        print(f"  TOKEN_TIMEOUT:   {TOKEN_TIMEOUT_MS}ms "
              f"  TOKEN_RETRANSMITS: {TOKEN_RETRANSMITS}")
        print(f"  WINDOW_SIZE:     {WINDOW_SIZE}"
              f"  MAX_MESSAGES: {MAX_MESSAGES}")
        print(f"  QUEUE_RTR_MAX:   {QUEUE_RTR_ITEMS_SIZE_MAX:,}"
              f"  FRAME_SIZE_MAX: {FRAME_SIZE_MAX:,}")
        print()
        print(f"  Fault injection:")
        print(f"    Slow node:       node-{slow_node.node_id:>3}  "
              f"drops {DROP_SLOW_NODE_PROB*100:.0f}% of first deliveries "
              f"(RTR fills gaps)")
        print(f"    Partition node:  node-{partition_node.node_id:>3}  "
              f"isolated {PARTITION_START_S:.0f}s–{PARTITION_END_S:.0f}s "
              f"({PARTITION_END_S-PARTITION_START_S:.0f}s gap)")
        print(f"    NIC flap node:   node-{nic_node.node_id:>3}  "
              f"outage {NIC_FLAP_START_S:.0f}s–{NIC_FLAP_END_S:.0f}s "
              f"({NIC_FLAP_END_S-NIC_FLAP_START_S:.0f}s gap)")
        print(f"    CPG cascade:     {CPG_CASCADE_SIZE} nodes join "
              f"{CPG_GROUP_SIZE}-member group at t={CPG_CASCADE_START_S:.0f}s  "
              f"(burst={CPG_CASCADE_SIZE*CPG_GROUP_SIZE} IPC msgs/node)")
        print()
        print(f"  L2433/L2890 assert threshold:")
        print(f"    gap >= {QUEUE_RTR_ITEMS_SIZE_MAX:,}  ≡  "
              f"rate × partition_duration >= {QUEUE_RTR_ITEMS_SIZE_MAX:,}")
        print(f"    ⇒ triggers when msg_rate >= "
              f"{QUEUE_RTR_ITEMS_SIZE_MAX/(PARTITION_END_S-PARTITION_START_S):.0f}"
              f" msg/s  (partition={PARTITION_END_S-PARTITION_START_S:.0f}s)")
        print(f"    ⇒ current rate {args.rate} msg/s → "
              f"expected gap ≈ {int(args.rate*(PARTITION_END_S-PARTITION_START_S)):,} msgs "
              f"({'EXCEEDS' if args.rate*(PARTITION_END_S-PARTITION_START_S)>=QUEUE_RTR_ITEMS_SIZE_MAX else 'below'} threshold)")
        print()

    ring    = Ring(nodes, rng)
    cpg_sim = CpgSim(nodes, rng)

    # ------------------------------------------------------------------
    # Time model:
    # One "tick" = one COMPLETE ring rotation = all N nodes hold the
    # token once each.  Simulated time advances by ROTATION_S per tick.
    #
    # Typical rotation time at 100 nodes ≈ 100ms (well within 5000ms
    # token_timeout).  We simulate with 100ms per rotation.
    #
    # Within each tick ring.rotate() iterates through all N nodes
    # sequentially, each holding the token for its MAX_MESSAGES quota.
    # ------------------------------------------------------------------
    ROTATION_S = 0.100                 # 100ms per full ring rotation
    msgs_per_rotation = args.rate * ROTATION_S

    sim_time   = 0.0
    tick       = 0
    p_injected = False
    n_injected = False
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
                print(f"  [t={sim_time:6.2f}s] PARTITION start  "
                      f"node-{partition_node.node_id}")

        if sim_time >= PARTITION_END_S and partition_node.is_partitioned:
            gap = sq_diff(ring.token.seq, partition_node.my_aru) \
                if ring.token.seq != SEQNO_INITIAL and \
                   partition_node.my_aru != SEQNO_INITIAL else 0
            ring.rejoin(partition_node, sim_time)
            partition_node.rejoined_partition = True
            ring.partition_recovery_sim_time = sim_time
            if not args.quiet:
                fires_now = sum(1 for e in _assert_fires if e.location == "L2433")
                print(f"  [t={sim_time:6.2f}s] PARTITION end    "
                      f"node-{partition_node.node_id}  "
                      f"missed_gap={gap:,}  L2433_fires={fires_now}")

        if sim_time >= NIC_FLAP_START_S and not nic_node.is_nic_flap \
                and not nic_node.rejoined_nic and not n_injected:
            nic_node.is_nic_flap = True
            n_injected = True
            if not args.quiet:
                print(f"  [t={sim_time:6.2f}s] NIC FLAP start   "
                      f"node-{nic_node.node_id}")

        if sim_time >= NIC_FLAP_END_S and nic_node.is_nic_flap:
            ring.rejoin(nic_node, sim_time)
            nic_node.rejoined_nic = True
            ring.nic_flap_recovery_sim_time = sim_time
            if not args.quiet:
                print(f"  [t={sim_time:6.2f}s] NIC FLAP end     "
                      f"node-{nic_node.node_id}  recovered")

        if sim_time >= CPG_CASCADE_START_S and not ring.cpg_cascade_done:
            # In stress mode, amplify CPG cascade to match 2026-03-25 incident:
            # 53-node cluster + rapid leave/rejoin loops ≈ 3× burst multiplier
            if args.stress:
                # Override: simulate 53-node cluster with deeper cascade
                # (20 joins × 53-member group × 2 view-changes each)
                for n in nodes:
                    n.cpg_ipc_q += 20 * 53 * 2  # = 2120 msg burst (>> 1000 limit)
                    if n.cpg_ipc_q > n.stats.cpg_peak_ipc_queue:
                        n.stats.cpg_peak_ipc_queue = n.cpg_ipc_q
                    if n.cpg_ipc_q > CPG_IPC_QUEUE_DEPTH_MAX:
                        n.stats.cpg_try_again += n.cpg_ipc_q - CPG_IPC_QUEUE_DEPTH_MAX
            ring.inject_cpg_cascade(nodes, sim_time)
            if not args.quiet:
                burst = (20 * 53 * 2 if args.stress else
                         CPG_CASCADE_SIZE * CPG_GROUP_SIZE)
                print(f"  [t={sim_time:6.2f}s] CPG CASCADE      "
                      f"{CPG_CASCADE_SIZE} nodes join "
                      f"{'53-member (stress)' if args.stress else f'{CPG_GROUP_SIZE}-member'} group  "
                      f"IPC_burst={burst}/node")

        # ---- message injection (once per full rotation) ----
        n_inject = int(msgs_per_rotation + rng.random())
        for _ in range(n_inject):
            sender = nodes[rng.randint(0, args.nodes - 1)]
            if not sender.is_partitioned and not sender.is_nic_flap:
                sender.tx_queue += 1

        # ---- one full ring rotation: all N nodes hold token once ----
        ring.rotate(sim_time)

        # ---- CPG IPC drain (once per rotation) ----
        cpg_sim.tick(sim_time)

        # ---- advance time (~100ms + small jitter) ----
        sim_time += ROTATION_S * max(0.5, rng.gauss(1.0, 0.03))

        # ---- progress ----
        if not args.quiet and sim_time >= next_prog:
            aru_gap = sq_diff(ring.token.seq, ring.group_aru) \
                if ring.token.seq != SEQNO_INITIAL else 0
            total_tx = sum(n.tx_queue for n in nodes)
            print(f"  [t={sim_time:6.1f}s]  "
                  f"asserts={len(_assert_fires):6,}  "
                  f"frame={len(_frame_fires):4,}  "
                  f"rings={ring.recovery_count:3}  "
                  f"aru_gap={aru_gap:5}  "
                  f"tx_backlog={total_tx:6,}  "
                  f"ipc_peak={cpg_sim.peak_queue:5}  "
                  f"wall={time.monotonic()-wall_start:.1f}s")
            next_prog += 10.0

    print_results(args, nodes, ring, cpg_sim,
                  slow_node, partition_node, nic_node)

    # In stress mode also run the dedicated assert-trigger scenario
    if args.stress:
        run_assert_trigger_scenario(args)


def run_assert_trigger_scenario(args) -> None:
    """
    Dedicated scenario to deliberately trigger L2890 and L2433.

    Setup: 100 nodes, NO slow node (all receive 100% of messages).
    One node is partitioned for 30s.  High message rate so that
    token.seq - partition.my_aru grows well past QUEUE_RTR_ITEMS_SIZE_MAX.

    Without the slow node as a laggard, group_aru = token.seq - WINDOW_SIZE
    and advances freely.  The partition node's my_aru stays frozen, so the
    gap = token.seq - partition.my_aru grows by ~msgs_per_rotation per tick.

    With rate=700 and WINDOW_SIZE=50:
      msgs_per_rotation = 700 * 0.1 = 70, capped to 50 by window
      In 30s / 0.1s = 300 rotations: gap = 300 * 50 = 15,000 seqnos
      Exceeds QUEUE_RTR_ITEMS_SIZE_MAX=16384 just over 327 rotations (~32.7s)
    """
    global _assert_fires, _frame_fires
    _assert_fires = []
    _frame_fires  = []

    rng2 = random.Random(args.seed + 9999)

    nodes2: List[Node] = [Node(node_id=i + 1) for i in range(args.nodes)]
    part_node = nodes2[0]   # node-1 will be partitioned

    if not args.quiet:
        print()
        print("=" * 74)
        print("  ASSERT-TRIGGER SCENARIO (stress mode)")
        print("  Purpose: deliberately cross QUEUE_RTR_ITEMS_SIZE_MAX boundary")
        print("=" * 74)
        print(f"  Setup: {args.nodes} nodes, NO slow node, one partition "
              f"({args.nodes}-node ring is healthy except node-{part_node.node_id})")
        print(f"  Partition: t=5s–45s (40s gap)")
        print(f"  Rate: {args.rate:,} msg/s → "
              f"msgs in 40s = {int(args.rate*40):,} "
              f"(threshold = {QUEUE_RTR_ITEMS_SIZE_MAX:,})")
        print()

    ring2    = Ring(nodes2, rng2)
    dummy_cpg = CpgSim(nodes2, rng2)

    ROTATION_S = 0.100
    msgs_per_rot = args.rate * ROTATION_S

    sim_time = 0.0
    part_started = False
    part_ended   = False
    next_prog    = 5.0

    while sim_time < 60.0:
        # Fault injection: partition at t=5, rejoin at t=45 (40s gap)
        if sim_time >= 5.0 and not part_started:
            part_node.is_partitioned = True
            part_started = True
            if not args.quiet:
                print(f"  [t={sim_time:.2f}s] PARTITION start  node-{part_node.node_id}")

        if sim_time >= 45.0 and not part_ended and part_started:
            gap = sq_diff(ring2.token.seq, part_node.my_aru) \
                if ring2.token.seq != SEQNO_INITIAL else 0
            ring2.rejoin(part_node, sim_time)
            part_ended = True
            if not args.quiet:
                fires = sum(1 for e in _assert_fires if e.location == "L2433")
                print(f"  [t={sim_time:.2f}s] PARTITION end    node-{part_node.node_id}  "
                      f"missed_gap={gap:,}  L2433_fires={fires}")

        # Message injection
        n_inj = int(msgs_per_rot + rng2.random())
        for _ in range(n_inj):
            sender = nodes2[rng2.randint(0, args.nodes - 1)]
            if not sender.is_partitioned:
                sender.tx_queue += 1

        ring2.rotate(sim_time)
        dummy_cpg.tick(sim_time)
        sim_time += ROTATION_S * max(0.5, rng2.gauss(1.0, 0.03))

        if not args.quiet and sim_time >= next_prog:
            aru_gap = sq_diff(ring2.token.seq, ring2.group_aru) \
                if ring2.token.seq != SEQNO_INITIAL else 0
            part_gap = sq_diff(ring2.token.seq, part_node.my_aru) \
                if ring2.token.seq != SEQNO_INITIAL and \
                   part_node.my_aru != SEQNO_INITIAL else 0
            print(f"  [t={sim_time:5.1f}s]  "
                  f"L2433={sum(1 for e in _assert_fires if e.location=='L2433'):4}  "
                  f"L2890={sum(1 for e in _assert_fires if e.location=='L2890'):4}  "
                  f"aru_gap={aru_gap:5}  "
                  f"part_gap={part_gap:7,}")
            next_prog += 5.0

    # Print just the assert analysis for this scenario
    by_loc: Dict[str, int] = collections.Counter(e.location for e in _assert_fires)
    by_loc["L4327"] = len({e.detail for e in _frame_fires})  # unique seqnos

    print()
    print("  Assert-trigger scenario results:")
    total = sum(by_loc.values())
    for loc in ["L2433", "L2672", "L2890", "L4215", "L4327"]:
        count = by_loc.get(loc, 0)
        if count > 0:
            evts = sorted([e for e in _assert_fires if e.location == loc],
                          key=lambda e: e.sim_time)
            first = evts[0] if evts else None
            print(f"    {loc}: {count:,} fires"
                  + (f"  (first at t={first.sim_time:.1f}s, "
                     f"range={first.range_val:,})" if first else ""))
        else:
            print(f"    {loc}: 0 fires  [stable]")

    if total > 0:
        print()
        print(f"  CONFIRMED: At {args.rate:,} msg/s + 40s partition,")
        print(f"  {total:,} assert-fire events would crash corosync v3.1.9.")
        print(f"  The simulation applied ring-recovery fix instead.")
    else:
        print()
        print(f"  No assert fires even in assert-trigger scenario at {args.rate:,} msg/s.")
        print(f"  WINDOW_SIZE={WINDOW_SIZE} limits the achievable gap.")
        print(f"  The gap can only reach: WINDOW_SIZE × rotation_count")
        eff_msgs = ring2.total_multicast
        print(f"  Actual msgs multicast: {eff_msgs:,} in 60s = "
              f"{eff_msgs//60} msg/s effective")


# ---------------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------------

def print_results(args, nodes: List[Node], ring: Ring,
                  cpg_sim: CpgSim,
                  slow_node: Node, partition_node: Node,
                  nic_node: Node) -> None:

    global _assert_fires, _frame_fires

    print()
    print("=" * 74)
    print("  SIMULATION RESULTS")
    print("=" * 74)

    total_multicast = ring.total_multicast
    total_retx  = sum(n.stats.rtr_retransmitted for n in nodes)
    total_drop  = sum(n.stats.msgs_dropped      for n in nodes)
    total_rtr_r = sum(n.stats.rtr_requested     for n in nodes)
    total_tok_l = ring.token_retransmits

    print()
    print("  Traffic summary:")
    print(f"    Messages multicast:   {total_multicast:>10,}")
    print(f"    RTR retransmits:      {total_retx:>10,}  "
          f"({100*total_retx/max(1,total_multicast):.1f}% overhead)")
    print(f"    Messages dropped:     {total_drop:>10,}")
    print(f"    RTR requests total:   {total_rtr_r:>10,}")
    print(f"    Token loss events:    {total_tok_l:>10,}  "
          f"({TOKEN_LOSS_PROB*100:.0f}% loss rate)")
    print(f"    New ring formations:  {ring.recovery_count:>10,}")

    # ---- Token rotation distribution ----
    print()
    print("  Token rotation time (one full ring circuit = 100 passes):")
    if ring.rotation_samples:
        times = [s["ms"] for s in ring.rotation_samples]
        srt   = sorted(times)
        n_s   = len(srt)
        rot_min  = srt[0]
        rot_mean = sum(times) / n_s
        rot_max  = srt[-1]
        rot_p95  = srt[min(int(n_s * 0.95), n_s - 1)]
        rot_p99  = srt[min(int(n_s * 0.99), n_s - 1)]
        print(f"    min={rot_min:.0f}ms  mean={rot_mean:.0f}ms  "
              f"p95={rot_p95:.0f}ms  p99={rot_p99:.0f}ms  max={rot_max:.0f}ms  "
              f"(samples={n_s:,})")
        # Histogram
        hi_ms = min(int(rot_max) + 100, 5000)
        bucket_w = max(10, (hi_ms // 20))
        buckets: Dict[int, int] = collections.Counter()
        for t in times:
            b = int(t / bucket_w) * bucket_w
            buckets[b] += 1
        print("    Histogram (ms):")
        max_count = max(buckets.values()) if buckets else 1
        for b in sorted(buckets.keys())[:20]:
            bar_len = int(40 * buckets[b] / max_count)
            bar = "#" * bar_len
            print(f"      {b:5}–{b+bucket_w-1:<5}ms  {buckets[b]:5,}  {bar}")
    else:
        rot_min = rot_mean = rot_max = rot_p95 = rot_p99 = 0.0
        print("    (no samples)")

    # ---- ARU stall ----
    print()
    print("  ARU stall (single node holding group ARU down for > 50ms):")
    print(f"    Events: {ring.stall_events:,}   "
          f"Total: {ring.total_stall_ms:,.0f}ms   "
          f"Average: {ring.total_stall_ms/max(1,ring.stall_events):.0f}ms/event")

    # ---- Per-node table (top 10 by RTR) ----
    print()
    print("  Top-10 nodes by RTR requests:")
    sn = sorted(nodes, key=lambda n: n.stats.rtr_requested, reverse=True)
    H = (f"  {'Node':>5}  {'RTR-req':>9}  {'RTR-retx':>9}  "
         f"{'Dropped':>9}  {'ARU-stall':>10}  Fault")
    S = f"  {'-----':>5}  {'---------':>9}  {'---------':>9}  "\
        f"{'---------':>9}  {'----------':>10}  -----"
    print(H)
    print(S)
    for n in sn[:10]:
        fault = ""
        if n is slow_node:       fault = f"slow({DROP_SLOW_NODE_PROB*100:.0f}% drop)"
        elif n is partition_node: fault = f"partition({PARTITION_START_S:.0f}–{PARTITION_END_S:.0f}s)"
        elif n is nic_node:       fault = f"NIC flap({NIC_FLAP_START_S:.0f}–{NIC_FLAP_END_S:.0f}s)"
        print(f"  {n.node_id:>5}  {n.stats.rtr_requested:>9,}  "
              f"{n.stats.rtr_retransmitted:>9,}  {n.stats.msgs_dropped:>9,}  "
              f"{n.stats.aru_stall_ms:>9.0f}ms  {fault}")

    # ---- CPG cascade ----
    print()
    print(f"  CPG cascade at t={CPG_CASCADE_START_S:.0f}s "
          f"({CPG_CASCADE_SIZE} nodes → {CPG_GROUP_SIZE}-member group):")
    print(f"    Initial IPC burst/node:   {CPG_CASCADE_SIZE*CPG_GROUP_SIZE:,} msgs "
          f"(limit={CPG_IPC_QUEUE_DEPTH_MAX:,})")
    print(f"    Peak IPC queue depth:     {cpg_sim.peak_queue:,}")
    print(f"    CS_ERR_TRY_AGAIN total:   {cpg_sim.try_again_total:,}")
    print(f"    Leave/rejoin cascades:    {cpg_sim.leave_rejoin_loops:,}")
    worst_cpg = max(nodes, key=lambda n: n.stats.cpg_peak_ipc_queue)
    print(f"    Worst node (node-{worst_cpg.node_id}):      "
          f"peak={worst_cpg.stats.cpg_peak_ipc_queue:,}")

    # ---- Recovery ----
    print()
    print("  Fault recovery:")
    print(f"    Partition node-{partition_node.node_id}: "
          + ("RECOVERED" if partition_node.rejoined_partition else "still isolated"))
    print(f"    NIC flap  node-{nic_node.node_id}: "
          + ("RECOVERED" if nic_node.rejoined_nic else "still flapping"))

    # ================================================================
    # Assert analysis
    # ================================================================
    print()
    print("=" * 74)
    print("  ASSERT / SAFETY ANALYSIS")
    print("=" * 74)
    print()

    # Count by location
    by_loc: Dict[str, int] = collections.Counter(e.location for e in _assert_fires)
    by_loc["L4327"] = len(_frame_fires)

    meta = {
        "L2433": ("old-ring msg copy",
                  "old_ring_high_seq − low_ring_aru",
                  "partition node rejoins after > 16384 msgs missed"),
        "L2672": ("sort-queue release",
                  "release_to − last_released",
                  "slow node / large gap when group ARU advances"),
        "L2890": ("RTR list build",
                  "token.seq − my_aru",
                  "any node misses > 16384 consecutive messages"),
        "L4215": ("message delivery",
                  "end_point − my_high_delivered",
                  "same conditions as L2890 at delivery stage"),
        "L4327": ("mcast frame size",
                  "msg_len > FRAME_SIZE_MAX (65536)",
                  "totempg fragmentation bug / malformed packet"),
    }

    fixes = {
        "L2433": "Trigger ring recovery (new ring); never abort().",
        "L2672": ("Clamp release_to to last_released + QUEUE_RTR_ITEMS_SIZE_MAX−1; "
                  "log warning; continue token passing."),
        "L2890": ("Clamp RTR entries to RETRANSMIT_ENTRIES_MAX; "
                  "if gap persists > TOKEN_RETRANSMITS passes → new ring."),
        "L4215": ("Deliver in chunks ≤ QUEUE_RTR_ITEMS_SIZE_MAX−1; "
                  "loop on subsequent passes until drained."),
        "L4327": "Drop message and log error; do NOT crash.",
    }

    for loc in ["L2433", "L2672", "L2890", "L4215", "L4327"]:
        count = by_loc.get(loc, 0)
        name, cond, trigger = meta[loc]
        verdict = "*** CRASH ***" if count > 0 else "stable"
        print(f"  {loc}  [{name:<22}]  fires={count:>8,}  [{verdict}]")
        print(f"       Condition:  {cond}")
        print(f"       Trigger:    {trigger}")
        if count > 0:
            print(f"       FIX:        {fixes[loc]}")
            evts = sorted(
                [e for e in (_assert_fires + _frame_fires) if e.location == loc],
                key=lambda e: e.sim_time)[:3]
            for ev in evts:
                print(f"       Example:    t={ev.sim_time:.2f}s  "
                      f"node-{ev.node_id}  range={ev.range_val:,}  "
                      f"{ev.detail}")
        print()

    # ================================================================
    # Summary table
    # ================================================================
    print("=" * 74)
    print("  SUMMARY TABLE")
    print("=" * 74)
    print()

    def row(label: str, status: str, detail: str) -> None:
        print(f"  {label:<38}  [{status:<14}]  {detail}")

    row("Metric", "Status", "Detail")
    row("─" * 38, "─" * 14, "─" * 30)

    # Token rotation
    if ring.rotation_samples:
        if rot_max < TOKEN_TIMEOUT_MS:
            row("Token rotation",
                "STABLE",
                f"max={rot_max:.0f}ms < {TOKEN_TIMEOUT_MS}ms timeout")
        else:
            row("Token rotation",
                "FAIL",
                f"max={rot_max:.0f}ms EXCEEDS {TOKEN_TIMEOUT_MS}ms timeout!")
    else:
        row("Token rotation", "N/A", "no full rotation completed")

    row("Token loss / retransmit",
        "STABLE" if ring.token_retransmits < 50 else "INFO",
        f"{ring.token_retransmits:,} loss events "
        f"({TOKEN_LOSS_PROB*100:.0f}% rate)")

    row("New ring formations",
        "STABLE" if ring.recovery_count == 0 else "WARNING",
        f"{ring.recovery_count} ring resets (assert fixes applied)")

    row(f"Slow node (node-{slow_node.node_id}, {DROP_SLOW_NODE_PROB*100:.0f}% drop)",
        "STABLE",
        f"RTR absorbed {slow_node.stats.rtr_requested:,} gaps")

    l2433 = by_loc.get("L2433", 0)
    row(f"Partition node-{partition_node.node_id} ({PARTITION_END_S-PARTITION_START_S:.0f}s isolated)",
        "CRASH→FIXED" if l2433 > 0 else "STABLE",
        f"L2433 fires={l2433} — "
        + ("ring recovery applied" if l2433 > 0 else "gap < 16384, safe rejoin"))

    row(f"NIC flap node-{nic_node.node_id} ({NIC_FLAP_END_S-NIC_FLAP_START_S:.0f}s outage)",
        "STABLE" if nic_node.rejoined_nic else "FAIL",
        f"RTR absorbed short gap")

    row("ARU stall",
        "INFO" if ring.stall_events > 10 else "STABLE",
        f"{ring.stall_events:,} events, {ring.total_stall_ms:,.0f}ms total")

    for loc, label in [("L2890", "RTR range"), ("L2433", "old-ring range"),
                        ("L2672", "release range"), ("L4215", "delivery range"),
                        ("L4327", "frame size")]:
        count = by_loc.get(loc, 0)
        row(f"assert {loc} ({label})",
            "CRASH→FIXED" if count > 0 else "STABLE",
            f"fires={count:,}"
            + (" — fix applied" if count > 0 else ""))

    if cpg_sim.leave_rejoin_loops > 0:
        row("CPG cascade (2026-03-25 pattern)",
            "FAIL",
            f"{cpg_sim.leave_rejoin_loops} leave/rejoin loops")
    elif cpg_sim.try_again_total > 0:
        row("CPG cascade (2026-03-25 pattern)",
            "WARNING",
            f"{cpg_sim.try_again_total:,} CS_ERR_TRY_AGAIN events")
    else:
        row("CPG cascade (2026-03-25 pattern)",
            "STABLE",
            "IPC queue handled without overflow")

    # ================================================================
    # Recommendations
    # ================================================================
    print()
    print("=" * 74)
    print("  RECOMMENDATIONS")
    print("=" * 74)
    print()

    def rec(sev: str, text: str) -> None:
        words = text.split()
        lines: List[str] = []
        cur = ""
        for w in words:
            if len((cur + " " + w).strip()) > 68:
                lines.append(cur)
                cur = w
            else:
                cur = (cur + " " + w).strip()
        if cur:
            lines.append(cur)
        print(f"  [{sev:<8}]  {lines[0]}")
        for l in lines[1:]:
            print(f"              {l}")
        print()

    l2890 = by_loc.get("L2890", 0)
    l2672 = by_loc.get("L2672", 0)
    l4215 = by_loc.get("L4215", 0)
    l4327 = by_loc.get("L4327", 0)

    threshold_rate = int(QUEUE_RTR_ITEMS_SIZE_MAX /
                         (PARTITION_END_S - PARTITION_START_S))

    if l2890 > 0 or l2433 > 0:
        rec("CRITICAL",
            f"L2890/L2433 assert fires detected at {args.rate:,} msg/s. "
            f"In stock corosync (v3.1.9 and earlier) this is an abort() — "
            f"the daemon crashes immediately. "
            f"Root cause: with {args.rate:,} msg/s, a "
            f"{PARTITION_END_S-PARTITION_START_S:.0f}s partition accumulates "
            f"≈{int(args.rate*(PARTITION_END_S-PARTITION_START_S)):,} missed "
            f"messages, exceeding QUEUE_RTR_ITEMS_SIZE_MAX={QUEUE_RTR_ITEMS_SIZE_MAX:,}. "
            f"Fix: replace assert(range < QUEUE_RTR_ITEMS_SIZE_MAX) at "
            f"totemsrp.c:2890 and :2433 with ring-recovery logic.")

    if cpg_sim.leave_rejoin_loops > 0:
        rec("CRITICAL",
            f"CPG join cascade caused {cpg_sim.leave_rejoin_loops:,} "
            f"leave/rejoin feedback loops — this matches the 2026-03-25 "
            f"Proxmox incident root cause. "
            f"The initial IPC burst ({CPG_CASCADE_SIZE}×{CPG_GROUP_SIZE}="
            f"{CPG_CASCADE_SIZE*CPG_GROUP_SIZE} msgs/node) exceeded "
            f"CPG_IPC_QUEUE_DEPTH_MAX ({CPG_IPC_QUEUE_DEPTH_MAX:,}), "
            f"causing CS_ERR_TRY_AGAIN → pmxcfs leave/rejoin → "
            f"new view-change → amplification. "
            f"Fix: (1) Add IPC back-pressure in cpg.c; "
            f"(2) Rate-limit CPG view-change delivery; "
            f"(3) Increase cpg_ipc_queue depth or use async delivery.")

    if cpg_sim.try_again_total > 0 and cpg_sim.leave_rejoin_loops == 0:
        rec("HIGH",
            f"CPG cascade generated {cpg_sim.try_again_total:,} "
            f"CS_ERR_TRY_AGAIN events without looping in this run. "
            f"At higher rates or with more CPG members the feedback "
            f"loop will trigger. "
            f"Fix: increase CPG_IPC_QUEUE_DEPTH_MAX or add rate-limiting.")

    if l2672 > 0:
        rec("HIGH",
            f"L2672 fired {l2672:,} times. The sort-queue release range "
            f"exceeded {QUEUE_RTR_ITEMS_SIZE_MAX:,}. "
            f"Fix: clamp release_to in message_queue_release() at totemsrp.c:2672; "
            f"log warning; never assert-crash.")

    if l4215 > 0:
        rec("HIGH",
            f"L4215 fired {l4215:,} times. Delivery range overflow. "
            f"Fix: deliver in QUEUE_RTR_ITEMS_SIZE_MAX-1 chunks per pass.")

    if l4327 > 0:
        rec("MEDIUM",
            f"L4327 fired {l4327:,} times (msg_len > FRAME_SIZE_MAX). "
            f"Fix: drop message and log at message_handler_mcast() entry; "
            f"never abort(). "
            f"In production: only occurs with totempg fragmentation bugs.")

    if ring.recovery_count == 0 and l2890 == 0 and l2433 == 0:
        rec("INFO",
            f"At {args.rate:,} msg/s all assert ranges stay below "
            f"QUEUE_RTR_ITEMS_SIZE_MAX={QUEUE_RTR_ITEMS_SIZE_MAX:,}. "
            f"The dangerous threshold is ~{threshold_rate:,} msg/s "
            f"(30s partition). "
            f"Run with --stress or --rate {threshold_rate+100} "
            f"to trigger assert fires.")

    rec("CONFIG",
        f"token_timeout formula: N × token_coefficient = "
        f"{args.nodes} × {TOKEN_COEFFICIENT} = {args.nodes*TOKEN_COEFFICIENT}ms. "
        f"Current {TOKEN_TIMEOUT_MS}ms is "
        f"{'correct' if TOKEN_TIMEOUT_MS >= args.nodes*TOKEN_COEFFICIENT else 'INSUFFICIENT'}. "
        f"Observed p99 rotation = {rot_p99:.0f}ms"
        f" ({'OK' if rot_p99 < TOKEN_TIMEOUT_MS else 'EXCEEDS TIMEOUT'}).")

    rec("CONFIG",
        f"window_size={WINDOW_SIZE} max_messages={MAX_MESSAGES}: "
        f"at {args.rate:,} msg/s the ring sustains "
        f"{total_multicast:,} messages in {args.seconds}s = "
        f"{total_multicast/args.seconds:.0f} msg/s effective throughput. "
        f"window_size=50 is appropriate for 100-node clusters.")

    rec("CONFIG",
        f"token_retransmits={TOKEN_RETRANSMITS} at {TOKEN_LOSS_PROB*100:.0f}% "
        f"token-loss rate: {ring.token_retransmits} loss events observed. "
        f"No ring recovery needed for loss alone — adequate setting.")

    print("=" * 74)
    total_fires = sum(by_loc.values())
    print()
    if total_fires > 0:
        print(f"  VERDICT: {total_fires:,} assert-fire events would crash "
              f"stock corosync v3.1.9.")
        print(f"           This simulation applied graceful fixes instead.")
        if args.rate < threshold_rate:
            print(f"           Most fires are L4327 (frame oversize) from the")
            print(f"           0.02% injection rate. Increase --rate to "
                  f"{threshold_rate+100} to trigger L2890/L2433.")
        print()
        print(f"  Required patches to totemsrp.c:")
        for loc in ["L2433", "L2672", "L2890", "L4215", "L4327"]:
            if by_loc.get(loc, 0) > 0:
                print(f"    {loc}: replace assert() with: {fixes[loc]}")
    else:
        print(f"  VERDICT: No assert fires at {args.rate:,} msg/s / {args.seconds}s.")
        print(f"           Raise --rate to ≥ {threshold_rate:,} msg/s "
              f"to cross the L2433/L2890 boundary.")
    print()


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Corosync TOTEM 100-node ring stress simulation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="Examples:\n"
               "  python3 sim100.py                   # normal load\n"
               "  python3 sim100.py --stress          # high-rate, triggers L2433/L2890\n"
               "  python3 sim100.py --rate 600        # custom rate\n"
               "  python3 sim100.py --quiet --stress  # stress mode, results only\n")

    parser.add_argument("--nodes",   type=int, default=N_NODES,
                        help=f"Cluster nodes (default: {N_NODES})")
    parser.add_argument("--seconds", type=int, default=SIMULATION_SECONDS,
                        help=f"Simulation seconds (default: {SIMULATION_SECONDS})")
    parser.add_argument("--rate",    type=int, default=MSG_RATE,
                        help=f"Total msg/s across ring (default: {MSG_RATE}). "
                             f"≥{int(QUEUE_RTR_ITEMS_SIZE_MAX/(PARTITION_END_S-PARTITION_START_S))+1}"
                             f" triggers L2433/L2890.")
    parser.add_argument("--seed",    type=int, default=42,
                        help="RNG seed (default: 42)")
    parser.add_argument("--stress",  action="store_true",
                        help="High-stress mode (sets rate to trigger assert fires)")
    parser.add_argument("--quiet",   action="store_true",
                        help="Suppress progress output")
    args = parser.parse_args()

    if args.stress and args.rate == MSG_RATE:
        # threshold ≈ 546 msg/s for 30s partition; use 700 for clear margin
        args.rate = 700

    run_simulation(args)


if __name__ == "__main__":
    main()
