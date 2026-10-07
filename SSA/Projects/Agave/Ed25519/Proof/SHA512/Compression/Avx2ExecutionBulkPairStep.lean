import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairReady
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairMemoryFrame
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairStep

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def bulkPairSpecEnv (E : Env program.Γ) (scratch cache k : Pointer) (b j : Nat)
    (block₀ block₁ : Bytes) (s : Spec.State) : Env program.Γ :=
  let r := 16*b+2*j
  bulkPairBodyEnv E scratch (cache.add (BitVec.ofNat 64 (128*(b+1)))) k r j
    (specWindow block₀ r) (specWindow block₁ r) s
    (constants.toList.getD (r+16) 0) (constants.toList.getD (r+17) 0)
    (scheduleKW (schedule block₀) r) (scheduleKW (schedule block₀) (r+1))

abbrev BulkPairSpecReady (E : Env program.Γ) (scratch cache k : Pointer) (b j : Nat)
    (block₀ block₁ : Bytes) (s : Spec.State) : Prop :=
  BulkPairReady E scratch (cache.add (BitVec.ofNat 64 (128*(b+1)))) k (16*b+2*j) j
    (specWindow block₀ (16*b+2*j)) (specWindow block₁ (16*b+2*j)) s

theorem bulkPairBodyState_spec (mem : GlobalState) (scratch cache : Pointer)
    (b j : Nat) (block₀ block₁ : Bytes) (hr : 16*b+2*j+1<64) :
    bulkPairBodyState mem scratch (cache.add (BitVec.ofNat 64 (128*(b+1)))) j
      (specWindow block₀ (16*b+2*j)) (specWindow block₁ (16*b+2*j))
      (constants.toList.getD (16*b+2*j+16) 0) (constants.toList.getD (16*b+2*j+17) 0) =
        bulkPairSpecMem mem scratch cache b j (schedule block₀) (schedule block₁) := by
  have h0 : 16*b+2*j+16=16*(b+1)+2*j := by omega
  have h1 : 16*b+2*j+17=16*(b+1)+2*j+1 := by omega
  simp only [bulkPairBodyState, bulkPairSpecMem,
    avxWindowPair_spec block₀ (16*b+2*j) hr, avxWindowPair_spec block₁ (16*b+2*j) hr,
    scheduleKW, BitVec.add_comm, h0, h1]

theorem bulk_pair_body_spec (E : Env program.Γ) (mem : GlobalState)
    (scratch cache k : Pointer) (b j : Nat) (block₀ block₁ : Bytes) (s : Spec.State)
    (hb : b<4) (hj : j<8) (h : BulkPairSpecReady E scratch cache k b j block₀ block₁ s)
    (hs : PairScratch mem.mem scratch (schedule block₀) b j)
    (hc : BulkCachePrefix mem.mem cache (schedule block₁) (16*(b+1)+2*j))
    (hk : PairConstants mem.mem k) :
    List.foldlM Instr.run E program.bb12.body mem =
      .value (bulkPairSpecEnv E scratch cache k b j block₀ block₁ s,
        bulkPairSpecMem mem scratch cache b j (schedule block₀) (schedule block₁)) := by
  have hr : 16*b+2*j+1<64 := by omega
  have hh := bulk_pair_body E mem scratch (cache.add (BitVec.ofNat 64 (128*(b+1))))
    k (16*b+2*j) j (specWindow block₀ (16*b+2*j)) (specWindow block₁ (16*b+2*j)) s
    (constants.toList.getD (16*b+2*j+16) 0) (constants.toList.getD (16*b+2*j+17) 0)
    (scheduleKW (schedule block₀) (16*b+2*j)) (scheduleKW (schedule block₀) (16*b+2*j+1))
    hr hj h hs.live (bulk_cache_group_live hc.live (b+1) (by omega))
    hk.live (hk.pairs _ hr) (hs.read_pair hj).1 (hs.read_pair hj).2
  rw [bulkPairBodyState_spec _ _ _ _ _ _ _ hr] at hh
  exact hh

theorem bulk_pair_spec_backedge (E : Env program.Γ) (mem : GlobalState)
    (scratch cache k : Pointer) (b j : Nat) (block₀ block₁ : Bytes) (s : Spec.State)
    (hb : b<4) (hj : j<7) (h : BulkPairSpecReady E scratch cache k b j block₀ block₁ s)
    (hs : PairScratch mem.mem scratch (schedule block₀) b j)
    (hc : BulkCachePrefix mem.mem cache (schedule block₁) (16*(b+1)+2*j))
    (hk : PairConstants mem.mem k) :
    program.bb12.run program.blockParams E mem =
      .value ((bulkPairNextEnv (bulkPairSpecEnv E scratch cache k b j block₀ block₁ s), .inr 12),
        bulkPairSpecMem mem scratch cache b j (schedule block₀) (schedule block₁)) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulk_pair_body_spec E mem scratch cache k b j block₀ block₁ s hb (by omega) h hs hc hk,
    PoisonOr.value_bind]
  apply bulk_pair_terminator_backedge
  simp only [bulkPairSpecEnv, bulkPairBodyEnv, bulkPairStoreEnv, mlir_env,
    show ¬j+1=8 by omega, decide_false, BitVec.ofBool_false]
  rfl

theorem bulk_pair_spec_exit (E : Env program.Γ) (mem : GlobalState)
    (scratch cache k : Pointer) (b : Nat) (block₀ block₁ : Bytes) (s : Spec.State)
    (hb : b<4) (h : BulkPairSpecReady E scratch cache k b 7 block₀ block₁ s)
    (hs : PairScratch mem.mem scratch (schedule block₀) b 7)
    (hc : BulkCachePrefix mem.mem cache (schedule block₁) (16*(b+1)+2*7))
    (hk : PairConstants mem.mem k) :
    program.bb12.run program.blockParams E mem =
      .value ((bulkPairSpecEnv E scratch cache k b 7 block₀ block₁ s, .inr 10),
        bulkPairSpecMem mem scratch cache b 7 (schedule block₀) (schedule block₁)) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulk_pair_body_spec E mem scratch cache k b 7 block₀ block₁ s hb (by decide) h hs hc hk,
    PoisonOr.value_bind]
  apply bulk_pair_terminator_exit
  simp [bulkPairSpecEnv, bulkPairBodyEnv, bulkPairStoreEnv, mlir_env]

theorem bulkPairSpecEnv_next_ready (E : Env program.Γ) (scratch cache k : Pointer)
    (b j : Nat) (block₀ block₁ : Bytes) (s : Spec.State) (hr : 16*b+2*j+1<64)
    (h : BulkPairSpecReady E scratch cache k b j block₀ block₁ s) :
    BulkPairSpecReady (bulkPairNextEnv (bulkPairSpecEnv E scratch cache k b j block₀ block₁ s))
      scratch cache k b (j+1) block₀ block₁ (roundsFrom s (schedule block₀) (16*b+2*j) 2) := by
  have hh := bulkPairBodyEnv_next_ready E scratch (cache.add (BitVec.ofNat 64 (128*(b+1))))
    k (16*b+2*j) j (specWindow block₀ (16*b+2*j)) (specWindow block₁ (16*b+2*j)) s
    (constants.toList.getD (16*b+2*j+16) 0) (constants.toList.getD (16*b+2*j+17) 0)
    (scheduleKW (schedule block₀) (16*b+2*j)) (scheduleKW (schedule block₀) (16*b+2*j+1)) h
  rw [pair_rounds_eq, avxWindowStep_spec block₀ (16*b+2*j) hr,
    avxWindowStep_spec block₁ (16*b+2*j) hr] at hh
  simpa only [bulkPairSpecEnv, BulkPairSpecReady,
    show 16*b+2*j+2=16*b+2*(j+1) by omega] using hh

theorem bulkPairSpecEnv_frame (E : Env program.Γ) (scratch cache k : Pointer)
    (b j : Nat) (block₀ block₁ : Bytes) (s : Spec.State) :
    RegFrame 488 572 E (bulkPairSpecEnv E scratch cache k b j block₀ block₁ s) :=
  bulkPairBodyEnv_frame _ _ _ _ _ _ _ _ _ _ _ _ _

theorem bulkPairSpecNext_frame (E : Env program.Γ) (scratch cache k : Pointer)
    (b j : Nat) (block₀ block₁ : Bytes) (s : Spec.State) :
    RegFrame 470 572 E (bulkPairNextEnv (bulkPairSpecEnv E scratch cache k b j block₀ block₁ s)) :=
  ((bulkPairSpecEnv_frame _ _ _ _ _ _ _ _ _).enlarge (by decide) (by decide)).trans
    ((bulkPairNextEnv_frame _).enlarge (by decide) (by decide))

end Agave.Ed25519.SHA512.Execution.Avx2
