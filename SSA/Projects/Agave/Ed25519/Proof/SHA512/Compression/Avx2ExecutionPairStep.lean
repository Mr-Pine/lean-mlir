import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairBody
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairMemory

/-! One exact imported two-round iteration, specialized to the FIPS schedule. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

def pairSpecEnv (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (block : Bytes) (s : Spec.State) : Env program.Γ :=
  pairBodyEnv E scratch k r j (specWindow block r) s
    (constants.toList.getD (r+16) 0) (constants.toList.getD (r+17) 0)
    (scheduleKW (schedule block) r) (scheduleKW (schedule block) (r+1))

def pairSpecMem (mem : GlobalState) (scratch : Pointer) (r j : Nat)
    (block : Bytes) : GlobalState :=
  pairStoreState mem scratch j (scheduleKW (schedule block) (r+16))
    (scheduleKW (schedule block) (r+17))

theorem pair_rounds_eq (s : Spec.State) (words : List Word) (r : Nat) :
    pairSecondState (tailRound s (scheduleKW words r)) (scheduleKW words (r+1)) =
      roundsFrom s words r 2 := by
  simp only [scheduleKW, pairSecondState_eq_round, tailRound_eq, roundsFrom,
    Nat.add_zero]

theorem pairBodyState_spec (mem : GlobalState) (scratch : Pointer) (r j : Nat)
    (block : Bytes) (hr : r+1<64) :
    pairBodyState mem scratch j (specWindow block r)
      (constants.toList.getD (r+16) 0) (constants.toList.getD (r+17) 0) =
        pairSpecMem mem scratch r j block := by
  simp only [pairBodyState, avxWindowPair_spec block r hr, pairSpecMem,
    scheduleKW, BitVec.add_comm]

/-- Concrete constants and the mixed scratch invariant discharge all memory reads. -/
theorem pair_body_spec (E : Env program.Γ) (mem : GlobalState)
    (scratch k : Pointer) (b j : Nat) (block : Bytes) (s : Spec.State)
    (hb : b<4) (hj : j<8)
    (h : PairReady E scratch k (16*b+2*j) j (specWindow block (16*b+2*j)) s)
    (hs : PairScratch mem.mem scratch (schedule block) b j)
    (hk : PairConstants mem.mem k) :
    List.foldlM Instr.run E program.bb5.body mem =
      .value (pairSpecEnv E scratch k (16*b+2*j) j block s,
        pairSpecMem mem scratch (16*b+2*j) j block) := by
  have hr : 16*b+2*j+1<64 := by omega
  have hh := pair_body E mem scratch k (16*b+2*j) j (specWindow block (16*b+2*j)) s
    (constants.toList.getD (16*b+2*j+16) 0) (constants.toList.getD (16*b+2*j+17) 0)
    (scheduleKW (schedule block) (16*b+2*j)) (scheduleKW (schedule block) (16*b+2*j+1))
    hr hj h hs.live hk.live (hk.pairs _ hr) (hs.read_pair hj).1 (hs.read_pair hj).2
  rw [pairBodyState_spec _ _ _ _ _ hr] at hh
  exact hh

theorem pair_spec_backedge (E : Env program.Γ) (mem : GlobalState)
    (scratch k : Pointer) (b j : Nat) (block : Bytes) (s : Spec.State)
    (hb : b<4) (hj : j<7)
    (h : PairReady E scratch k (16*b+2*j) j (specWindow block (16*b+2*j)) s)
    (hs : PairScratch mem.mem scratch (schedule block) b j)
    (hk : PairConstants mem.mem k) :
    program.bb5.run program.blockParams E mem =
      .value ((pairNextEnv (pairSpecEnv E scratch k (16*b+2*j) j block s), .inr 5),
        pairSpecMem mem scratch (16*b+2*j) j block) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    pair_body_spec E mem scratch k b j block s hb (by omega) h hs hk, PoisonOr.value_bind]
  apply pair_terminator_backedge
  simp only [pairSpecEnv, pairBodyEnv, pairStoreEnv, mlir_env,
    show ¬j+1=8 by omega, decide_false, BitVec.ofBool_false]
  rfl

theorem pair_spec_exit (E : Env program.Γ) (mem : GlobalState)
    (scratch k : Pointer) (b : Nat) (block : Bytes) (s : Spec.State)
    (hb : b<4)
    (h : PairReady E scratch k (16*b+2*7) 7 (specWindow block (16*b+2*7)) s)
    (hs : PairScratch mem.mem scratch (schedule block) b 7)
    (hk : PairConstants mem.mem k) :
    program.bb5.run program.blockParams E mem =
      .value ((pairSpecEnv E scratch k (16*b+2*7) 7 block s, .inr 3),
        pairSpecMem mem scratch (16*b+2*7) 7 block) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    pair_body_spec E mem scratch k b 7 block s hb (by decide) h hs hk, PoisonOr.value_bind]
  apply pair_terminator_exit
  simp [pairSpecEnv, pairBodyEnv, pairStoreEnv, mlir_env]

theorem pairSpecEnv_final_ready (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (block : Bytes) (s : Spec.State)
    (h : PairReady E scratch k r j (specWindow block r) s) :
    PairSecondFinalReady (pairSpecEnv E scratch k r j block s)
      (roundsFrom s (schedule block) r 2) := by
  have hf := pairBodyEnv_final_ready E scratch k r j (specWindow block r) s
    (constants.toList.getD (r+16) 0) (constants.toList.getD (r+17) 0)
    (scheduleKW (schedule block) r) (scheduleKW (schedule block) (r+1)) h
  rw [pair_rounds_eq] at hf
  exact hf

theorem pairSpecMem_scratch (mem : GlobalState) (scratch : Pointer) (b j : Nat)
    (block : Bytes) (hj : j<8) (hs : PairScratch mem.mem scratch (schedule block) b j) :
    PairScratch (pairSpecMem mem scratch (16*b+2*j) j block).mem scratch
      (schedule block) b (j+1) := by
  have h0 : 16*b+2*j+16 = 16*(b+1)+2*j := by omega
  have h1 : 16*b+2*j+17 = 16*(b+1)+2*j+1 := by omega
  simpa only [pairSpecMem, pairStoreState, h0, h1] using hs.advance hj

theorem pairSpecMem_constants (mem : GlobalState) (scratch k : Pointer) (r j : Nat)
    (block : Bytes) (hj : j<8) (hs : SmallRange mem.mem scratch 128)
    (hk : PairConstants mem.mem k)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120)) :
    PairConstants (pairSpecMem mem scratch r j block).mem k :=
  hk.store hs j hj _ _ hd

end Agave.Ed25519.SHA512.Execution.Avx2
