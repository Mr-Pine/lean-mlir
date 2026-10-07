import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionSchedulePrefix

/-! Exact scratch store, counter update, and exit test of the imported bb5. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure PairStoreReady (E : Env program.Γ) (scratch : Pointer)
    (r j : Nat) (lo hi : Word) : Prop where
  scratchPtr : E.read (%81) = .value scratch
  slot : E.read (%174) = .value (BitVec.ofNat 64 j)
  index : E.read (%173) = .value (BitVec.ofNat 64 (r+16))
  nextSlot : E.read (%191) = .value (BitVec.ofNat 64 (j+1))
  words : E.read (%217) = pairVec lo hi
  two : E.read (%42) = .value 2#64
  eight : E.read (%3) = .value 8#64

def pairStoreEnv (E : Env program.Γ) (scratch : Pointer) (r j : Nat) : Env program.Γ :=
  E[%269 := .value (scratch.add (BitVec.ofNat 64 (16*j))),
    %270 := .value (BitVec.ofNat 64 (r+18)),
    %271 := .value (BitVec.ofBool (j+1=8))]

def pairStoreState (mem : GlobalState) (scratch : Pointer) (j : Nat)
    (lo hi : Word) : GlobalState :=
  { mem with mem := pairScratchStore mem.mem scratch j lo hi }

private theorem pair_store_gep (j : Nat) (hj : j < 8) :
    Operation.gepInboundsIndex 16 (.value (BitVec.ofNat 64 j)) =
      .value (Int.ofNat (16*j)) := by
  interval_cases j <;> decide

private theorem pair_store_eq8 (j : Nat) (hj : j < 8) :
    Operation.icmp .eq (.value (BitVec.ofNat 64 (j+1))) (.value 8#64) =
      .value (BitVec.ofBool (j+1=8)) := by
  interval_cases j <;> decide

/-- Offsets 78 through 81 are the only writes to scratch in one bb5 pair. -/
theorem pair_store_body (E : Env program.Γ) (mem : GlobalState)
    (scratch : Pointer) (r j : Nat) (lo hi : Word)
    (hj : j < 8) (h : PairStoreReady E scratch r j lo hi)
    (hm : SmallRange mem.mem scratch 128) :
    List.foldlM Instr.run E ((program.bb5.body.drop 78).take 4) mem =
      .value (pairStoreEnv E scratch r j, pairStoreState mem scratch j lo hi) := by
  have hidx := pair_store_gep j hj
  have hgep := hm.gep (k := 16*j) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hfit := hm.fits_add (k := 16*j) (count := 16) (by omega)
  have heq := pair_store_eq8 j hj
  have hadd : Operation.add {} (.value (BitVec.ofNat 64 (r+16))) (.value 2#64) =
      .value (BitVec.ofNat 64 (r+18)) := by
    simp only [Operation.add, PoisonOr.value_bind, Bool.false_eq_true, false_and,
      ite_false, pure]
    congr 1
    rw [← BitVec.ofNat_add]
  rcases h with ⟨hp, hj174, hr173, hj191, hw, h2, h8⟩
  simp [program.bb5, List.foldlM_cons, List.foldlM_nil, Instr.run,
    pairStoreEnv, pairStoreState, pairScratchStore,
    hp, hj174, hr173, hj191, hw, h2, h8, hidx, hgep, hfit, heq, hadd,
    pairVec_flatten, GepIndex.inboundsOffset, Operation.store, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.SHA512.Execution.Avx2
