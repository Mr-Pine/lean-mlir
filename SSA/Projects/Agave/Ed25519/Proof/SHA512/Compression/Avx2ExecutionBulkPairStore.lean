import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairSchedule
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairStore


/-! Exact two stores at the end of bb12. The first pair updates the circular
first-block scratch; the second pair extends the second-block cache. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure BulkPairStoreReady (E : Env program.Γ) (scratch cacheGroup : Pointer)
    (r j : Nat) (lo hi lo' hi' : Word) : Prop where
  scratchPtr : E.read (%83) = .value scratch
  cachePtr : E.read (%469) = .value cacheGroup
  slot : E.read (%471) = .value (BitVec.ofNat 64 j)
  index : E.read (%470) = .value (BitVec.ofNat 64 (r+16))
  nextSlot : E.read (%488) = .value (BitVec.ofNat 64 (j+1))
  words : E.read (%515) = bulkVec lo hi lo' hi'
  two : E.read (%42) = .value 2#64
  eight : E.read (%3) = .value 8#64

def bulkPairStoreEnv (E : Env program.Γ) (scratch cacheGroup : Pointer)
    (r j : Nat) (lo hi lo' hi' : Word) : Env program.Γ :=
  E[%567 := pairVec lo hi,
    %568 := .value (scratch.add (BitVec.ofNat 64 (16*j))),
    %569 := pairVec lo' hi',
    %570 := .value (cacheGroup.add (BitVec.ofNat 64 (16*j))),
    %571 := .value (BitVec.ofNat 64 (r+18)),
    %572 := .value (BitVec.ofBool (j+1=8))]

def bulkPairStoreState (mem : GlobalState) (scratch cacheGroup : Pointer) (j : Nat)
    (lo hi lo' hi' : Word) : GlobalState :=
  pairStoreState (pairStoreState mem scratch j lo hi) cacheGroup j lo' hi'

private theorem bulk_pair_store_gep (j : Nat) (hj : j < 8) :
    Operation.gepInboundsIndex 16 (.value (BitVec.ofNat 64 j)) =
      .value (Int.ofNat (16*j)) := by
  interval_cases j <;> decide

private theorem bulk_pair_store_eq8 (j : Nat) (hj : j < 8) :
    Operation.icmp .eq (.value (BitVec.ofNat 64 (j+1))) (.value 8#64) =
      .value (BitVec.ofBool (j+1=8)) := by
  interval_cases j <;> decide


/-- Both actual stores are executed in source order. Ranges need not be
assumed disjoint merely to execute: disjointness belongs to semantic readback. -/
theorem bulk_pair_store_body (E : Env program.Γ) (mem : GlobalState)
    (scratch cacheGroup : Pointer) (r j : Nat) (lo hi lo' hi' : Word)
    (hj : j < 8) (h : BulkPairStoreReady E scratch cacheGroup r j lo hi lo' hi')
    (hm : SmallRange mem.mem scratch 128) (hc : SmallRange mem.mem cacheGroup 128) :
    List.foldlM Instr.run E ((program.bb12.body.drop 79).take 8) mem =
      .value (bulkPairStoreEnv E scratch cacheGroup r j lo hi lo' hi',
        bulkPairStoreState mem scratch cacheGroup j lo hi lo' hi') := by
  have hidx := bulk_pair_store_gep j hj
  have hgep := hm.gep (k := 16*j) (by omega)
  have hfit := hm.fits_add (k := 16*j) (count := 16) (by omega)
  have hc' := hc.storeAt (scratch.add (BitVec.ofNat 64 (16*j))) (hi ++ lo)
  have hcgep := hc'.gep (k := 16*j) (by omega)
  have hcfit := hc'.fits_add (k := 16*j) (count := 16) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep hcgep
  have heq := bulk_pair_store_eq8 j hj
  have hadd : Operation.add {} (.value (BitVec.ofNat 64 (r+16))) (.value 2#64) =
      .value (BitVec.ofNat 64 (r+18)) := by
    simp only [Operation.add, PoisonOr.value_bind, Bool.false_eq_true, false_and,
      ite_false, pure]
    congr 1
    rw [← BitVec.ofNat_add]
  rcases h with ⟨hp, hcp, hj471, hr470, hj488, hw, h2, h8⟩
  let E1 := E[%567 := pairVec lo hi]
  let E3 := E1[%568 := .value (scratch.add (BitVec.ofNat 64 (16*j)))]
  let M3 := pairStoreState mem scratch j lo hi
  let E4 := E3[%569 := pairVec lo' hi']
  let E6 := E4[%570 := .value (cacheGroup.add (BitVec.ofNat 64 (16*j)))]
  let M6 := pairStoreState M3 cacheGroup j lo' hi'
  have hl : List.foldlM Instr.run E ((program.bb12.body.drop 79).take 1) mem =
      .value (E1, mem) := by
    simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run, E1, hw,
      BinOp.compute, bulkVec, pairVec, Ty.wrap_vec,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]
  have hsl : List.foldlM Instr.run E1 ((program.bb12.body.drop 80).take 2) mem =
      .value (E3, M3) := by
    simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run,
      E1, E3, M3, hp, hj471, hidx, hgep, hfit, pairStoreState, pairScratchStore,
      pairVec_flatten, GepIndex.inboundsOffset, Operation.store,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
  have hh : List.foldlM Instr.run E3 ((program.bb12.body.drop 82).take 1) M3 =
      .value (E4, M3) := by
    simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run, E1, E3, E4, hw,
      BinOp.compute, bulkVec, pairVec, Ty.wrap_vec,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]
  have hsh : List.foldlM Instr.run E4 ((program.bb12.body.drop 83).take 2) M3 =
      .value (E6, M6) := by
    simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run,
      E1, E3, E4, E6, M3, M6, hcp, hj471, hidx, hcgep, hcfit,
      pairStoreState, pairScratchStore, pairVec_flatten, GepIndex.inboundsOffset, Operation.store,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
  have hlast : List.foldlM Instr.run E6 ((program.bb12.body.drop 85).take 2) M6 =
      .value (bulkPairStoreEnv E scratch cacheGroup r j lo hi lo' hi', M6) := by
    simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run,
      E1, E3, E4, E6, bulkPairStoreEnv, hr470, hj488, h2, h8, heq, hadd,
      BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]
  have hcut : (program.bb12.body.drop 79).take 8 =
      (program.bb12.body.drop 79).take 1 ++ (program.bb12.body.drop 80).take 2 ++
      (program.bb12.body.drop 82).take 1 ++ (program.bb12.body.drop 83).take 2 ++
      (program.bb12.body.drop 85).take 2 := by rfl
  rw [hcut, List.foldlM_append, List.foldlM_append, List.foldlM_append, List.foldlM_append]
  simp only [EffectM.bind_eq, hl, PoisonOr.value_bind, hsl, hh, hsh, hlast]
  rfl

theorem bulkPairStoreEnv_frame (E : Env program.Γ) (scratch cacheGroup : Pointer)
    (r j : Nat) (lo hi lo' hi' : Word) :
    RegFrame 567 572 E (bulkPairStoreEnv E scratch cacheGroup r j lo hi lo' hi') := by
  unfold bulkPairStoreEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

end Agave.Ed25519.SHA512.Execution.Avx2
