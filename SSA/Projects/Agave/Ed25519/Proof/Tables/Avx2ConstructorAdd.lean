import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAddExecution

/-! Actual positive-add execution and the interface consumed by the table loop. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Add
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
attribute [local implicit_reducible] Ty.width

theorem body_tail_frame (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 806 kernel.Γ.n (bodyEnv1 E q table index P C) (bodyEnv9 E q table index P C) := by
  have f2 := (prepare_frame (bodyEnv1 E q table index P C) (packPoint P)).weaken (lo' := 806) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f3 := (load_product4_frame (bodyEnv2 E q table index P C) (packPoint (productPoint false P C))).weaken (lo' := 806) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f4 := (abdc_frame (bodyEnv3 E q table index P C)).weaken (lo' := 806) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f5 := (load_product1_frame (bodyEnv4 E q table index P C) (packPoint (productPoint false P C))).weaken (lo' := 806) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f6 := (difference_frame (bodyEnv5 E q table index P C)).weaken (lo' := 806) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f7 := (adda_frame (bodyEnv6 E q table index P C)).weaken (lo' := 806) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f8 := (cbcb_frame (bodyEnv7 E q table index P C)).weaken (lo' := 806) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f9 := (load_result_frame (bodyEnv8 E q table index P C) (packPoint (resultPoint false P C))).weaken (lo' := 806) (hi' := kernel.Γ.n) (by decide) (by decide)
  exact ((((((((RegisterFrame.refl 806 kernel.Γ.n (bodyEnv1 E q table index P C)).trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9


theorem body_cursor (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (bodyEnv9 E q table index P C).read (%804) = .value (BitVec.ofNat 64 (index.val+1)) ∧
    (bodyEnv9 E q table index P C).read (%805) = .value (tableRow table index) := by
  have hf := body_tail_frame E q table index P C
  constructor
  · rw [hf.read (%804) (by decide)]
    simp [bodyEnv1, rowEnv, mlir_env]
  · rw [hf.read (%805) (by decide)]
    simp [bodyEnv1, rowEnv, mlir_env]

theorem body_packed (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (bodyEnv9 E q table index P C).read (%876) = Ty.wrap (packPoint (add P C) 0) ∧
    (bodyEnv9 E q table index P C).read (%877) = Ty.wrap (packPoint (add P C) 1) ∧
    (bodyEnv9 E q table index P C).read (%878) = Ty.wrap (packPoint (add P C) 2) ∧
    (bodyEnv9 E q table index P C).read (%879) = Ty.wrap (packPoint (add P C) 3) ∧
    (bodyEnv9 E q table index P C).read (%880) = Ty.wrap (packPoint (add P C) 4) := by
  simpa only [resultPoint_eq, Bool.false_eq_true, ↓reduceIte] using body_output E q table index P C

/-- The square primitive is unused by bb2; its multiplication primitive is the
checked, unchanged imported field helper. -/
noncomputable def actual (square : Vals [.ptr, .ptr] → EffectM (Vals [])) : Primitives where
  call0 := square
  call1 := Avx2FieldMul.program.call

/-- Exact instructions [0,105), including the flagged increment, inbounds table
GEP, two memcpy instructions, two actual multiplications, and all vector loads,
stores and arithmetic. No successful helper or point-add execution is assumed. -/
theorem body_actual (square : Vals [.ptr, .ptr] → EffectM (Vals []))
    (E : ⟪kernel.Γ⟫) (s : GlobalState) (q : Scratch) (fixed table : Pointer)
    (index : Fin 64) (bytes : Nat) (P C : Point)
    (hreg : Input E q fixed table index)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hfixed : Reduce64.Execution.SmallRange s.mem fixed 160)
    (hfixedRead : Avx2FieldMul.Execution.readBlocks s.mem fixed = packPoint P)
    (hdisjoint : q.prepared.id ≠ fixed.id)
    (hP : pointReduced P) (hC : pointReduced C) :
    (kernel.bb2 (actual square)).runBodyFrom E 0 s =
      (kernel.bb2 (actual square)).runBodyFrom (bodyEnv9 E q table index P C) 105
        (resultState s q fixed P C) :=
  body_continue (actual square) E s q fixed table index bytes P C
    Avx2PointAdd.Execution.imported_mul_contract hreg hmem htable hindex hcache
    hfixed hfixedRead hdisjoint hP hC

end Agave.Ed25519.Tables.Avx2Constructor.Add

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.Add.body_actual,
      `Agave.Ed25519.Tables.Avx2Constructor.Add.body_packed,
      `Agave.Ed25519.Tables.Avx2Constructor.Add.body_cursor,
      `Agave.Ed25519.Tables.Avx2Constructor.Add.body_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.Add.resultState_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.Add.resultState_read] do
    let axioms ← collectAxioms endpoint
    for axiomName in axioms do
      unless axiomName ∈ [`propext, `Classical.choice, `Quot.sound] do
        throwError "nonstandard axiom {axiomName} in {endpoint}"
    logInfo m!"standard-three audit passed: {endpoint}"
