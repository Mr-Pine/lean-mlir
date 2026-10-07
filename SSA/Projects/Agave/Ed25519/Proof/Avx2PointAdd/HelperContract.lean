import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Refinement
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionRefinement

/-! The concrete multiplication helper boundary for the cached-add pipeline.
The theorem below executes the unchanged imported field helper and reads its
actual output memory. Its point bounds are the invariant preserved by cached
addition. It does not assume a field-correctness relation for a helper. -/
namespace Agave.Ed25519.Avx2PointAdd.Execution
open LeanMLIR.RIR Avx2FieldMul PointArithmetic
open Avx2FieldMul.Execution
open Reduce64.Execution (SmallRange outputWord)

/-- Exact three-pointer ABI used by the multiplication helper. -/
def mulArgs (r a b : Pointer) : Vals [.ptr, .ptr, .ptr] :=
  .cons (.value r) (.cons (.value a) (.cons (.value b) .nil))

/-- Exact byte contract, independent of the square helper. It is definitionally
identical to the multiplication contract used by the double-base caller. -/
def MulContract (call : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (r a b : Pointer) (s : GlobalState), s.WF →
    SmallRange s.mem r 160 → SmallRange s.mem a 160 → SmallRange s.mem b 160 →
    call (mulArgs r a b) s = .value (.nil, {s with mem := (Reduce64.Execution.storeOutputs s.mem r
      (rawColumns4 (readBlocks s.mem a) (readBlocks s.mem b)))})

theorem imported_mul_contract : MulContract Avx2FieldMul.program.call := by
  intro r a b s hwf hr ha hb
  exact Avx2FieldMul.Execution.kernel_call_words r a b s hwf hr ha hb

/-- Logical A/B/C/D coordinates in the compiler's packed 160-byte object. -/
def readPoint (m : MemoryState) (p : Pointer) : Point :=
  let limbs := inputNat (readBlocks m p)
  ⟨limbs 0, limbs 1, limbs 2, limbs 3⟩

theorem inputNat_outputWord (m : MemoryState) (p : Pointer)
    (lane : Fin 4) (limb : Fin 10) :
    inputNat (readBlocks m p) lane limb = (outputWord m p limb lane).toNat := by
  exact inputNat_readBlocks_eq_outputWord m p lane limb

theorem pointWide_lanes {m : MemoryState} {p : Pointer} (h : pointWide (readPoint m p))
    (lane : Fin 4) : wide (inputNat (readBlocks m p) lane) := by
  fin_cases lane
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-- The actual callee restores the reduced point invariant and computes the
lane-wise field product. All input words are read before the output stores,
so no extra non-aliasing assumption is needed. -/
theorem multiply_call (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hb : SmallRange s.mem b 160)
    (hA : pointWide (readPoint s.mem a)) (hB : pointWide (readPoint s.mem b)) :
    ∃ s' : GlobalState,
      Avx2FieldMul.program.call
        (Avx2FieldMul.program.args (.value r) (.value a) (.value b)) s =
        .value (.nil, s') ∧
      readPoint s'.mem r = multiply (readPoint s.mem a) (readPoint s.mem b) ∧
      pointReduced (readPoint s'.mem r) ∧
      pointValue (readPoint s'.mem r) =
        laneMul (pointValue (readPoint s.mem a)) (pointValue (readPoint s.mem b)) := by
  obtain ⟨s', hcall, hwords, _⟩ := Avx2FieldMul.Execution.kernel_correct r a b s hwf
    hr ha hb (fun lane => wide_left (pointWide_lanes hA lane))
      (fun lane => wide_right (pointWide_lanes hB lane))
  have hpoint : readPoint s'.mem r = multiply (readPoint s.mem a) (readPoint s.mem b) := by
    ext limb
    all_goals simp only [readPoint, multiply, inputNat_outputWord]
    all_goals simpa only [inputNat_outputWord] using hwords _ limb
  refine ⟨s', hcall, hpoint, ?_, ?_⟩
  · rw [hpoint]
    exact multiply_reduced hA hB
  · rw [hpoint]
    exact pointValue_multiply _ _

end Agave.Ed25519.Avx2PointAdd.Execution
