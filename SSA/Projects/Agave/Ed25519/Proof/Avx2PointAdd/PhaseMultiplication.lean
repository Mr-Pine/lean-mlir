import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseRepresentation
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.HelperContract

/-! The actual field-helper call boundary in the point pipeline.
The pre/post representation is the same eight-lane vector representation used
by CFGPrepare/CFGNegate/CFGDifference/CFGFactors. It therefore does not require
expanding a multiplication trace into either adjacent instruction phase. -/
namespace Agave.Ed25519.Avx2PointAdd.Phases
open LeanMLIR.RIR Avx2FieldMul.Execution Avx2PointAdd.Execution
open Reduce64.Execution (SmallRange)

def coordinate (P : Point) : Fin 4 → Avx2FieldMul.Limbs := ![P.X, P.Y, P.Z, P.T]

theorem pointWide_coordinate {P : Point} (hP : pointWide P) (lane : Fin 4) :
    wide (coordinate P lane) := by
  fin_cases lane
  · exact hP.1
  · exact hP.2.1
  · exact hP.2.2.1
  · exact hP.2.2.2

private theorem wide_word_toNat {a : Avx2FieldMul.Limbs} (ha : wide a) (i : Fin 10) :
    (word (a i)).toNat = a i := by
  have h := (wide_input_safety ha i).1
  exact Nat.mod_eq_of_lt (by omega)

/-- Decode the packed helper arguments without a narrowing assumption hidden
inside the representation relation. The wide caller invariant proves it. -/
theorem inputNat_packPoint {P : Point} (hP : pointWide P)
    (lane : Fin 4) (limb : Fin 10) :
    inputNat (packPoint P) lane limb = coordinate P lane limb := by
  fin_cases lane <;> fin_cases limb <;>
    simp [inputNat, unpackBlocks, packPoint, coordinate, evenIndex, oddIndex,
      wide_word_toNat hP.1, wide_word_toNat hP.2.1,
      wide_word_toNat hP.2.2.1, wide_word_toNat hP.2.2.2]

theorem readPoint_of_packed {P : Point} (hP : pointWide P)
    (m : MemoryState) (p : Pointer) (hread : readBlocks m p = packPoint P) :
    readPoint m p = P := by
  ext limb
  all_goals simp only [readPoint, hread, inputNat_packPoint hP]
  all_goals rfl

/-- Readback followed by repacking is lossless for arbitrary memory words.
This direction needs no limb bound: `ofNat .toNat` recovers each u32 exactly. -/
theorem packPoint_readPoint (m : MemoryState) (p : Pointer) :
    packPoint (readPoint m p) = readBlocks m p := by
  funext k
  apply Vector.ext
  intro i hi
  fin_cases k <;> interval_cases i <;>
    simp [packPoint, readPoint, inputNat, unpackBlocks, evenIndex, oddIndex, word]

/-- Execute the unchanged imported multiplier between two point instruction
phases, obtaining packed output words and the restored reduced invariant. -/
theorem multiply_packed_call (r a b : Pointer) (s : GlobalState) (P Q : Point)
    (hwf : s.WF) (hr : SmallRange s.mem r 160)
    (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : readBlocks s.mem a = packPoint P)
    (hB : readBlocks s.mem b = packPoint Q) :
    ∃ s' : GlobalState,
      Avx2FieldMul.program.call
        (Avx2FieldMul.program.args (.value r) (.value a) (.value b)) s =
          .value (.nil, s') ∧
      readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (readPoint s'.mem r) = laneMul (pointValue P) (pointValue Q) := by
  have hp := readPoint_of_packed hP s.mem a hA
  have hq := readPoint_of_packed hQ s.mem b hB
  obtain ⟨s', hcall, hpoint, hred, hvalue⟩ := multiply_call r a b s hwf hr ha hb
    (hp.symm ▸ hP) (hq.symm ▸ hQ)
  rw [hp, hq] at hpoint hvalue
  refine ⟨s', hcall, ?_, multiply_reduced hP hQ, hvalue⟩
  rw [← packPoint_readPoint, hpoint]

/-- A CFG primitive satisfying the already-proved exact byte contract inherits
the same packed field result. This uses no point-add or backend correctness
premise; `imported_mul_contract` supplies the actual helper implementation. -/
theorem multiply_packed_of_contract
    (call : Vals [.ptr, .ptr, .ptr] → EffectM (Vals []))
    (hcall : Avx2PointAdd.Execution.MulContract call)
    (r a b : Pointer) (s : GlobalState) (P Q : Point)
    (hwf : s.WF) (hr : SmallRange s.mem r 160)
    (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : readBlocks s.mem a = packPoint P)
    (hB : readBlocks s.mem b = packPoint Q) :
    ∃ s' : GlobalState,
      call (Avx2PointAdd.Execution.mulArgs r a b) s = .value (.nil, s') ∧
      readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (readPoint s'.mem r) = laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hactual, hwords, hred, hvalue⟩ :=
    multiply_packed_call r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hwords, hred, hvalue⟩
  exact (hcall r a b s hwf hr ha hb).trans
    ((Avx2FieldMul.Execution.kernel_call_words r a b s hwf hr ha hb).symm.trans hactual)

/-- The call's entire state change is exactly the five packed product stores.
This form exposes the memory frame required by the next point phase: all
allocation witnesses and reads from distinct objects follow from PhaseMemory.
No field computation is unfolded into the caller's execution proof. -/
theorem multiply_packed_state
    (call : Vals [.ptr, .ptr, .ptr] → EffectM (Vals []))
    (hcall : Avx2PointAdd.Execution.MulContract call)
    (r a b : Pointer) (s : GlobalState) (P Q : Point)
    (hwf : s.WF) (hr : SmallRange s.mem r 160)
    (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : readBlocks s.mem a = packPoint P)
    (hB : readBlocks s.mem b = packPoint Q) :
    call (Avx2PointAdd.Execution.mulArgs r a b) s =
      .value (.nil, {s with mem := storeBlocks s.mem r (packPoint (multiply P Q))}) := by
  obtain ⟨s', hresult, hwords, _, _⟩ :=
    multiply_packed_of_contract call hcall r a b s P Q hwf hr ha hb hP hQ hA hB
  have hs' : s' = {s with mem := (Reduce64.Execution.storeOutputs s.mem r
      (rawColumns4 (readBlocks s.mem a) (readBlocks s.mem b)))} := by
    exact congrArg Prod.snd
      (PoisonOr.value_inj.mp (hresult.symm.trans (hcall r a b s hwf hr ha hb)))
  have hpacked : Reduce64.Execution.packedOutput
      (rawColumns4 (readBlocks s.mem a) (readBlocks s.mem b)) =
        packPoint (multiply P Q) := by
    rw [hs'] at hwords
    simpa only [readBlocks_storeOutputs s.mem r _ hr] using hwords
  rw [hcall r a b s hwf hr ha hb]
  change PoisonOr.value ((Vals.nil : Vals []), {s with mem := (storeBlocks s.mem r
      (Reduce64.Execution.packedOutput
        (rawColumns4 (readBlocks s.mem a) (readBlocks s.mem b))))}) = _
  rw [hpacked]

end Agave.Ed25519.Avx2PointAdd.Phases
