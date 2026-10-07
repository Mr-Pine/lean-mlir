import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.Algebra
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.PreparationPacking
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs

/-! Arithmetic refinement of the two explicit byte-level helper contracts in
AVX2 point doubling. The caller establishes that its preparation and mixing
instructions write the stated operands. These theorems derive readback and
arithmetic bounds from the contracts and the point invariant; they do not
claim that an imported helper implementation satisfies its contract. -/
namespace Agave.Ed25519.Avx2PointDouble.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange outputWord)
open DoubleBase.ExecutionAvx2 (SquareContract MulContract args2 args3)

/-- The ten coefficients of all four logical lanes in the five packed blocks. -/
def readCoordinates (m : MemoryState) (p : Pointer) : Coordinates :=
  blockCoordinates (Avx2FieldMul.Execution.readBlocks m p)

/-- The multiplication input reader and reduction output reader use the same
physical layout; no abstract point is substituted for the stored bytes. -/
theorem readCoordinates_eq_outputWord (m : MemoryState) (p : Pointer)
    (lane : Fin 4) (limb : Fin 10) :
    readCoordinates m p lane limb = (outputWord m p limb lane).toNat := by
  fin_cases lane <;> fin_cases limb <;>
    simp [readCoordinates, blockCoordinates,
      Avx2FieldMul.Execution.readBlocks, Avx2FieldMul.Execution.unpackBlocks,
      outputWord, Reduce64.Execution.physicalLane, Ty.extractVecElem_eq]

/-- The byte-level square contract, applied to X,Y,Z,X+Y, yields the square
stage and restores the reduced point invariant. The contract admits aliasing. -/
theorem square_call_correct
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (hcall : SquareContract call)
    (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (p : Coordinates) (hp : PointBound p)
    (hprepare : readCoordinates s.mem a = prepare p) :
    ∃ s' : GlobalState,
      call (args2 r a) s = .value (.nil, s') ∧
      readCoordinates s'.mem r = squareStage p ∧
      PointBound (readCoordinates s'.mem r) := by
  have hinput : ∀ lane, Avx2SquareNegateD.Bounded
      (Avx2SquareNegateD.Execution.inputNat
        (Avx2SquareNegateD.Execution.readBlocks s.mem a) lane) := by
    intro lane
    change Avx2SquareNegateD.Bounded (readCoordinates s.mem a lane)
    rw [hprepare]
    exact prepare_bounded hp lane
  let s' : GlobalState := {s with mem := (Reduce64.Execution.storeOutputs s.mem r
    (Avx2SquareNegateD.Execution.signedColumns4
      (Avx2SquareNegateD.Execution.readBlocks s.mem a)))}
  have hout : readCoordinates s'.mem r = squareStage p := by
    funext lane limb
    rw [readCoordinates_eq_outputWord]
    rw [Avx2SquareNegateD.Execution.outputWord_square s.mem r _ hr lane (hinput lane)]
    change Avx2SquareNegateD.output (readCoordinates s.mem a lane)
      (decide (lane = 3)) limb = squareStage p lane limb
    rw [hprepare]
    have hsign : decide (lane = 3) = (lane.val == 3) := by
      fin_cases lane <;> decide
    rw [hsign]
    rfl
  exact ⟨s', hcall r a s hwf hr ha, hout, hout.symm ▸ squareStage_bounded hp⟩

/-- A caller may supply the concrete five prepared blocks instead of proving
the logical-limb preparation equation separately. -/
theorem square_call_prepared
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (hcall : SquareContract call)
    (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (input : Blocks) (hp : PointBound (blockCoordinates input))
    (hprepare : Avx2FieldMul.Execution.readBlocks s.mem a = prepareBlocks input) :
    ∃ s' : GlobalState,
      call (args2 r a) s = .value (.nil, s') ∧
      readCoordinates s'.mem r = squareStage (blockCoordinates input) ∧
      PointBound (readCoordinates s'.mem r) := by
  apply square_call_correct call hcall r a s hwf hr ha (blockCoordinates input) hp
  change blockCoordinates (Avx2FieldMul.Execution.readBlocks s.mem a) = _
  rw [hprepare, prepareBlocks_coordinates input hp]

/-- The byte-level multiplication contract on the mixed operands yields the
doubling result in memory, its field formula, and the next iteration's bound. -/
theorem multiply_call_correct
    (call : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])) (hcall : MulContract call)
    (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hb : SmallRange s.mem b 160) (p : Coordinates) (hp : PointBound p)
    (hleft : readCoordinates s.mem a = left (squareStage p))
    (hright : readCoordinates s.mem b = right (squareStage p)) :
    ∃ s' : GlobalState,
      call (args3 r a b) s = .value (.nil, s') ∧
      readCoordinates s'.mem r = output p ∧
      PointBound (readCoordinates s'.mem r) ∧
      values (readCoordinates s'.mem r) = PointArithmetic.avx2Double (values p) := by
  have hl : ∀ lane, Avx2FieldMul.LeftBound
      (Avx2FieldMul.Execution.inputNat
        (Avx2FieldMul.Execution.readBlocks s.mem a) lane) := by
    intro lane
    change Avx2FieldMul.LeftBound (readCoordinates s.mem a lane)
    rw [hleft]
    exact multiply_left_bounded (squareStage_bounded hp) lane
  have hr' : ∀ lane, Avx2FieldMul.RightBound
      (Avx2FieldMul.Execution.inputNat
        (Avx2FieldMul.Execution.readBlocks s.mem b) lane) := by
    intro lane
    change Avx2FieldMul.RightBound (readCoordinates s.mem b lane)
    rw [hright]
    exact multiply_right_bounded (squareStage_bounded hp) lane
  let s' : GlobalState := {s with mem := (Reduce64.Execution.storeOutputs s.mem r
    (Avx2FieldMul.Execution.rawColumns4
      (Avx2FieldMul.Execution.readBlocks s.mem a)
      (Avx2FieldMul.Execution.readBlocks s.mem b)))}
  have hout : readCoordinates s'.mem r = output p := by
    funext lane limb
    rw [readCoordinates_eq_outputWord]
    rw [Avx2FieldMul.Execution.outputWord_product s.mem r _ _ hr lane (hl lane) (hr' lane)]
    change Avx2FieldMul.product (readCoordinates s.mem a lane)
      (readCoordinates s.mem b lane) limb = output p lane limb
    rw [hleft, hright]
    rfl
  refine ⟨s', hcall r a b s hwf hr ha hb, hout, ?_, ?_⟩
  · rw [hout]
    exact output_bounded hp
  · rw [hout]
    exact output_values hp

end Agave.Ed25519.Avx2PointDouble.Execution
