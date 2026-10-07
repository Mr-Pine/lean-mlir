import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.ExecutionRefinement
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.MixingPacking
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs

/-! Packed, exact-state consequences of the explicit byte-level helper
contracts for the caller in bb18. No property of point doubling or the
surrounding loop is assumed. -/
namespace Agave.Ed25519.Avx2PointDouble.Execution
open LeanMLIR.RIR
open Avx2FieldMul.Execution (readBlocks storeBlocks)
open Avx2PointAdd.Phases (readBlocks_storeBlocks)
open Reduce64.Execution (SmallRange)
open DoubleBase.ExecutionAvx2 (SquareContract MulContract args2 args3)

theorem packCoordinates_readCoordinates (m : MemoryState) (r : Pointer) :
    packCoordinates (readCoordinates m r) = readBlocks m r :=
  packCoordinates_blockCoordinates _

theorem square_packed_state
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (hcall : SquareContract call)
    (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (input : Blocks) (hp : PointBound (blockCoordinates input))
    (hprepare : readBlocks s.mem a = prepareBlocks input) :
    call (args2 r a) s = .value (.nil,
      {s with mem := storeBlocks s.mem r (packCoordinates (squareStage (blockCoordinates input)))}) := by
  obtain ⟨s', hactual, hout, _⟩ := square_call_prepared call hcall r a s hwf hr ha input hp hprepare
  have hraw := hcall r a s hwf hr ha
  have hs' : s' = {s with mem := (Reduce64.Execution.storeOutputs s.mem r
      (Avx2SquareNegateD.Execution.signedColumns4
        (Avx2SquareNegateD.Execution.readBlocks s.mem a)))} := by
    exact congrArg Prod.snd (PoisonOr.value_inj.mp (hactual.symm.trans hraw))
  have hpacked : Reduce64.Execution.packedOutput
      (Avx2SquareNegateD.Execution.signedColumns4
        (Avx2SquareNegateD.Execution.readBlocks s.mem a)) =
      packCoordinates (squareStage (blockCoordinates input)) := by
    have hwords := congrArg packCoordinates hout
    rw [packCoordinates_readCoordinates, hs'] at hwords
    simpa only [Avx2FieldMul.Execution.readBlocks_storeOutputs s.mem r _ hr] using hwords
  rw [hcall r a s hwf hr ha]
  change PoisonOr.value (Vals.nil, {s with mem := (storeBlocks s.mem r
    (Reduce64.Execution.packedOutput (Avx2SquareNegateD.Execution.signedColumns4
      (Avx2SquareNegateD.Execution.readBlocks s.mem a))))}) = _
  rw [hpacked]

theorem multiply_packed_state
    (call : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])) (hcall : MulContract call)
    (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hb : SmallRange s.mem b 160) (p : Coordinates) (hp : PointBound p)
    (hleft : readCoordinates s.mem a = left (squareStage p))
    (hright : readCoordinates s.mem b = right (squareStage p)) :
    call (args3 r a b) s = .value (.nil,
      {s with mem := storeBlocks s.mem r (packCoordinates (output p))}) := by
  obtain ⟨s', hactual, hout, _, _⟩ :=
    multiply_call_correct call hcall r a b s hwf hr ha hb p hp hleft hright
  have hraw := hcall r a b s hwf hr ha hb
  have hs' : s' = {s with mem := (Reduce64.Execution.storeOutputs s.mem r
      (Avx2FieldMul.Execution.rawColumns4 (readBlocks s.mem a) (readBlocks s.mem b)))} := by
    exact congrArg Prod.snd (PoisonOr.value_inj.mp (hactual.symm.trans hraw))
  have hpacked : Reduce64.Execution.packedOutput
      (Avx2FieldMul.Execution.rawColumns4 (readBlocks s.mem a) (readBlocks s.mem b)) =
      packCoordinates (output p) := by
    have hwords := congrArg packCoordinates hout
    rw [packCoordinates_readCoordinates, hs'] at hwords
    simpa only [Avx2FieldMul.Execution.readBlocks_storeOutputs s.mem r _ hr] using hwords
  rw [hcall r a b s hwf hr ha hb]
  change PoisonOr.value (Vals.nil, {s with mem := (storeBlocks s.mem r
    (Reduce64.Execution.packedOutput (Avx2FieldMul.Execution.rawColumns4
      (readBlocks s.mem a) (readBlocks s.mem b))))}) = _
  rw [hpacked]

/-- This form consumes the caller's five stored vectors. The asymmetric
doubling bounds, rather than point-add's narrower wide bound, justify both
operands. -/
theorem blockCoordinates_pack_left {q : Coordinates} (hq : PointBound q) :
    blockCoordinates (packCoordinates (left q)) = left q := by
  have hfit (e : Fin 4) (i : Fin 10) : left q e i < 2 ^ 32 := by
    have h := left_bound hq e i
    unfold leftLimit radix slack at h
    split_ifs at h <;> norm_num at h ⊢ <;> omega
  funext e i
  fin_cases e <;> fin_cases i <;>
    simp [blockCoordinates, packCoordinates, pointOf, Avx2FieldMul.Execution.unpackBlocks,
      Avx2PointAdd.Phases.packPoint, Avx2PointAdd.Phases.evenIndex,
      Avx2PointAdd.Phases.oddIndex, Avx2PointAdd.word]
  all_goals exact hfit _ _

theorem blockCoordinates_pack_right {q : Coordinates} (hq : PointBound q) :
    blockCoordinates (packCoordinates (right q)) = right q := by
  have hfit (e : Fin 4) (i : Fin 10) : right q e i < 2 ^ 32 := by
    have h := right_bound hq e i
    unfold rightLimit radix slack at h
    split_ifs at h <;> norm_num at h ⊢ <;> omega
  funext e i
  fin_cases e <;> fin_cases i <;>
    simp [blockCoordinates, packCoordinates, pointOf, Avx2FieldMul.Execution.unpackBlocks,
      Avx2PointAdd.Phases.packPoint, Avx2PointAdd.Phases.evenIndex,
      Avx2PointAdd.Phases.oddIndex, Avx2PointAdd.word]
  all_goals exact hfit _ _

end Agave.Ed25519.Avx2PointDouble.Execution
