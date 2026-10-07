import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionProgram

/-! Bind both small-order verifier calls and every lower call to actual RIR
bodies from the pinned crate. This is code linkage, not execution refinement. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR Verifier.Execution

noncomputable def doublePrimitives : SmallOrderProjectiveDouble.Primitives where
  pow2k := Encoding.Decompress.Execution.Pow2k.program.call

noncomputable def cofactorPrimitives : PointMulByPow2.Primitives where
  projectiveDouble := (SmallOrderProjectiveDouble.program doublePrimitives).call
  fieldMul := SerialFieldMul.kernel.call

noncomputable def equalityPrimitives : PointConstantTimeEq.Primitives where
  fieldMul := SerialFieldMul.kernel.call
  bytesConstantTimeEq := (Encoding.Decompress.Execution.BytesEq.program
    Encoding.Decompress.Execution.bytesEqPrimitives).call
  blackBoxByte := Encoding.Decompress.Execution.BlackBox.program.call

noncomputable def cofactorProgram : Func := PointMulByPow2.program cofactorPrimitives
noncomputable def equalityProgram : Func := PointConstantTimeEq.program equalityPrimitives

noncomputable def linkVerifier (p : Dalek.Primitives) : Dalek.Primitives :=
  { p with
    pointMulByPow2 := cofactorProgram.call
    pointConstantTimeEq := equalityProgram.call }

theorem cofactor_is_imported (p : Dalek.Primitives) :
    (linkVerifier p).pointMulByPow2 =
      (PointMulByPow2.program cofactorPrimitives).call := rfl

theorem equality_is_imported (p : Dalek.Primitives) :
    (linkVerifier p).pointConstantTimeEq =
      (PointConstantTimeEq.program equalityPrimitives).call := rfl

end Agave.Ed25519.SmallOrder.Execution
