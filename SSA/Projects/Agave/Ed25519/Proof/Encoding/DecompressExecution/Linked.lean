import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Program
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioProgram
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501Program
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2kProgram
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytesProgram
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BytesEqProgram
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBox
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Contract

/-! Close the extracted decompression call graph with the actual imported RIR
bodies. No field operation, byte comparison, exponentiation, square-root helper,
or decompressor is supplied as an abstract effect. Global initializer and
memory-layout obligations remain explicit. Linking itself is not a refinement
proof of the whole decoder. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR

noncomputable def pow22501Primitives : Pow22501.Primitives where
  pow2k := Pow2k.program.call
  mul := SerialFieldMul.kernel.call

noncomputable def bytesEqPrimitives : BytesEq.Primitives where
  blackBoxByte := BlackBox.program.call

noncomputable def sqrtRatioPrimitives : SqrtRatio.Primitives where
  pow2k := Pow2k.program.call
  mul := SerialFieldMul.kernel.call
  pow22501 := (Pow22501.program pow22501Primitives).call
  toBytes := ToBytes.program.call
  bytesEq := (BytesEq.program bytesEqPrimitives).call
  blackBoxByte := BlackBox.program.call

noncomputable def decodePrimitives (sqrtGlobals : SqrtRatio.Globals) : Decode.Primitives where
  pow2k := Pow2k.program.call
  mul := SerialFieldMul.kernel.call
  sqrtRatio := (SqrtRatio.program sqrtRatioPrimitives sqrtGlobals).call
  blackBoxByte := BlackBox.program.call

/-- The concrete RIR decompressor with every reachable call bound to imported
code; two field-constant addresses remain parameters of the global environment. -/
noncomputable def linkedProgram (decodeGlobals : Decode.Globals)
    (sqrtGlobals : SqrtRatio.Globals) : Func :=
  Decode.program (decodePrimitives sqrtGlobals) decodeGlobals

end Agave.Ed25519.Encoding.Decompress.Execution
