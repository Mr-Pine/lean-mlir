import SSA.Projects.Agave.Ed25519.Bridge.CrossClientCheckedLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCompressLinked
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorLinked

/-! Link the actual scalar reducer, point equality and point compressor using
their completed arithmetic and execution proofs. The imported cache initializer
is supplied from instruction-level hardware contracts. Equality uses the
proved cofactor representative. The three remaining Dalek leaves are explicit
implementation boundaries, not asserted theorems. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution

namespace ProvedLeaves

/-- Select the proved callees while preserving the remaining primitive slots. -/
noncomputable def primitives (remaining : Dalek.Primitives) (dg : Dalek.Globals)
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions) : Dalek.Primitives :=
  CheckedLeaves.primitives
    { remaining with
      compressPoint := Encoding.Compress.Execution.linkedProgram.call
      pointMulByPow2 := SmallOrder.Execution.cofactorProgram.call }
    dg hardware

/-- Only leaves without an unconditional linked implementation proof remain. -/
structure RemainingContracts (p : Dalek.Primitives) : Prop where
  serialDoubleBase : Dalek.DoubleBaseContract p.serialDoubleBase
    (ValidPoint.layout SmallOrder.ValidPoint.timesEight) ValidPoint.doubleBase
  avx2DoubleBase : Dalek.DoubleBaseContract p.avx2DoubleBase
    (ValidPoint.layout SmallOrder.ValidPoint.timesEight) ValidPoint.doubleBase
  bcmp : Dalek.CompareContract p.compareBytes

/-- Supply the removed cofactor, scalar, equality, compression and cache contract fields
from the corresponding linked implementation proofs. -/
theorem RemainingContracts.complete
    (p : Dalek.Primitives) (dg : Dalek.Globals)
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (decode : Bytes32 → Option ValidPoint) (h : RemainingContracts p)
    (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware) :
    ResidualLeaves.NonDecoderContracts (primitives p dg hardware) dg decode
      SmallOrder.ValidPoint.timesEight :=
  CheckedLeaves.RemainingContracts.complete
    { p with
      compressPoint := Encoding.Compress.Execution.linkedProgram.call
      pointMulByPow2 := SmallOrder.Execution.cofactorProgram.call } dg hardware decode
    { cofactor := SmallOrder.Execution.cofactorContract
      serialDoubleBase := h.serialDoubleBase
      avx2DoubleBase := h.avx2DoubleBase
      compress := Dalek.linked_compress_contract SmallOrder.ValidPoint.timesEight
      bcmp := h.bcmp }
    hhardware

end ProvedLeaves
end Agave.Ed25519.Bridge
