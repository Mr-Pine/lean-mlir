import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedResidualLeaves
import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.Contract
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityValidPoint
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorValidPoint
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Execution

/-! Instantiate the checked scalar32, point-equality and cache-initializer
proofs independently of the pending point-compression dependency closure.
The cofactor representative has its proved group interpretation. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution

namespace CheckedLeaves

/-- Select the proved callees while preserving the remaining primitive slots. -/
noncomputable def primitives (remaining : Dalek.Primitives) (dg : Dalek.Globals)
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions) : Dalek.Primitives :=
  { remaining with
    pointConstantTimeEq := SmallOrder.Execution.equalityProgram.call
    scalarReduce := ScalarReduce32.Execution.program.call
    initializeAvx2Cache :=
      (Dalek.Avx2Cache.Instructions.initializer hardware.link dg.address1).call }

/-- Only leaves without an unconditional linked implementation proof remain. -/
structure RemainingContracts (p : Dalek.Primitives) : Prop where
  cofactor : Dalek.CofactorContract p.pointMulByPow2
    (ValidPoint.layout SmallOrder.ValidPoint.timesEight)
  serialDoubleBase : Dalek.DoubleBaseContract p.serialDoubleBase
    (ValidPoint.layout SmallOrder.ValidPoint.timesEight) ValidPoint.doubleBase
  avx2DoubleBase : Dalek.DoubleBaseContract p.avx2DoubleBase
    (ValidPoint.layout SmallOrder.ValidPoint.timesEight) ValidPoint.doubleBase
  compress : Dalek.CompressContract p.compressPoint
    (ValidPoint.layout SmallOrder.ValidPoint.timesEight) Bridge.compress
  bcmp : Dalek.CompareContract p.compareBytes

/-- Supply the removed scalar, equality and cache contract fields
from the corresponding linked implementation proofs. -/
theorem RemainingContracts.complete
    (p : Dalek.Primitives) (dg : Dalek.Globals)
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (decode : Bytes32 → Option ValidPoint) (h : RemainingContracts p)
    (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware) :
    ResidualLeaves.NonDecoderContracts (primitives p dg hardware) dg decode
      SmallOrder.ValidPoint.timesEight :=
  { cofactor := h.cofactor
    smallOrderEq := SmallOrder.Execution.EqualityValidPoint.smallOrder_contract decode
      SmallOrder.ValidPoint.timesEight (fun _ => rfl)
    scalarReduce := ScalarReduce32.Execution.contract
      (ValidPoint.layout SmallOrder.ValidPoint.timesEight) (fun _ => rfl)
    cache := Dalek.Avx2Cache.Instructions.cache_contract hardware hhardware dg.address1
    serialDoubleBase := h.serialDoubleBase
    avx2DoubleBase := h.avx2DoubleBase
    compress := h.compress
    bcmp := h.bcmp }

end CheckedLeaves
end Agave.Ed25519.Bridge
