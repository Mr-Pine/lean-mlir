import SSA.Projects.Agave.Ed25519.Bridge.CrossClientBackendLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCompressLinked

/-! All concrete Dalek execution leaves are linked except external bcmp.
The two backend contracts require only their actual loaded globals. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution
open LeanMLIR.RIR (Vals EffectM)

namespace ContextualProvedLeaves
noncomputable def primitives (remaining : Dalek.Primitives) (dg : Dalek.Globals)
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (serialGlobals : DoubleBase.SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic)
    (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
    (avx2Globals : DoubleBase.Avx2CFG.Globals) : Dalek.Primitives :=
  BackendLeaves.primitives
    { remaining with compressPoint := Encoding.Compress.Execution.linkedProgram.call }
    dg hardware serialGlobals d2 panic avx2Panic avx2Globals

structure RemainingContracts (p : Dalek.Primitives) : Prop where
  bcmp : Dalek.CompareContract p.compareBytes

theorem RemainingContracts.complete
    (p : Dalek.Primitives) (dg : Dalek.Globals)
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (serialGlobals : DoubleBase.SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic)
    (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
    (avx2Globals : DoubleBase.Avx2CFG.Globals)
    (decode : Bytes32 → Option ValidPoint) (h : RemainingContracts p)
    (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware) :
    ResidualLeaves.NonDecoderContractsUnder
      (primitives p dg hardware serialGlobals d2 panic avx2Panic avx2Globals) dg
      (DoubleBase.RIR.serialLinkedReady serialGlobals d2) (BackendLeaves.avx2Ready avx2Globals) decode
      SmallOrder.ValidPoint.timesEight :=
  BackendLeaves.RemainingContracts.complete
    { p with compressPoint := Encoding.Compress.Execution.linkedProgram.call }
    dg hardware serialGlobals d2 panic avx2Panic avx2Globals decode
    ⟨Dalek.linked_compress_contract SmallOrder.ValidPoint.timesEight, h.bcmp⟩ hhardware

end ContextualProvedLeaves
end Agave.Ed25519.Bridge
