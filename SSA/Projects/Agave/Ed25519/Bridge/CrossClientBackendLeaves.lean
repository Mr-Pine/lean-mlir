import SSA.Projects.Agave.Ed25519.Bridge.CrossClientCheckedLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedResidualLeavesUnder
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorLinked
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialClosed
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientAvx2Prefix

/-! Both backend witnesses link their actual constructor and arithmetic bodies.
Readiness contains only the concrete loaded serial and AVX2 globals. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution
open LeanMLIR.RIR (Pointer GlobalState Vals EffectM)

namespace BackendLeaves

abbrev avx2Ready := Dalek.Avx2BackendReadiness.ready

noncomputable def primitives (remaining : Dalek.Primitives) (dg : Dalek.Globals)
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (serialGlobals : DoubleBase.SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic)
    (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
    (avx2Globals : DoubleBase.Avx2CFG.Globals) : Dalek.Primitives :=
  CheckedLeaves.primitives
    { remaining with
      pointMulByPow2 := SmallOrder.Execution.cofactorProgram.call
      serialDoubleBase := (DoubleBase.RIR.serialLinkedKernel serialGlobals d2 panic).call
      avx2DoubleBase := (DoubleBase.RIR.avx2Kernel
        (DoubleBase.ExecutionAvx2.concretePrimitives avx2Panic) avx2Globals).call }
    dg hardware

structure RemainingContracts (p : Dalek.Primitives) : Prop where
  compress : Dalek.CompressContract p.compressPoint
    (ValidPoint.layout SmallOrder.ValidPoint.timesEight) Bridge.compress
  bcmp : Dalek.CompareContract p.compareBytes

/-- All backend/helper execution contracts are supplied by checked witnesses. -/
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
      (DoubleBase.RIR.serialLinkedReady serialGlobals d2) (avx2Ready avx2Globals) decode
      SmallOrder.ValidPoint.timesEight :=
  { cofactor := SmallOrder.Execution.cofactorContract
    smallOrderEq := SmallOrder.Execution.EqualityValidPoint.smallOrder_contract decode
      SmallOrder.ValidPoint.timesEight (fun _ => rfl)
    scalarReduce := ScalarReduce32.Execution.contract
      (ValidPoint.layout SmallOrder.ValidPoint.timesEight) (fun _ => rfl)
    cache := Dalek.Avx2Cache.Instructions.cache_contract hardware hhardware dg.address1
    serialDoubleBase := DoubleBase.RIR.serialLinked_doubleBaseContractUnder_closed serialGlobals d2 panic
      SmallOrder.ValidPoint.timesEight
    avx2DoubleBase := DoubleBase.ExecutionAvx2.concrete_doubleBaseContractUnder avx2Panic avx2Globals
      SmallOrder.ValidPoint.timesEight
    compress := h.compress
    bcmp := h.bcmp }

end BackendLeaves
end Agave.Ed25519.Bridge
