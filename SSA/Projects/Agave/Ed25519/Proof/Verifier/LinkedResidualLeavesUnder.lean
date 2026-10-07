import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedResidualLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContractsUnder

/-! The residual leaf interface with invocation-local backend contracts. -/
namespace Agave.Ed25519.Verifier.Execution.ResidualLeaves
open LeanMLIR.RIR

structure NonDecoderContractsUnder (p : Dalek.Primitives) (dg : Dalek.Globals)
    (serialReady avx2Ready : Dalek.BackendReadyPredicate)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint) : Prop where
  cofactor : Dalek.CofactorContract p.pointMulByPow2 (ValidPoint.layout timesEight)
  smallOrderEq : Dalek.SmallOrderEqContract p.pointConstantTimeEq (ValidPoint.layout timesEight)
    (ValidPoint.shared decode)
  scalarReduce : Dalek.ScalarReduceContract p.scalarReduce (ValidPoint.layout timesEight)
  cache : Dalek.CacheContract p.initializeAvx2Cache dg.address1
  serialDoubleBase : Dalek.DoubleBaseContractUnder serialReady p.serialDoubleBase
    (ValidPoint.layout timesEight) ValidPoint.doubleBase
  avx2DoubleBase : Dalek.DoubleBaseContractUnder avx2Ready p.avx2DoubleBase
    (ValidPoint.layout timesEight) ValidPoint.doubleBase
  compress : Dalek.CompressContract p.compressPoint (ValidPoint.layout timesEight) Bridge.compress
  bcmp : Dalek.CompareContract p.compareBytes

/-- Construct the full interface from exactly the outstanding leaves. The
black-box allocation effect and all 33 comparison black-box calls are supplied
by their existing exact execution proofs. -/
theorem NonDecoderContractsUnder.complete
    (p : Dalek.Primitives) (dg : Dalek.Globals)
    (serialReady avx2Ready : Dalek.BackendReadyPredicate)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (decodeCall : Vals [.ptr, .ptr] → EffectM (Vals []))
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (h : NonDecoderContractsUnder p dg serialReady avx2Ready decode timesEight) :
    Dalek.NonDecoderLeafContractsUnder (decoderPrimitives p cp cg decodeCall) dg serialReady avx2Ready (ValidPoint.layout timesEight)
      (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress := by
  obtain ⟨hparse, hcomplete⟩ := ValidPoint.parser_contracts decode timesEight
  exact
    { pointMulByPow2 := h.cofactor
      pointConstantTimeEq := h.smallOrderEq
      blackBoxByte := Dalek.BytePrimitives.blackBox_contract
      scalarReduce := h.scalarReduce
      bytesConstantTimeEq := Dalek.BytePrimitives.bytesEq_contract
      initializeAvx2Cache := h.cache
      serialDoubleBase := h.serialDoubleBase
      avx2DoubleBase := h.avx2DoubleBase
      compressPoint := h.compress
      compareBytes := h.bcmp
      scalarParse := hparse
      scalarComplete := hcomplete }

end Agave.Ed25519.Verifier.Execution.ResidualLeaves
