import SSA.Projects.Agave.Ed25519.Bridge.AgaveReadyExecution

/-! A bcmp-only public constructor for the closed Agave wrapper. The seed's
other slots are discarded by the concrete linker; the equality theorem proves
that no other caller-supplied function can affect the resulting wrapper. -/
namespace Agave.Ed25519.Bridge.AgaveReady
open Verifier Verifier.Execution
open LeanMLIR.RIR
open Dalek.SerialBackendReadiness (Ready Separate)
set_option maxRecDepth 24000
set_option maxHeartbeats 8000000

/-- Seed for a linker that replaces every field except compareBytes. -/
def bcmpOnly (compareCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32])) : Dalek.Primitives :=
  { challengeScalar := fun _ _ => .poison
    pointMulByPow2 := fun _ _ => .poison
    pointConstantTimeEq := fun _ _ => .poison
    decompress := fun _ _ => .poison
    blackBoxByte := fun _ _ => .poison
    scalarReduce := fun _ _ => .poison
    bytesConstantTimeEq := fun _ _ => .poison
    initializeAvx2Cache := fun _ _ => .poison
    serialDoubleBase := fun _ _ => .poison
    avx2DoubleBase := fun _ _ => .poison
    compressPoint := fun _ _ => .poison
    compareBytes := compareCall }

section
variable (compareCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32]))
variable (dg : Dalek.Globals)
variable (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
variable (serialGlobals : DoubleBase.SerialCFG.Globals)
variable (d2 : Tables.SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic)
variable (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
variable (avx2Globals : DoubleBase.Avx2CFG.Globals)
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)

variable (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
variable (hbcmp : Dalek.CompareContract compareCall)
variable (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
variable (hcaller : ColdInput.CallerMemory i initial a r s message)
variable (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
variable (hserial : Ready serialGlobals d2 initial)
variable (havxGlobals : DoubleBase.ExecutionAvx2.GlobalsReady avx2Globals initial)
variable (hseparate : Separate serialGlobals d2 dg.address1)
variable (havxSeparate : avx2Globals.address2.id ≠ dg.address1.id)
include hhardware hbcmp hcaller hglobals hserial havxGlobals hseparate havxSeparate


/-- Only bcmp remains as an opaque functional implementation contract.
Hardware and unreachable panic symbols remain ordinary linker parameters. -/
theorem call_strict_bcmp :
    ∃ finalState, (Wrapper.program (wrapper (bcmpOnly compareCall) dg hardware
      serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)).call
      i.args initial = .value (Wrapper.boolResult (strictVerify a r s message), finalState) :=
  call_strict (bcmpOnly compareCall) dg hardware serialGlobals d2 panic avx2Panic avx2Globals
    cg sg scg ddg dsg hhardware hbcmp i initial a r s message hcaller hglobals
    hserial havxGlobals hseparate havxSeparate

end

/-- The concrete linked wrapper is insensitive to all remaining-record fields
except the external byte comparator. This is equality of actual program inputs. -/
theorem wrapper_eq_of_compareBytes_eq (p q : Dalek.Primitives)
    (dg : Dalek.Globals) (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (serialGlobals : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (panic : DoubleBase.RIR.SerialPanic)
    (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
    (avx2Globals : DoubleBase.Avx2CFG.Globals) (cg : Execution.Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (hcompare : p.compareBytes = q.compareBytes) :
    wrapper p dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg =
      wrapper q dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg := by
  cases p
  cases q
  dsimp only at hcompare
  cases hcompare
  rfl

end Agave.Ed25519.Bridge.AgaveReady
