import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedColdLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCompressLinked
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorLinked
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityValidPoint
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdLinked
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialDalekContract
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorContract

/-! Compose the already proved cofactor, small-order equality, point compressor,
and scalar-wide call into the exact verifier. The five remaining Dalek contracts
are explicit below. Decoder execution, SHA compression, and invocation memory
remain separate premises. In particular, neither the external bcmp ABI nor
the hardware-dependent AVX2 cache initializer is supplied by this module.

The backend contracts here retain the original all-state interface. Concrete
global-dependent backends require the separate invocation-local `*Under` chain;
this module does not manufacture their global readiness.
-/
namespace Agave.Ed25519.Verifier.Execution.LinkedProvedLeaves
open LeanMLIR.RIR

abbrev timesEight := SmallOrder.ValidPoint.timesEight

/-- Fix three previously residual leaves to their actual imported programs. -/
noncomputable def primitives (remaining : Dalek.Primitives) : Dalek.Primitives :=
  { remaining with
    pointMulByPow2 := SmallOrder.Execution.cofactorProgram.call
    pointConstantTimeEq := SmallOrder.Execution.equalityProgram.call
    compressPoint := Encoding.Compress.Execution.linkedProgram.call }

/-- Exactly the five Dalek leaves not discharged by this composition.
The cache field is an explicit hardware/ABI boundary and bcmp remains external.
The scalar reduction and both backend refinements are proof obligations. -/
structure RemainingContracts (p : Dalek.Primitives) (dg : Dalek.Globals) : Prop where
  scalarReduce : Dalek.ScalarReduceContract p.scalarReduce (ValidPoint.layout timesEight)
  cache : Dalek.CacheContract p.initializeAvx2Cache dg.address1
  serialDoubleBase : Dalek.DoubleBaseContract p.serialDoubleBase
    (ValidPoint.layout timesEight) ValidPoint.doubleBase
  avx2DoubleBase : Dalek.DoubleBaseContract p.avx2DoubleBase
    (ValidPoint.layout timesEight) ValidPoint.doubleBase
  bcmp : Dalek.CompareContract p.compareBytes

/-- The cofactor and equality theorems share the same exact limb representative;
compression consumes the valid result representation returned by either backend. -/
theorem RemainingContracts.complete (p : Dalek.Primitives) (dg : Dalek.Globals)
    (decode : Bytes32 → Option ValidPoint) (h : RemainingContracts p dg) :
    ResidualLeaves.NonDecoderContracts (primitives p) dg decode timesEight := by
  exact
    { cofactor := SmallOrder.Execution.cofactorContract
      smallOrderEq := SmallOrder.Execution.EqualityValidPoint.smallOrder_contract
        decode timesEight SmallOrder.ValidPoint.timesEight_curve
      scalarReduce := h.scalarReduce
      cache := h.cache
      serialDoubleBase := h.serialDoubleBase
      avx2DoubleBase := h.avx2DoubleBase
      compress := Dalek.linked_compress_contract timesEight
      bcmp := h.bcmp }

/-- The completed constructor proof removes the serial adapter's former table
execution premise. Its immutable globals are still required at the actual call
state, so this theorem deliberately retains DoubleBaseContractUnder. -/
theorem serial_doubleBase_contract_under (g : DoubleBase.SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic) :
    Dalek.DoubleBaseContractUnder (DoubleBase.RIR.serialLinkedReady g d2)
      (DoubleBase.RIR.serialLinkedKernel g d2 panic).call
      (ValidPoint.layout timesEight) ValidPoint.doubleBase :=
  DoubleBase.RIR.serialLinked_doubleBaseContractUnder g d2 panic timesEight
    (Tables.SerialConstructorContract.linked_contract d2 panic)

section
variable (kp : Key.Primitives) (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
variable (compression : Agave.Ed25519.SHA512.Compression)
variable (cg : Challenge.Globals) (sg : ScalarWide.Globals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (decode : Bytes32 → Option ValidPoint)
variable (hleaves : RemainingContracts remaining dg)
variable (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
  (ValidPoint.layout timesEight) (ValidPoint.shared decode))

include hleaves hdecodeRun

/-- Contextual exact wrapper execution with the three point leaves and the
wide-reduction finalizer supplied by their proved imported implementations. -/
theorem primitive_calls_contextual
    (hcompress : Challenge.CompressContract compressCall (Agave.Ed25519.SHA512.model compression))
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hinput : LinkedContextualLeaves.Inputs kp dg cg sg ddg dsg decode timesEight
      i initial a r s message) :
    Wrapper.PrimitiveCalls
      (linkedWrapper kp
        (LinkedContextualLeaves.primitives (primitives remaining) compressCall sg cg ddg dsg)
        dg Signature.program.call)
      (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress
      (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression))
      i initial a r s message :=
  LinkedContextualLeaves.primitive_calls kp (primitives remaining) dg compressCall
    compression cg sg ddg dsg decode timesEight
    (RemainingContracts.complete remaining dg decode hleaves) hdecodeRun hcompress
    (SHA512Finalization.linkedReduceWide_of_execution sg (ScalarWide.execution_obligation sg))
    i initial a r s message hinput

/-- Defined contextual observation; no cofactor, point-equality, compression,
or scalar-wide execution hypothesis remains. -/
theorem observe_contextual
    (hcompress : Challenge.CompressContract compressCall (Agave.Ed25519.SHA512.model compression))
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hinput : LinkedContextualLeaves.Inputs kp dg cg sg ddg dsg decode timesEight
      i initial a r s message) :
    Execution.observe
      (linkedWrapper kp
        (LinkedContextualLeaves.primitives (primitives remaining) compressCall sg cg ddg dsg)
        dg Signature.program.call) i initial =
      some (verify (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress a r s
        (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression) r a message)) :=
  LinkedContextualLeaves.observe kp (primitives remaining) dg compressCall
    compression cg sg ddg dsg decode timesEight
    (RemainingContracts.complete remaining dg decode hleaves) hdecodeRun hcompress
    (SHA512Finalization.linkedReduceWide_of_execution sg (ScalarWide.execution_obligation sg))
    i initial a r s message hinput

/-- Exact cold-capable wrapper execution. The SHA cache may start cold or warm;
the local readiness and cache-aware compression contract remain explicit. -/
theorem primitive_calls_cold (scg : SHA512Finalization.CompressionGlobals)
    (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hinput : LinkedColdLeaves.Inputs kp dg cg sg scg ddg dsg decode timesEight
      i initial a r s message) :
    Wrapper.PrimitiveCalls
      (linkedWrapper kp
        (LinkedColdLeaves.primitives (primitives remaining) compressCall sg cg ddg dsg)
        dg Signature.program.call)
      (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress
      (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression))
      i initial a r s message :=
  LinkedColdLeaves.primitive_calls kp (primitives remaining) dg compressCall
    compression cg sg scg ddg dsg decode timesEight
    (RemainingContracts.complete remaining dg decode hleaves) hdecodeRun hcompress
    (ScalarWide.execution_obligation sg) i initial a r s message hinput

/-- Cold/warm observation after discharging every currently proved leaf in
this interface. This remains conditional on the five fields of RemainingContracts,
the contextual decoder, SHA compression, and concrete invocation inputs. -/
theorem observe_cold (scg : SHA512Finalization.CompressionGlobals)
    (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hinput : LinkedColdLeaves.Inputs kp dg cg sg scg ddg dsg decode timesEight
      i initial a r s message) :
    Execution.observe
      (linkedWrapper kp
        (LinkedColdLeaves.primitives (primitives remaining) compressCall sg cg ddg dsg)
        dg Signature.program.call) i initial =
      some (verify (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress a r s
        (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression) r a message)) :=
  LinkedColdLeaves.observe kp (primitives remaining) dg compressCall
    compression cg sg scg ddg dsg decode timesEight
    (RemainingContracts.complete remaining dg decode hleaves) hdecodeRun hcompress
    (ScalarWide.execution_obligation sg) i initial a r s message hinput

end
end Agave.Ed25519.Verifier.Execution.LinkedProvedLeaves
