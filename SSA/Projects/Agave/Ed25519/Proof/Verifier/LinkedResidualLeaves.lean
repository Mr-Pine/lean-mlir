import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedValidPayload
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekBytePrimitives
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionDecoderContextual

/-!
The final composition must not continue assuming contracts already proved for
the imported byte helpers, or parser properties proved for bounded scalars.
This module fixes those choices and names only the remaining Dalek leaves.

The remaining contracts are proof obligations, not claimed facts about the
extracted callees. In particular, global-dependent implementations need a
contextual replacement for the unrestricted interfaces used here.
-/
namespace Agave.Ed25519.Verifier.Execution.ResidualLeaves
open LeanMLIR.RIR

/-- Keep the unclosed callees explicit while linking the challenge and both
byte primitives directly to their imported RIR bodies. -/
noncomputable def primitives (remaining : Dalek.Primitives)
    (cp : Challenge.Primitives) (cg : Challenge.Globals) : Dalek.Primitives :=
  { remaining with
    challengeScalar := (Challenge.program cp cg).call
    blackBoxByte := Encoding.Decompress.Execution.BlackBox.program.call
    bytesConstantTimeEq := (Encoding.Decompress.Execution.BytesEq.program
      Encoding.Decompress.Execution.bytesEqPrimitives).call }

/-- The mathematical challenge is constructed from the original transcript
bytes. Its scalar range and its machine encoding need no separate hypotheses. -/
def scalarChallenge (sha : Challenge.Sha512Model)
    (r a : Bytes32) (message : List (BitVec 8)) : CanonicalScalar :=
  ⟨(sha.digest (Challenge.transcript r a message)).toNat % Bridge.subgroupOrder,
    Nat.mod_lt _ (by norm_num [Bridge.subgroupOrder])⟩

theorem scalarChallenge_encoding (sha : Challenge.Sha512Model)
    (r a : Bytes32) (message : List (BitVec 8)) :
    CanonicalScalar.encode (scalarChallenge sha r a message) =
      Challenge.digestScalarBytes (sha.digest (Challenge.transcript r a message)) := rfl

/-- The nine remaining Dalek semantic leaf obligations. The decoder called by
the public-key constructor is separately present in the invocation inputs. -/
structure Contracts (p : Dalek.Primitives) (dg : Dalek.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint) : Prop where
  cofactor : Dalek.CofactorContract p.pointMulByPow2 (ValidPoint.layout timesEight)
  smallOrderEq : Dalek.SmallOrderEqContract p.pointConstantTimeEq (ValidPoint.layout timesEight)
    (ValidPoint.shared decode)
  decompress : Dalek.DecompressContract p.decompress (ValidPoint.layout timesEight)
    (ValidPoint.shared decode)
  scalarReduce : Dalek.ScalarReduceContract p.scalarReduce (ValidPoint.layout timesEight)
  cache : Dalek.CacheContract p.initializeAvx2Cache dg.address1
  serialDoubleBase : Dalek.DoubleBaseContract p.serialDoubleBase
    (ValidPoint.layout timesEight) ValidPoint.doubleBase
  avx2DoubleBase : Dalek.DoubleBaseContract p.avx2DoubleBase
    (ValidPoint.layout timesEight) ValidPoint.doubleBase
  compress : Dalek.CompressContract p.compressPoint (ValidPoint.layout timesEight) Bridge.compress
  bcmp : Dalek.CompareContract p.compareBytes

/-- Construct the full interface from exactly the outstanding leaves. The
black-box allocation effect and all 33 comparison black-box calls are supplied
by their existing exact execution proofs. -/
theorem Contracts.complete
    (p : Dalek.Primitives) (dg : Dalek.Globals)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (h : Contracts p dg decode timesEight) :
    Dalek.LeafContracts (primitives p cp cg) dg (ValidPoint.layout timesEight)
      (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress := by
  obtain ⟨hparse, hcomplete⟩ := ValidPoint.parser_contracts decode timesEight
  exact
    { pointMulByPow2 := h.cofactor
      pointConstantTimeEq := h.smallOrderEq
      decompress := h.decompress
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

/-- Exact decoder linkage does not change any of the independent leaf slots. -/
noncomputable def decoderPrimitives (remaining : Dalek.Primitives)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (decodeCall : Vals [.ptr, .ptr] → EffectM (Vals [])) : Dalek.Primitives :=
  { primitives remaining cp cg with decompress := decodeCall }

/-- The eight remaining nondecoder leaves; contextual decompression is
supplied separately at its actual call state. -/
structure NonDecoderContracts (p : Dalek.Primitives) (dg : Dalek.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint) : Prop where
  cofactor : Dalek.CofactorContract p.pointMulByPow2 (ValidPoint.layout timesEight)
  smallOrderEq : Dalek.SmallOrderEqContract p.pointConstantTimeEq (ValidPoint.layout timesEight)
    (ValidPoint.shared decode)
  scalarReduce : Dalek.ScalarReduceContract p.scalarReduce (ValidPoint.layout timesEight)
  cache : Dalek.CacheContract p.initializeAvx2Cache dg.address1
  serialDoubleBase : Dalek.DoubleBaseContract p.serialDoubleBase
    (ValidPoint.layout timesEight) ValidPoint.doubleBase
  avx2DoubleBase : Dalek.DoubleBaseContract p.avx2DoubleBase
    (ValidPoint.layout timesEight) ValidPoint.doubleBase
  compress : Dalek.CompressContract p.compressPoint (ValidPoint.layout timesEight) Bridge.compress
  bcmp : Dalek.CompareContract p.compareBytes

/-- Construct the full interface from exactly the outstanding leaves. The
black-box allocation effect and all 33 comparison black-box calls are supplied
by their existing exact execution proofs. -/
theorem NonDecoderContracts.complete
    (p : Dalek.Primitives) (dg : Dalek.Globals)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (decodeCall : Vals [.ptr, .ptr] → EffectM (Vals []))
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (h : NonDecoderContracts p dg decode timesEight) :
    Dalek.NonDecoderLeafContracts (decoderPrimitives p cp cg decodeCall) dg (ValidPoint.layout timesEight)
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
