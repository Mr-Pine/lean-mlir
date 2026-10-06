import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionGlobals
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ControlFlow

/-!
# Execution interface for the exact extracted verifier

`linkedWrapper` connects the original byte-input wrapper to the extracted key
constructor and `verify_dalek`, using their actual RIR `Func.call` semantics.
`linkedChallenge` likewise resolves `challenge_scalar` to its extracted body.
The only remaining external effects are the individually named fields in the
generated primitive records. No verifier body is supplied as an opaque helper
when these linkers are used.

The Boolean composition theorem below is conditional on `RefinesControlFlow`.
That condition is a separate, currently undischarged memory/execution proof
obligation. In particular, successful import is not that proof. The contracts
still needed include the Rust option/result layouts, point negation in the key
constructor, cofactor multiplication and point equality, canonical scalar
reduction, backend calls, compression, byte comparison, and frame preservation.
SHA-512 and decompression also retain explicit primitive boundaries.
-/

namespace Agave.Ed25519.Verifier.Execution

open LeanMLIR.RIR
section

/-- Resolve both formerly opaque verifier callees to their extracted bodies.
The signature constructor is the remaining 64-byte copy primitive. -/
noncomputable def linkedWrapper (key : Key.Primitives)
    (dalek : Dalek.Primitives) (globalMap : Dalek.Globals)
    (signatureFromBytes : Vals [.ptr, .ptr] → EffectM (Vals [])) : Wrapper.Primitives where
  keyFromBytes := (Key.program key).call
  verifyDalek := (Dalek.program dalek globalMap).call
  signatureFromBytes := signatureFromBytes

/-- Resolve the message challenge to its exact extracted body. Its two named
external calls are SHA-512 compression and digest-to-scalar finalization. -/
noncomputable def linkedChallenge (dalek : Dalek.Primitives)
    (challenge : Challenge.Primitives) (globalMap : Challenge.Globals) : Dalek.Primitives :=
  { dalek with challengeScalar := (Challenge.program challenge globalMap).call }

/-- The pinned Rust ABI represents `Ok(())` by 255 and `InvalidSignature` by 2.
These are the only result bytes returned by the extracted `verify_dalek`. -/
def resultCode (accepted : Bool) : BitVec 8 := if accepted then 255 else 2

theorem resultCode_is_ok (accepted : Bool) :
    decide (resultCode accepted = 255) = accepted := by
  cases accepted <;> decide

/-- The exact final comparison in `verify_dalek` turns `bcmp == 0` into the
success discriminant; the outer wrapper compares that discriminant with 255. -/
theorem final_comparison (comparison : BitVec 32) :
    decide ((if comparison = 0 then (255 : BitVec 8) else 2) = 255) =
      decide (comparison = 0) := by
  by_cases h : comparison = 0 <;> simp [h]

/-- A legal Rust slice invocation, with the memory facts separated from the
byte-level acceptance predicate. Message bytes are read in little-endian order.
Rust's generated ABI limits the slice length to the signed pointer range. -/
structure Invocation where
  publicKey : Pointer
  signature : Pointer
  message : Pointer
  length : BitVec 64

def Invocation.args (i : Invocation) : Vals [.ptr, .ptr, .ptr, .bv 64] :=
  .cons (.value i.publicKey) (.cons (.value i.signature)
    (.cons (.value i.message) (.cons (.value i.length) .nil)))

/-- All inputs, including malformed encodings, are admitted. `Fits` only records
the memory needed by the wrapper; it does not assert cryptographic validity. -/
structure Represents (i : Invocation) (state : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8)) : Prop where
  wellFormed : state.WF
  /-- Required by RIR's explicit live-allocation semantics for flags-7 GEP. -/
  smallAllocations : ∀ (id : BlockId) (block : MemoryBlock),
    state.mem[id]? = some block → block.length < 2 ^ 63
  publicKeyFits : Fits state.mem i.publicKey 256
  signatureFits : Fits state.mem i.signature 512
  messageFits : Fits state.mem i.message (8 * message.length)
  length : i.length.toNat = message.length
  lengthBound : message.length < 2 ^ 63
  publicKey : state.mem.readAt i.publicKey 256 = a
  signatureR : state.mem.readAt i.signature 256 = r
  signatureS : state.mem.readAt (i.signature.add 32) 256 = s
  message : ∀ (n : Nat) (hn : n < message.length),
    state.mem.readAt (i.message.add (BitVec.ofNat 64 n)) 8 = message[n]

/-- Exact global-state requirements for the linked verifier/challenge bodies.
The CPUID cache is mutable: 255 is uninitialized, and 0/1 are cached results.
Primitive-specific table, aliasing, and memory invariants belong in
`primitiveReady`; its proof is required at each concrete invocation. -/
structure LinkedEnvironment (dalek : Dalek.Globals) (challenge : Challenge.Globals)
    (primitiveReady : GlobalState → Prop) (i : Invocation) (state : GlobalState) : Prop where
  identityAddress : dalek.address0.offset = 0
  identityPresent : identityOne.Present dalek.address0.id state.mem
  shaAddress : challenge.address0.offset = 0
  shaPresent : sha512InitialState.Present challenge.address0.id state.mem
  cacheAddress : dalek.address1.offset = 0
  cachePresent : ∃ value : BitVec 8,
    state.mem[dalek.address1.id]? = some ⟨1, value⟩ ∧
      (value = 0 ∨ value = 1 ∨ value = 255)
  distinctGlobals : [dalek.address0.id, dalek.address1.id, challenge.address0.id].Nodup
  cacheDisjointInput : dalek.address1.id ∉
    [i.publicKey.id, i.signature.id, i.message.id]
  primitives : primitiveReady state

/-- Observe the returned Boolean. Poison/undefined execution remains `none`;
it is not silently treated as rejection. -/
noncomputable def observe (primitives : Wrapper.Primitives) (i : Invocation)
    (state : GlobalState) : Option Bool :=
  match (Wrapper.program primitives).call i.args state with
  | .poison => none
  | .value (.cons .poison .nil, _) => none
  | .value (.cons (.value b) .nil, _) => some (decide (b = 1))

/-- The outstanding execution-conformance obligation, stated on the actual
linked RIR program and every representable input. It includes termination and
absence of poison, not merely agreement on runs that happen to succeed. -/
def RefinesControlFlow {Point Scalar Result : Type}
    (primitives : Wrapper.Primitives) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (environment : Invocation → GlobalState → Prop) : Prop :=
  ∀ (i : Invocation) (state : GlobalState) (a r s : Bytes32) (message : List (BitVec 8)),
    Represents i state a r s message → environment i state →
    observe primitives i state =
      some (verify shared doubleBase compress a r s (challenge r a message))

/-- The concrete linking of the three extracted bodies, with exactly the
environment invariant needed by their global loads. This remains a proof
obligation; its environment is not optional or replaced by `True`. -/
noncomputable def LinkedRefinesControlFlow {Point Scalar Result : Type}
    (key : Key.Primitives) (dalek : Dalek.Primitives) (dg : Dalek.Globals)
    (sha : Challenge.Primitives) (cg : Challenge.Globals)
    (signatureFromBytes : Vals [.ptr, .ptr] → EffectM (Vals []))
    (shared : Shared Point Scalar) (doubleBase : Scalar → Point → Scalar → Result)
    (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (primitiveReady : GlobalState → Prop) : Prop :=
  RefinesControlFlow (linkedWrapper key (linkedChallenge dalek sha cg) dg signatureFromBytes)
    shared doubleBase compress challenge (LinkedEnvironment dg cg primitiveReady)

/-- Instantiation at a real RIR invocation requires both byte-layout facts and
the exact globals/primitive invariant. It cannot be applied to absent globals. -/
theorem linked_observation_of_refinement {Point Scalar Result : Type}
    (key : Key.Primitives) (dalek : Dalek.Primitives) (dg : Dalek.Globals)
    (sha : Challenge.Primitives) (cg : Challenge.Globals)
    (signatureFromBytes : Vals [.ptr, .ptr] → EffectM (Vals []))
    (shared : Shared Point Scalar) (doubleBase : Scalar → Point → Scalar → Result)
    (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (primitiveReady : GlobalState → Prop)
    (hrefines : LinkedRefinesControlFlow key dalek dg sha cg signatureFromBytes
      shared doubleBase compress challenge primitiveReady)
    (i : Invocation) (state : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hinput : Represents i state a r s message)
    (henv : LinkedEnvironment dg cg primitiveReady i state) :
    observe (linkedWrapper key (linkedChallenge dalek sha cg) dg signatureFromBytes) i state =
      some (verify shared doubleBase compress a r s (challenge r a message)) :=
  hrefines i state a r s message hinput henv

/-- All-input Boolean equality follows once the two exact executions refine
the shared control flow and the backends have equal compressed observations.
No validity restriction is imposed on public keys or signature components.
This theorem does not construct either execution-refinement premise. -/
theorem observations_equal_of_refinement {Point Scalar Left Right : Type}
    (leftPrimitives rightPrimitives : Wrapper.Primitives) (shared : Shared Point Scalar)
    (left : Scalar → Point → Scalar → Left) (right : Scalar → Point → Scalar → Right)
    (compressLeft : Left → Bytes32) (compressRight : Right → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (leftEnvironment rightEnvironment : Invocation → GlobalState → Prop)
    (hleft : RefinesControlFlow leftPrimitives shared left compressLeft challenge leftEnvironment)
    (hright : RefinesControlFlow rightPrimitives shared right compressRight challenge rightEnvironment)
    (hbackend : ∀ a r s message A R scalar,
      shared.decompress a = some A → shared.smallOrder (shared.negate A) = false →
      shared.decompress r = some R → shared.smallOrder R = false →
      shared.parseScalar s = some scalar →
      compressLeft (left (challenge r a message) (shared.negate A) scalar) =
        compressRight (right (challenge r a message) (shared.negate A) scalar))
    (i : Invocation) (state : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hinput : Represents i state a r s message)
    (henvLeft : leftEnvironment i state) (henvRight : rightEnvironment i state) :
    observe leftPrimitives i state = observe rightPrimitives i state := by
  rw [hleft i state a r s message hinput henvLeft,
    hright i state a r s message hinput henvRight]
  exact congrArg some (verify_congr shared left right compressLeft compressRight
    a r s (challenge r a message) (hbackend a r s message))

end
end Agave.Ed25519.Verifier.Execution
