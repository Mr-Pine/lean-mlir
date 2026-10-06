import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ControlFlow
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-!
# Local primitive contracts for the imported Dalek verifier

Every execution contract below concerns exactly one named external call. None
mentions `Dalek.program`, a verifier run, or a final acceptance result. Frames
allow private callee allocations and preserve every prior live range and every
byte outside the output. The contracts are explicit obligations: this file does
not claim that the independently compiled cryptographic routines satisfy them.
-/

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

abbrev PointBytes := BitVec 1280

def args2 (a b : Pointer) : Vals [.ptr, .ptr] :=
  .cons (.value a) (.cons (.value b) .nil)

def args4 (a b c d : Pointer) : Vals [.ptr, .ptr, .ptr, .ptr] :=
  .cons (.value a) (.cons (.value b) (.cons (.value c) (.cons (.value d) .nil)))

/-- Exact bytes, plus allocation bounds. This assertion does not impose any
cryptographic validity condition on the represented bytes. -/
def ReadBytes (state : GlobalState) (p : Pointer) (bytes : Nat)
    (value : BitVec (8 * bytes)) : Prop :=
  SmallRange state.mem p bytes ∧ state.mem.readAt p (8 * bytes) = value

/-- The caller-visible frame of a single output-producing primitive. -/
structure OutputFrame (before after : GlobalState) (output : Pointer) (bytes : Nat) : Prop where
  wellFormed : after.WF
  live : ∀ (q : Pointer) (n : Nat),
    SmallRange before.mem q n → SmallRange after.mem q n
  read : ∀ (q : Pointer) (width : Nat),
    (Range.of q width).Disjoint (Range.of output (8 * bytes)) →
    after.mem.readAt q width = before.mem.readAt q width

/-- A read-only callee may use private stack space. Its allocation counter can
advance, but all caller-visible bytes and live ranges are preserved. -/
structure ReadOnlyFrame (before after : GlobalState) : Prop where
  wellFormed : after.WF
  live : ∀ (q : Pointer) (n : Nat),
    SmallRange before.mem q n → SmallRange after.mem q n
  read : ∀ (q : Pointer) (width : Nat),
    after.mem.readAt q width = before.mem.readAt q width

theorem OutputFrame.readBytes (before after : GlobalState) (output q : Pointer)
    (bytes count : Nat) (value : BitVec (8 * count))
    (frame : OutputFrame before after output bytes)
    (hread : ReadBytes before q count value)
    (hd : (Range.of q (8 * count)).Disjoint (Range.of output (8 * bytes))) :
    ReadBytes after q count value :=
  ⟨frame.live q count hread.1, (frame.read q (8 * count) hd).trans hread.2⟩

theorem ReadOnlyFrame.readBytes (before after : GlobalState) (q : Pointer)
    (count : Nat) (value : BitVec (8 * count))
    (frame : ReadOnlyFrame before after) (hread : ReadBytes before q count value) :
    ReadBytes after q count value :=
  ⟨frame.live q count hread.1, (frame.read q (8 * count)).trans hread.2⟩

/-- The layout functions distinguish ordinary points, their cofactor multiples,
backend outputs, and canonical scalars. `result` is a relation so that the
serial and vector implementations may use different projective representatives
of the same mathematical result; no equality of their result bytes is required. -/
structure Layout (Point Scalar Result : Type) where
  point : Point → PointBytes
  cofactor : Point → PointBytes
  result : Result → PointBytes → Prop
  scalar : Scalar → Bytes32
  identity : PointBytes
  reduce : Bytes32 → Bytes32

/-- The exact signed comparison used by `%53`: `s[31] > -1`. -/
def scalarHighBitClear (s : Bytes32) : Bool :=
  (-1 : BitVec 8).slt (s.extractLsb' 248 8)

def scalarGate (layout : Layout Point Scalar Result) (s : Bytes32) : Bool :=
  scalarHighBitClear s && decide (layout.reduce s = s)

/-- The `subtle::Choice` ABI uses exact byte values, not merely nonzero bytes. -/
def choiceByte (value : Bool) : BitVec 8 := if value then 1 else 0

theorem choiceByte_and (a b : Bool) :
    choiceByte a &&& choiceByte b = choiceByte (a && b) := by
  cases a <;> cases b <;> decide

theorem choiceByte_eq_one (b : Bool) : choiceByte b = 1 ↔ b = true := by
  cases b <;> decide

/-- Reduction equality, the high-bit check, and the final equality-to-one
have exactly the parser gate's Boolean value. -/
theorem scalar_choice_gate (layout : Layout Point Scalar Result) (s : Bytes32) :
    (choiceByte (decide (s = layout.reduce s)) &&& choiceByte (scalarHighBitClear s) = 1) ↔
      scalarGate layout s = true := by
  rw [choiceByte_and, choiceByte_eq_one]
  simp only [scalarGate, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨heq, hhigh⟩
    exact ⟨hhigh, heq.symm⟩
  · rintro ⟨hhigh, heq⟩
    exact ⟨heq.symm, hhigh⟩

/-- The scalar source contract connects reduction and byte equality to the
canonical parser, including rejected byte strings. -/
def ScalarParseContract (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar) : Prop :=
  ∀ (s : Bytes32) (scalar : Scalar),
    shared.parseScalar s = some scalar ↔
      scalarGate layout s = true ∧ layout.scalar scalar = s

/-- Successful parsing entails both concrete machine checks. -/
theorem scalarGate_of_parse (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar) (hparse : ScalarParseContract layout shared)
    (s : Bytes32) (scalar : Scalar) (hs : shared.parseScalar s = some scalar) :
    scalarGate layout s = true ∧ layout.scalar scalar = s :=
  (hparse s scalar).mp hs

/-- Completeness is separate from the successful-parse implication: a gate
that accepted bytes outside the parser's image would otherwise escape it. -/
def ScalarParseComplete (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar) : Prop :=
  ∀ s, scalarGate layout s = true → ∃ scalar, shared.parseScalar s = some scalar

theorem scalarGate_iff_parse (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar) (hparse : ScalarParseContract layout shared)
    (hcomplete : ScalarParseComplete layout shared) (s : Bytes32) :
    scalarGate layout s = true ↔ ∃ scalar, shared.parseScalar s = some scalar := by
  constructor
  · exact hcomplete s
  · rintro ⟨scalar, hs⟩
    exact ((hparse s scalar).mp hs).1

/-- Decompression has the pinned Rust `Option<EdwardsPoint>` layout: a u64
0/1 tag at offset zero and the 160-byte payload at offset eight. -/
def DecompressContract (call : Vals [.ptr, .ptr] → EffectM (Vals []))
    (layout : Layout Point Scalar Result) (shared : Shared Point Scalar) : Prop :=
  ∀ (out input : Pointer) (state : GlobalState) (encoded : Bytes32), state.WF →
    SmallRange state.mem out 168 → ReadBytes state input 32 encoded →
    (Range.of out 1344).Disjoint (Range.of input 256) →
    ∃ after,
      call (args2 out input) state = .value (.nil, after) ∧
      OutputFrame state after out 168 ∧
      match shared.decompress encoded with
      | none => after.mem.readAt out 64 = 0
      | some point => after.mem.readAt out 64 = 1 ∧
          ReadBytes after (out.add 8) 160 (layout.point point)

/-- Only multiplication by eight is used by this verifier. -/
def CofactorContract (call : Vals [.ptr, .ptr, .bv 32] → EffectM (Vals []))
    (layout : Layout Point Scalar Result) : Prop :=
  ∀ (out input : Pointer) (state : GlobalState) (point : Point), state.WF →
    SmallRange state.mem out 160 → ReadBytes state input 160 (layout.point point) →
    (Range.of out 1280).Disjoint (Range.of input 1280) →
    ∃ after,
      call (.cons (.value out) (.cons (.value input) (.cons (.value 3) .nil))) state =
        .value (.nil, after) ∧
      OutputFrame state after out 160 ∧ ReadBytes after out 160 (layout.cofactor point)

/-- The two point-equality calls compare a cofactor multiple with the concrete
identity constructed by the caller. The choice byte is exactly zero or one. -/
def SmallOrderEqContract (call : Vals [.ptr, .ptr] → EffectM (Vals [.bv 8]))
    (layout : Layout Point Scalar Result) (shared : Shared Point Scalar) : Prop :=
  ∀ (point identity : Pointer) (state : GlobalState) (value : Point), state.WF →
    ReadBytes state point 160 (layout.cofactor value) →
    ReadBytes state identity 160 layout.identity →
    ∃ after,
      call (args2 point identity) state =
        .value (.cons (.value (if shared.smallOrder value then 1 else 0)) .nil, after) ∧
      ReadOnlyFrame state after

def BlackBoxContract (call : Vals [.bv 8] → EffectM (Vals [.bv 8])) : Prop :=
  ∀ (value : BitVec 8) (state : GlobalState),
    call (.cons (.value value) .nil) state = .value (.cons (.value value) .nil, state)

def ScalarReduceContract (call : Vals [.ptr, .ptr] → EffectM (Vals []))
    (layout : Layout Point Scalar Result) : Prop :=
  ∀ (out input : Pointer) (state : GlobalState) (s : Bytes32), state.WF →
    SmallRange state.mem out 32 → ReadBytes state input 32 s →
    (Range.of out 256).Disjoint (Range.of input 256) →
    ∃ after,
      call (args2 out input) state = .value (.nil, after) ∧
      OutputFrame state after out 32 ∧ ReadBytes after out 32 (layout.reduce s)

def BytesEqContract (call : Vals [.ptr, .ptr] → EffectM (Vals [.bv 8])) : Prop :=
  ∀ (left right : Pointer) (state : GlobalState) (a b : Bytes32), state.WF →
    ReadBytes state left 32 a → ReadBytes state right 32 b →
    ∃ after,
      call (args2 left right) state =
        .value (.cons (.value (if a = b then 1 else 0)) .nil, after) ∧
      ReadOnlyFrame state after

/-- The initializer's return value is not consumed by the extracted caller.
The contract therefore specifies the reloaded cache byte and its frame. -/
def CacheContract (call : Vals [] → EffectM (Vals [.bv 1])) (cache : Pointer) : Prop :=
  ∀ (state : GlobalState), state.WF → ReadBytes state cache 1 255 →
    ∃ (after : GlobalState) (returned : BitVec 1) (avx2 : Bool),
      call .nil state = .value (.cons (.value returned) .nil, after) ∧
      OutputFrame state after cache 1 ∧
      ReadBytes after cache 1 (if avx2 then 1 else 0)

/-- Both backends have this one-call contract. The frame is only the ordinary
160-byte point output; private callee stack objects may be allocated. -/
def DoubleBaseContract (call : Vals [.ptr, .ptr, .ptr, .ptr] → EffectM (Vals []))
    (layout : Layout Point Scalar Result) (doubleBase : Scalar → Point → Scalar → Result) : Prop :=
  ∀ (out hptr aptr sptr : Pointer) (state : GlobalState) (h s : Scalar) (a : Point), state.WF →
    SmallRange state.mem out 160 →
    ReadBytes state hptr 32 (layout.scalar h) →
    ReadBytes state aptr 160 (layout.point a) →
    ReadBytes state sptr 32 (layout.scalar s) →
    (Range.of out 1280).Disjoint (Range.of hptr 256) →
    (Range.of out 1280).Disjoint (Range.of aptr 1280) →
    (Range.of out 1280).Disjoint (Range.of sptr 256) →
    ∃ after encoded,
      call (args4 out hptr aptr sptr) state = .value (.nil, after) ∧
      OutputFrame state after out 160 ∧ ReadBytes after out 160 encoded ∧
      layout.result (doubleBase h a s) encoded

def CompressContract (call : Vals [.ptr, .ptr] → EffectM (Vals []))
    (layout : Layout Point Scalar Result) (compress : Result → Bytes32) : Prop :=
  ∀ (out input : Pointer) (state : GlobalState) (result : Result) (encoded : PointBytes), state.WF →
    SmallRange state.mem out 32 → ReadBytes state input 160 encoded →
    layout.result result encoded →
    (Range.of out 256).Disjoint (Range.of input 1280) →
    ∃ after,
      call (args2 out input) state = .value (.nil, after) ∧
      OutputFrame state after out 32 ∧ ReadBytes after out 32 (compress result)

/-- `bcmp` need not return one on inequality: only its zero/nonzero distinction
is observable in the pinned caller. -/
def CompareContract (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32])) : Prop :=
  ∀ (left right : Pointer) (state : GlobalState) (a b : Bytes32), state.WF →
    ReadBytes state left 32 a → ReadBytes state right 32 b →
    ∃ (after : GlobalState) (result : BitVec 32),
      call (.cons (.value left) (.cons (.value right) (.cons (.value 32) .nil))) state =
        .value (.cons (.value result) .nil, after) ∧
      ReadOnlyFrame state after ∧ (result = 0 ↔ a = b)

/-- The digest/challenge boundary is one named call. It ranges over arbitrary
message bytes and lengths within the Rust slice bound. -/
def ChallengeContract (call : Vals [.ptr, .ptr, .ptr, .ptr, .bv 64] → EffectM (Vals []))
    (layout : Layout Point Scalar Result)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar) : Prop :=
  ∀ (out key signature message : Pointer) (state : GlobalState)
    (a r : Bytes32) (msg : List (BitVec 8)), state.WF →
    SmallRange state.mem out 32 → SmallRange state.mem key 192 →
    SmallRange state.mem signature 64 → SmallRange state.mem message msg.length →
    state.mem.readAt key 256 = a → state.mem.readAt signature 256 = r →
    (∀ (i : Nat) (hi : i < msg.length),
      state.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i]) →
    msg.length < 2 ^ 63 →
    (Range.of out 256).Disjoint (Range.of key 1536) →
    (Range.of out 256).Disjoint (Range.of signature 512) →
    (Range.of out 256).Disjoint (Range.of message (8 * msg.length)) →
    ∃ after,
      call (.cons (.value out) (.cons (.value key) (.cons (.value signature)
        (.cons (.value message) (.cons (.value (BitVec.ofNat 64 msg.length)) .nil))))) state =
          .value (.nil, after) ∧
      OutputFrame state after out 32 ∧ ReadBytes after out 32 (layout.scalar (challenge r a msg))

/-- The complete named external boundary, with scalar parsing laws stated
separately so that rejected scalar encodings cannot be excluded implicitly. -/
structure PrimitiveContracts (p : Primitives) (g : Globals)
    (layout : Layout Point Scalar Result) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar) : Prop where
  challengeScalar : ChallengeContract p.challengeScalar layout challenge
  pointMulByPow2 : CofactorContract p.pointMulByPow2 layout
  pointConstantTimeEq : SmallOrderEqContract p.pointConstantTimeEq layout shared
  decompress : DecompressContract p.decompress layout shared
  blackBoxByte : BlackBoxContract p.blackBoxByte
  scalarReduce : ScalarReduceContract p.scalarReduce layout
  bytesConstantTimeEq : BytesEqContract p.bytesConstantTimeEq
  initializeAvx2Cache : CacheContract p.initializeAvx2Cache g.address1
  serialDoubleBase : DoubleBaseContract p.serialDoubleBase layout doubleBase
  avx2DoubleBase : DoubleBaseContract p.avx2DoubleBase layout doubleBase
  compressPoint : CompressContract p.compressPoint layout compress
  compareBytes : CompareContract p.compareBytes
  scalarParse : ScalarParseContract layout shared
  scalarComplete : ScalarParseComplete layout shared

end Agave.Ed25519.Verifier.Execution.Dalek
