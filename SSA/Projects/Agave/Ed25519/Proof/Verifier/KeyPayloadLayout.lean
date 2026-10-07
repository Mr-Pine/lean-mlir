import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionContracts
import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionNegation
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory
import SSA.Projects.Agave.Ed25519.Bridge.Encoding

/-!
Exact readback of the constructor's 160-byte extended-coordinate payload.
This separates byte layout from field interpretation: field equality alone
cannot identify the noncanonical limb representation with a chosen `Layout.point`.
-/
namespace Agave.Ed25519.Verifier.Execution.Key
open LeanMLIR.RIR
open _root_.Ed25519
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

/-- Concrete extended-coordinate packing, in the constructor's store order.
X and T each comprise a scalar limb and two two-limb vectors; Y and Z are
unmodified 40-byte copies. -/
def pointPayload (x t : Words) (y z : BitVec 320) : BitVec 1280 :=
  let v := Memory.spliceBits (0#1280) 320 y
  let v := Memory.spliceBits v 640 z
  let v := Memory.spliceBits v 0 (x 0)
  let v := Memory.spliceBits v 64 (BitVec.packLanes #v[x 1, x 2])
  let v := Memory.spliceBits v 192 (BitVec.packLanes #v[x 3, x 4])
  let v := Memory.spliceBits v 960 (t 0)
  let v := Memory.spliceBits v 1024 (BitVec.packLanes #v[t 1, t 2])
  Memory.spliceBits v 1152 (BitVec.packLanes #v[t 3, t 4])

private def fullPayload (old : BitVec 1600) (a : BitVec 256)
    (x t : Words) (y z : BitVec 320) : BitVec 1600 :=
  let v := Memory.spliceBits old 640 y
  let v := Memory.spliceBits v 960 z
  let v := Memory.spliceBits v 64 a
  let v := Memory.spliceBits v 320 (x 0)
  let v := Memory.spliceBits v 384 (BitVec.packLanes #v[x 1, x 2])
  let v := Memory.spliceBits v 512 (BitVec.packLanes #v[x 3, x 4])
  let v := Memory.spliceBits v 1280 (t 0)
  let v := Memory.spliceBits v 1344 (BitVec.packLanes #v[t 1, t 2])
  Memory.spliceBits v 1472 (BitVec.packLanes #v[t 3, t 4])

private theorem fullPayload_extract (old : BitVec 1600) (a : BitVec 256)
    (x t : Words) (y z : BitVec 320) :
    (fullPayload old a x t y z).extractLsb' 320 1280 = pointPayload x t y z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fullPayload, pointPayload, BitVec.getLsbD_extractLsb', Memory.getLsbD_spliceBits]
  grind

/-- Readback is independent of the old output allocation, the copied key
bytes, and every decoder byte outside Y/Z. No arithmetic bounds are needed. -/
theorem payload_point_readback (s : GlobalState) (out opt bytes : Pointer) (x t : Words)
    (h : SmallRange s.mem out 200) :
    (payloadState s out opt bytes x t).mem.readAt (out.add 40#64) 1280 =
      pointPayload (negResult x) (negResult t)
        (s.mem.readAt (opt.add 48#64) 320) (s.mem.readAt (opt.add 88#64) 320) := by
  have hstore (m : MemoryState) (hm : Fits m out 1600) (k : Nat) (w : Nat)
      (hk : k ≤ 200) (hw : k * 8 + w ≤ 1600) (v : BitVec w) :
      (m.storeAt (out.add (BitVec.ofNat 64 k)) v).readAt out 1600 =
        Memory.spliceBits (m.readAt out 1600) (k * 8) v := by
    have hk64 : k < 2^64 := by omega
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] using
      MemoryState.readAt_add_storeAt hm (h.no_wrap hk)
        (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] using hw) v
  have hall : (payloadState s out opt bytes x t).mem.readAt out 1600 =
      fullPayload (s.mem.readAt out 1600) (s.mem.readAt bytes 256)
        (negResult x) (negResult t) (s.mem.readAt (opt.add 48#64) 320)
          (s.mem.readAt (opt.add 88#64) 320) := by
    unfold payloadState copyYZ fullPayload
    simp only
    rw [hstore _ h.fits.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt 184 128 (by decide) (by decide),
      hstore _ h.fits.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt 168 128 (by decide) (by decide),
      hstore _ h.fits.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt 160 64 (by decide) (by decide),
      hstore _ h.fits.storeAt.storeAt.storeAt.storeAt.storeAt 64 128 (by decide) (by decide),
      hstore _ h.fits.storeAt.storeAt.storeAt.storeAt 48 128 (by decide) (by decide),
      hstore _ h.fits.storeAt.storeAt.storeAt 40 64 (by decide) (by decide),
      hstore _ h.fits.storeAt.storeAt 8 256 (by decide) (by decide),
      hstore _ h.fits.storeAt 120 320 (by decide) (by decide),
      hstore _ h.fits 80 320 (by decide) (by decide)]
  exact (MemoryState.readAt_add_of_readAt (payload_range h).fits
    (h.no_wrap (k := 40) (by decide)) (by decide) hall).trans
      (fullPayload_extract _ _ _ _ _ _)

/-- The Result tag and call-frame erasure preserve the concrete payload. -/
theorem returned_point_readback (initial decoded : GlobalState) (out bytes : Pointer)
    (x t : Words) (h : SmallRange decoded.mem out 200)
    (hcaller : out.id.id < initial.alloc.nextFreeBlock) :
    (returnedState initial decoded out bytes x t true).mem.readAt (out.add 40#64) 1280 =
      pointPayload (negResult x) (negResult t)
        (decoded.mem.readAt ((optionSlot initial).add 48#64) 320)
        (decoded.mem.readAt ((optionSlot initial).add 88#64) 320) := by
  have hoff := Pointer.offsetInBits_add (h.no_wrap (k := 40) (by decide))
  have hd : (Range.of out 8).Disjoint (Range.of (out.add 40#64) 1280) := by
    simp only [Range.Disjoint, Range.of, hoff]
    right; left; norm_num
  change (((payloadState decoded out (optionSlot initial) bytes x t).mem.storeAt out (0#8)).eraseFrom
    initial.alloc.nextFreeBlock).readAt (out.add 40#64) 1280 = _
  rw [erase_read _ (out.add 40#64) _ _ hcaller, MemoryState.readAt_storeAt_disjoint hd]
  exact payload_point_readback _ _ _ _ _ _ h

/-- Explicit limb representatives retain the noncanonical information lost
when passing to a mathematical curve point. -/
structure PointWords where
  X : Words
  Y : Words
  Z : Words
  T : Words

def coordinatePayload (x : Words) : BitVec 320 :=
  Memory.spliceBits (Memory.spliceBits (Memory.spliceBits (0#320) 0 (x 0))
    64 (BitVec.packLanes #v[x 1, x 2])) 192 (BitVec.packLanes #v[x 3, x 4])

def PointWords.bytes (P : PointWords) : BitVec 1280 :=
  pointPayload P.X P.T (coordinatePayload P.Y) (coordinatePayload P.Z)

def PointWords.negate (P : PointWords) : PointWords :=
  ⟨negResult P.X, P.Y, P.Z, negResult P.T⟩

/-- A concrete Dalek point layout, leaving unrelated scalar/result encodings
as parameters. No choice of canonical field representatives is hidden here. -/
def limbLayout (base : Dalek.Layout PointWords Scalar Result) :
    Dalek.Layout PointWords Scalar Result :=
  { base with point := PointWords.bytes }

def curveValue (x : Words) : ZMod _root_.p :=
  SerialFieldMul.decode (SerialFieldMul.unsigned x)

theorem curveValue_negResult (x : Words)
    (hx : SerialFieldMul.Bounded (SerialFieldMul.unsigned x)) :
    curveValue (negResult x) = -curveValue x := by
  have h := negResult_value x hx
  have hp : SerialFieldMul.modulus = _root_.p := by decide
  unfold SerialPoint.value at h
  rw [hp] at h
  exact h

/-- Standard homogeneous extended-coordinate interpretation. -/
def PointWords.Represents (P : PointWords) (A : Bridge.CurvePoint) : Prop :=
  let v := curveValue
  v P.Z ≠ 0 ∧ v P.X = A.x * v P.Z ∧ v P.Y = A.y * v P.Z ∧
    v P.T = A.x * A.y * v P.Z

/-- The exact word operation used in the concrete layout represents group
negation, for every curve point including torsion and zero coordinates. -/
theorem PointWords.negate_represents (P : PointWords) (A : Bridge.CurvePoint)
    (h : P.Represents A)
    (hx : SerialFieldMul.Bounded (SerialFieldMul.unsigned P.X))
    (ht : SerialFieldMul.Bounded (SerialFieldMul.unsigned P.T)) :
    P.negate.Represents (-A) := by
  rcases h with ⟨hz, hX, hY, hT⟩
  refine ⟨hz, ?_, ?_, ?_⟩
  · change curveValue (negResult P.X) = _
    rw [curveValue_negResult _ hx, hX]
    simp [PointWords.negate, Edwards.Point.neg_x]
    rfl
  · simpa [PointWords.negate, Edwards.Point.neg_y] using hY
  · change curveValue (negResult P.T) = _
    rw [curveValue_negResult _ ht, hT]
    simp [PointWords.negate, Edwards.Point.neg_x, Edwards.Point.neg_y]
    rfl

/-- With this concrete layout the decoder needs only identify its four raw
coordinate arrays. There is no assumed cached-output equality. -/
theorem call_concrete_cached_point (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer) (P : PointWords)
    (base : Dalek.Layout PointWords Scalar Result)
    (h : DecoderCall p initial decoded out bytes P.X P.T true)
    (hy : decoded.mem.readAt ((optionSlot initial).add 48#64) 320 = coordinatePayload P.Y)
    (hz : decoded.mem.readAt ((optionSlot initial).add 88#64) 320 = coordinatePayload P.Z)
    (hcaller : out.id.id < initial.alloc.nextFreeBlock) :
    (program p).call (args out bytes) initial =
      .value (.nil, returnedState initial decoded out bytes P.X P.T true) ∧
    (returnedState initial decoded out bytes P.X P.T true).mem.readAt (out.add 40#64) 1280 =
      (limbLayout base).point P.negate := by
  refine ⟨call_of_decoder _ _ _ _ _ _ _ _ h, ?_⟩
  rw [returned_point_readback _ _ _ _ _ _ h.outputRange hcaller, hy, hz]
  rfl

/-- Direct form of the cached-minus-A field consumed by Dalek. This concrete
shared representation uses the proved word-level negation above. -/
theorem call_shared_cached_point (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer) (A : PointWords)
    (base : Dalek.Layout PointWords Scalar Result) (shared : Shared PointWords Scalar)
    (hnegate : shared.negate = PointWords.negate)
    (h : DecoderCall p initial decoded out bytes A.X A.T true)
    (hy : decoded.mem.readAt ((optionSlot initial).add 48#64) 320 = coordinatePayload A.Y)
    (hz : decoded.mem.readAt ((optionSlot initial).add 88#64) 320 = coordinatePayload A.Z)
    (hcaller : out.id.id < initial.alloc.nextFreeBlock) :
    (program p).call (args out bytes) initial =
      .value (.nil, returnedState initial decoded out bytes A.X A.T true) ∧
    (returnedState initial decoded out bytes A.X A.T true).mem.readAt (out.add 40#64) 1280 =
      (limbLayout base).point (shared.negate A) := by
  rw [hnegate]
  exact call_concrete_cached_point p initial decoded out bytes A base h hy hz hcaller

/-- Additional decoder data required to interpret the byte payload in a
functional Dalek layout. The exact representative equation is intentional:
field congruence does not fix noncanonical limb bytes. -/
def PayloadLayout (layout : Dalek.Layout Point Scalar Result)
    (decoded : GlobalState) (opt : Pointer) (x t : Words) (minusA : Point) : Prop :=
  ∃ y z : BitVec 320,
    decoded.mem.readAt (opt.add 48#64) 320 = y ∧
    decoded.mem.readAt (opt.add 88#64) 320 = z ∧
    pointPayload (negResult x) (negResult t) y z = layout.point minusA

/-- The constructor's cached point follows from its actual decoder call and
an explicit choice of the decoder's limb representative; execution and output
memory equalities are conclusions, not additional hypotheses. -/
theorem call_cached_point (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer) (x t : Words)
    (layout : Dalek.Layout Point Scalar Result) (minusA : Point)
    (h : DecoderCall p initial decoded out bytes x t true)
    (hl : PayloadLayout layout decoded (optionSlot initial) x t minusA)
    (hcaller : out.id.id < initial.alloc.nextFreeBlock) :
    (program p).call (args out bytes) initial =
      .value (.nil, returnedState initial decoded out bytes x t true) ∧
    (returnedState initial decoded out bytes x t true).mem.readAt (out.add 40#64) 1280 =
      layout.point minusA := by
  refine ⟨call_of_decoder _ _ _ _ _ _ _ _ h, ?_⟩
  obtain ⟨y, z, hy, hz, hp⟩ := hl
  rw [returned_point_readback _ _ _ _ _ _ h.outputRange hcaller, hy, hz]
  exact hp

end Agave.Ed25519.Verifier.Execution.Key
