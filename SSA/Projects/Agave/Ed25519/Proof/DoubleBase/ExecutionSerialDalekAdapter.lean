import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialWhole
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointRepresentation

/-! Direct four-pointer verifier ABI for the linked serial double-base body.
The result retains actual machine bytes. The only residual execution premise
is the concrete constructor's contextual contract. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open SerialContracts (readPoint)
open Verifier Verifier.Execution
set_option maxRecDepth 10000

theorem serial_readKeyWords_of_validPoint (s : GlobalState) (q : Pointer) (P : ValidPoint)
    (hp : Dalek.ReadBytes s q 160 P.bytes) : readKeyWords s q = P.words := by
  have hx : SerialFieldMul.readLimbs s q = P.words.X := by
    simpa [SmallOrder.coordinates] using SmallOrder.read_coordinate s q P.words hp 0
  have hy : SerialFieldMul.readLimbs s (q.add 40) = P.words.Y := by
    simpa [SmallOrder.coordinates] using SmallOrder.read_coordinate s q P.words hp 1
  have hz : SerialFieldMul.readLimbs s (q.add 80) = P.words.Z := by
    simpa [SmallOrder.coordinates] using SmallOrder.read_coordinate s q P.words hp 2
  have ht : SerialFieldMul.readLimbs s (q.add 120) = P.words.T := by
    simpa [SmallOrder.coordinates] using SmallOrder.read_coordinate s q P.words hp 3
  unfold readKeyWords
  rw [hx, hy, hz, ht]

theorem serial_validPoint_readPoint (s : GlobalState) (q : Pointer) (P : ValidPoint)
    (hp : Dalek.ReadBytes s q 160 P.bytes) :
    readPoint s q = SerialPoint.unsignedPoint (SmallOrder.keyWordPoint P.words) := by
  rw [← readKeyWords_unsigned, serial_readKeyWords_of_validPoint s q P hp]

theorem serial_validPoint_input_tight (s : GlobalState) (q : Pointer) (P : ValidPoint)
    (hp : Dalek.ReadBytes s q 160 P.bytes) : SerialPoint.PointTight (readPoint s q) := by
  rw [serial_validPoint_readPoint s q P hp]
  exact ⟨P.tightX, P.tightY, P.tightZ, P.tightT⟩

theorem serial_validPoint_input_represents (s : GlobalState) (q : Pointer) (P : ValidPoint)
    (hp : Dalek.ReadBytes s q 160 P.bytes) :
    Tables.Represents (SerialPoint.pointValue (readPoint s q)) P.curve := by
  rw [serial_validPoint_readPoint s q P hp]
  exact (SmallOrder.key_represents_iff _ _).mp P.represents

/-- Whole linked serial call at the actual Dalek input/output interface.
The globals are initial memory facts. Neither point arithmetic nor the
ladder, output bytes, result representation or frame is a premise. -/
theorem serialLinked_dalek_call (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (htable : Tables.SerialConstructorContext.ContextualTableContract d2
      (serialLinkedPrimitives d2 panic).call0)
    (out hptr aptr sptr : Pointer) (state : GlobalState)
    (hval sval : CanonicalScalar) (aval : ValidPoint)
    (hwf : state.WF) (hout : NAF.Memory.Buffer state.mem out 160)
    (hh : Dalek.ReadBytes state hptr 32 (CanonicalScalar.encode hval))
    (hA : Dalek.ReadBytes state aptr 160 aval.bytes)
    (hs : Dalek.ReadBytes state sptr 32 (CanonicalScalar.encode sval))
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 state)
    (hg : SerialContracts.GlobalsReady g state) :
    ∃ after encoded,
      (serialLinkedKernel g d2 panic).call (Dalek.args4 out hptr aptr sptr) state =
        .value (.nil, after) ∧
      Dalek.OutputFrame state after out 160 ∧ Dalek.ReadBytes after out 160 encoded ∧
      ValidPoint.ResultRepresents (ValidPoint.doubleBase hval aval sval) encoded := by
  let i : SerialContracts.Invocation := ⟨out, hptr, aptr, sptr⟩
  have hHbound : (CanonicalScalar.encode hval).toNat < 2^255 := by
    rw [CanonicalScalar.encode_toNat]
    exact CanonicalScalar.bound hval
  have hSbound : (CanonicalScalar.encode sval).toNat < 2^255 := by
    rw [CanonicalScalar.encode_toNat]
    exact CanonicalScalar.bound sval
  have hi : SerialContracts.InputState i state (CanonicalScalar.encode hval)
      (CanonicalScalar.encode sval) (readPoint state aptr) :=
    ⟨hwf, hout, hh.1, hs.1, hA.1, hh.2, hs.2, hHbound, hSbound, rfl,
      serial_validPoint_input_tight state aptr aval hA⟩
  obtain ⟨P, after, hcall, hframe, hcurve, hbytes⟩ :=
    serialLinked_call_validPoint g d2 panic htable i state _ _ _ aval.curve hi
      (serial_validPoint_input_represents state aptr aval hA) hd2 hg
  refine ⟨after, P.bytes, hcall, hframe, hbytes, P, ?_, rfl⟩
  change P.curve = hval.val • aval.curve + sval.val • Tables.baseGroup
  simpa only [CanonicalScalar.encode_toNat, natCast_zsmul] using hcurve

end Agave.Ed25519.DoubleBase.RIR
