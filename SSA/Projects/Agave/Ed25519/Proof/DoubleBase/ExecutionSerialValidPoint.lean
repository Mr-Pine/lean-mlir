import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialReturnRefinement
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorValidPoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressValidPointLayout

/-! Exact verifier ABI output for the serial return block. The ValidPoint
retains the twenty actual output words, including noncanonical limb choices. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (readPoint)
open Verifier.Execution

def payloadWords (v : BitVec 1280) : Key.PointWords :=
  ⟨fun i => v.extractLsb' (64 * i.val) 64,
   fun i => v.extractLsb' (320 + 64 * i.val) 64,
   fun i => v.extractLsb' (640 + 64 * i.val) 64,
   fun i => v.extractLsb' (960 + 64 * i.val) 64⟩

theorem payloadWords_bytes (v : BitVec 1280) : (payloadWords v).bytes = v := by
  rw [Encoding.Decompress.Valid.pointPayload_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [payloadWords, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    Fin.val_zero, Fin.val_one, Fin.val_two]
  grind only

def readKeyWords (s : GlobalState) (p : Pointer) : Key.PointWords :=
  ⟨SerialFieldMul.readLimbs s p, SerialFieldMul.readLimbs s (p.add 40),
   SerialFieldMul.readLimbs s (p.add 80), SerialFieldMul.readLimbs s (p.add 120)⟩

theorem readLimbs_payloadWords (s : GlobalState) (p : Pointer)
    (h : Buffer s.mem p 160) (c : Fin 4) (i : Fin 5) :
    SerialFieldMul.readLimbs s (p.add (BitVec.ofNat 64 (40*c.val))) i =
      (s.mem.readAt p 1280).extractLsb' (320*c.val + 64*i.val) 64 := by
  have hk : 40*c.val + 8*i.val < 2^64 := by omega
  have hbits : (BitVec.ofNat 64 (40*c.val + 8*i.val)).toNat * 8 + 64 ≤ 1280 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
    omega
  have he := MemoryState.readAt_add_of_readAt h.fits
    (Reduce64.Execution.SmallRange.no_wrap h (k := 40*c.val + 8*i.val) (by omega)) hbits rfl
  have hoff : (40*c.val + 8*i.val)*8 = 320*c.val + 64*i.val := by omega
  simpa only [SerialFieldMul.readLimbs, Pointer.add_add, ← BitVec.ofNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, hoff] using he

theorem readKeyWords_payload (s : GlobalState) (p : Pointer)
    (h : Buffer s.mem p 160) : readKeyWords s p = payloadWords (s.mem.readAt p 1280) := by
  unfold readKeyWords payloadWords
  congr 1 <;> funext i
  · simpa [readKeyWords, payloadWords] using readLimbs_payloadWords s p h 0 i
  · simpa [readKeyWords, payloadWords] using readLimbs_payloadWords s p h 1 i
  · simpa [readKeyWords, payloadWords] using readLimbs_payloadWords s p h 2 i
  · simpa [readKeyWords, payloadWords] using readLimbs_payloadWords s p h 3 i

theorem readKeyWords_bytes (s : GlobalState) (p : Pointer)
    (h : Buffer s.mem p 160) : (readKeyWords s p).bytes = s.mem.readAt p 1280 := by
  rw [readKeyWords_payload s p h, payloadWords_bytes]

theorem readKeyWords_unsigned (s : GlobalState) (p : Pointer) :
    SerialPoint.unsignedPoint (SmallOrder.keyWordPoint (readKeyWords s p)) =
      readPoint s p := rfl

/-- The output value is built from the actual memory words, not from a
chosen canonical representative of the result curve point. -/
def readValidPoint (s : GlobalState) (p : Pointer) (V : GroupPoint)
    (ht : SerialPoint.PointTight (readPoint s p))
    (hr : Tables.Represents (SerialPoint.pointValue (readPoint s p)) V) : ValidPoint where
  words := readKeyWords s p
  curve := V
  tightX := ht.1
  tightY := ht.2.1
  tightZ := ht.2.2.1
  tightT := ht.2.2.2
  represents := (SmallOrder.key_represents_iff _ _).mpr hr

/-- Concrete serial output-block correctness at the verifier's ValidPoint
interface, with exact bytes and the full 160-byte write frame. -/
theorem serial_return_run_validPoint (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (hsquare : p.call8 = Encoding.Decompress.Execution.Pow2k.program.call)
    (E : ⟪serialKernel.Γ⟫) (out projective : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : Buffer s.mem out 160) (hp : Buffer s.mem projective 120)
    (hne : out.id ≠ projective.id) (harg : E.read (%arg0) = .value out)
    (hbound : SerialPoint.PointBounded (SerialContracts.readProjective s projective))
    (V : GroupPoint) (hpoint : ProjectiveRepresents (SerialContracts.readProjective s projective) V) :
    ∃ P : ValidPoint,
      (serialKernel p g).runFrom (serialReturnInput E projective) 34 s =
        .value (.nil, serialReturnState s out projective) ∧
      SerialContracts.WritesOnly out 160 s (serialReturnState s out projective) ∧
      P.curve = V ∧
      Dalek.ReadBytes (serialReturnState s out projective) out 160 P.bytes := by
  obtain ⟨hrun, hframe, ht, hr⟩ := serial_return_run_represents p g hfield hsquare
    E out projective s hwf hout hp hne harg hbound V hpoint
  refine ⟨readValidPoint _ out V ht hr, hrun, hframe, rfl, hframe.smallRange hout, ?_⟩
  exact (readKeyWords_bytes _ out (hframe.smallRange hout)).symm

end Agave.Ed25519.DoubleBase.RIR
