import SSA.Projects.Agave.Ed25519.Proof.Tables.ConstructorMemory
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorContext
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! The actual final 1280-byte memcpy transfers all eight physical Niels
records and has the exact output-only caller frame. -/
namespace Agave.Ed25519.Tables.SerialConstructorReturn
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open DoubleBase.SerialContracts
local instance : Fact (Nat.Prime SerialFieldMul.modulus) := ⟨prime_p⟩

def copyState (s : GlobalState) (out table : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt out (s.mem.readAt table 10240)}

theorem copyState_writesOnly (s : GlobalState) (out table : Pointer) (hwf : s.WF) :
    WritesOnly out 1280 s (copyState s out table) := by
  refine ⟨hwf.storeAt, le_refl _, ?_, ?_⟩
  · intro id
    exact SerialPoint.Execution.storeAt_allocationShape s.mem out _ id
  · intro q bits hd
    exact MemoryState.readAt_storeAt_disjoint hd.symm _

/-- The record readback uses the source table bytes, including all twenty
field words and the physical cache-coordinate permutation. -/
theorem copyState_readCached (s : GlobalState) (out table : Pointer)
    (hout : SmallRange s.mem out 1280) (htable : SmallRange s.mem table 1280)
    (k : Fin 8) :
    readCached (copyState s out table) (out.add (BitVec.ofNat 64 (160*k.val))) =
      readCached s (table.add (BitVec.ofNat 64 (160*k.val))) := by
  have hword (c : Fin 4) (i : Fin 5) :
      (copyState s out table).mem.readAt
          (out.add (BitVec.ofNat 64 (160*k.val + 40*c.val + 8*i.val))) 64 =
        s.mem.readAt (table.add (BitVec.ofNat 64 (160*k.val + 40*c.val + 8*i.val))) 64 := by
    have hk : 160*k.val + 40*c.val + 8*i.val < 2^64 := by omega
    have hbits : (BitVec.ofNat 64 (160*k.val + 40*c.val + 8*i.val)).toNat * 8 + 64 ≤ 10240 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
      omega
    unfold copyState
    rw [MemoryState.readAt_storeAt_add hout.fits
      (hout.no_wrap (k := 160*k.val + 40*c.val + 8*i.val) (by omega)) hbits]
    exact (MemoryState.readAt_add_of_readAt htable.fits
      (htable.no_wrap (k := 160*k.val + 40*c.val + 8*i.val) (by omega)) hbits rfl).symm
  have hfield (c : Fin 4) :
      readField (copyState s out table)
          (out.add (BitVec.ofNat 64 (160*k.val + 40*c.val))) =
        readField s (table.add (BitVec.ofNat 64 (160*k.val + 40*c.val))) := by
    funext i
    simp only [readField, SerialFieldMul.unsigned, SerialFieldMul.readLimbs,
      Pointer.add_add, ← BitVec.ofNat_add, hword]
  apply PointArithmetic.Extended.ext
  · simpa [readCached, Pointer.add_add, BitVec.ofNat_add] using hfield 1
  · simpa [readCached, Pointer.add_add, BitVec.ofNat_add] using hfield 0
  · simpa [readCached, Pointer.add_add, BitVec.ofNat_add] using hfield 2
  · simpa [readCached, Pointer.add_add, BitVec.ofNat_add] using hfield 3

/-- No table-execution premise occurs here: this executes the real return
block and transports the already established scratch-table invariant. -/
theorem return_contract (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out table : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 1280) (htable : SmallRange s.mem table 1280)
    (hne : out.id ≠ table.id) (harg : E.read (%arg0) = .value out)
    (A : SerialPoint.FieldPoint)
    (hentries : ∀ k : Fin 8,
      SerialPoint.PointBounded (readCached s (table.add (BitVec.ofNat 64 (160*k.val)))) ∧
      SerialPoint.pointValue (readCached s (table.add (BitVec.ofNat 64 (160*k.val)))) =
        PointArithmetic.serialCache (K := ZMod SerialFieldMul.modulus) _root_.Ed25519.d (serialWidth5 (K := ZMod SerialFieldMul.modulus) _root_.Ed25519.d A k)) :
    let final := copyState s out table
    (SerialConstructor.kernel p g).runFrom (ConstructorMemory.serialReturnInput E table) 1 s =
      .value (.nil, final) ∧ WritesOnly out 1280 s final ∧
      ∀ k : Fin 8,
        SerialPoint.PointBounded (readCached final (out.add (BitVec.ofNat 64 (160*k.val)))) ∧
        SerialPoint.pointValue (readCached final (out.add (BitVec.ofNat 64 (160*k.val)))) =
          PointArithmetic.serialCache (K := ZMod SerialFieldMul.modulus) _root_.Ed25519.d (serialWidth5 (K := ZMod SerialFieldMul.modulus) _root_.Ed25519.d A k) := by
  refine ⟨ConstructorMemory.serial_return_run p g E s out table hout htable hne harg,
    copyState_writesOnly s out table hwf, ?_⟩
  intro k
  rw [copyState_readCached s out table hout htable k]
  exact hentries k

end Agave.Ed25519.Tables.SerialConstructorReturn
