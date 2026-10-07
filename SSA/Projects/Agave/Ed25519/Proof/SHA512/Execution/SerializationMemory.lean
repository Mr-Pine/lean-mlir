import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Serialization
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ByteOrder

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge
open Agave.Ed25519.SHA512

/-- Later word stores preserve the already serialized digest words. -/
theorem writeWords_read (m : MemoryState) (dst : Pointer) (words : Nat → BitVec 64)
    (n i : Nat) (hd : SmallRange m dst 64) (hn : n ≤ 8) (hi : i < n) :
    (writeWords m dst words n).readAt (dst.add (BitVec.ofNat 64 (8 * i))) 64 =
      swapBytes (words i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hl := writeWords_live m dst dst words n 64 hd
    by_cases heq : i = n
    · subst i
      exact MemoryState.readAt_storeAt_self
        (hl.fits_add (k := 8 * n) (count := 8) (by omega)) _
    · have hil : i < n := by omega
      have hdis : (Range.of (dst.add (BitVec.ofNat 64 (8 * n))) 64).Disjoint
          (Range.of (dst.add (BitVec.ofNat 64 (8 * i))) 64) := by
        exact smallRange_disjoint_offsets hl
          (i := 8 * n) (countI := 8) (j := 8 * i) (countJ := 8)
          (by omega) (by omega) (Or.inr (by omega))
      rw [writeWords, MemoryState.readAt_storeAt_disjoint hdis]
      exact ih (by omega) hil

/-- Clearing the length byte leaves every native chaining word unchanged. -/
theorem chainWord_eq (s : GlobalState) (ctx : Pointer) (i : Nat)
    (hc : SmallRange s.mem ctx 208) (hi : i < 8) :
    chainWord s ctx i = (s.mem.readAt (ctx.add 128#64) 512).extractLsb' (64 * i) 64 := by
  have hdis : (Range.of (ctx.add 127#64) 8).Disjoint
      (Range.of (ctx.add (BitVec.ofNat 64 (128 + 8 * i))) 64) :=
    smallRange_disjoint_offsets hc (i := 127) (countI := 1)
      (j := 128 + 8 * i) (countJ := 8) (by decide) (by omega) (Or.inl (by omega))
  unfold chainWord clearCount
  rw [MemoryState.readAt_storeAt_disjoint hdis]
  have hl : SmallRange s.mem (ctx.add 128#64) 64 := smallRange_add hc (by decide)
  have hoff : (BitVec.ofNat 64 (8 * i)).toNat = 8 * i :=
    Nat.mod_eq_of_lt (by omega)
  have hr := MemoryState.readAt_add_of_readAt hl.fits (hl.no_wrap (k := 8 * i) (by omega))
    (w := 64) (by rw [hoff]; omega) rfl
  rw [hoff] at hr
  simpa [Pointer.add_add, ← BitVec.ofNat_add, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hr

theorem writeWords_frame (m : MemoryState) (dst : Pointer) (words : Nat → BitVec 64)
    (n mark : Nat) (hd : mark ≤ dst.id.id) :
    (writeWords m dst words n).eraseFrom mark = m.eraseFrom mark := by
  induction n with
  | zero => rfl
  | succ n ih => exact erase_internal_store _ _ _ _ _ ih hd

theorem serializedState_frame (s : GlobalState) (ctx dst : Pointer) (mark : Nat)
    (hc : mark ≤ ctx.id.id) (hd : mark ≤ dst.id.id) :
    (serializedState s ctx dst).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  unfold serializedState
  rw [writeWords_frame _ _ _ _ _ hd]
  exact erase_internal_store _ _ _ _ _ rfl hc

/-- All eight stored native words recover the precise common serializer. -/
theorem serialized_readback (s : GlobalState) (ctx dst : Pointer)
    (hc : SmallRange s.mem ctx 208) (hd : SmallRange s.mem dst 64) :
    (serializedState s ctx dst).mem.readAt dst 512 =
      serialize (s.mem.readAt (ctx.add 128#64) 512) := by
  have hl : SmallRange (serializedState s ctx dst).mem dst 64 :=
    writeWords_live _ _ _ _ _ _ (hd.storeAt _ _)
  have hword (i : Nat) (hi : i < 8) :
      ((serializedState s ctx dst).mem.readAt dst 512).extractLsb' (64 * i) 64 =
        (serialize (s.mem.readAt (ctx.add 128#64) 512)).extractLsb' (64 * i) 64 := by
    have hoff : (BitVec.ofNat 64 (8 * i)).toNat = 8 * i :=
      Nat.mod_eq_of_lt (by omega)
    have hr := MemoryState.readAt_add_of_readAt hl.fits
      (hl.no_wrap (k := 8 * i) (by omega)) (w := 64) (by rw [hoff]; omega) rfl
    have hw := writeWords_read (clearCount s ctx).mem dst (chainWord s ctx) 8 i
      (hd.storeAt _ _) (by decide) hi
    rw [chainWord_eq s ctx i hc hi] at hw
    rw [serialize_word _ i hi]
    have hr' : (serializedState s ctx dst).mem.readAt (dst.add (BitVec.ofNat 64 (8 * i))) 64 =
        ((serializedState s ctx dst).mem.readAt dst 512).extractLsb' (64 * i) 64 := by
      rw [hoff] at hr
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hr
    exact hr'.symm.trans hw
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hmod : j % 64 < 64 := Nat.mod_lt _ (by decide)
  have hpos : 64 * (j / 64) + j % 64 = j := by omega
  have h := congrArg (fun word : BitVec 64 => word.getLsbD (j % 64))
    (hword (j / 64) (by omega))
  simpa [BitVec.getLsbD_extractLsb', hmod, hpos] using h

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
