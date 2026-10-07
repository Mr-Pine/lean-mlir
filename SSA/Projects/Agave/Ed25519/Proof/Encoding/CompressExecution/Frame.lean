import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Calls
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! Memory effects of each lower field invocation, followed by the actual
compressor call's frame erasure. These premises concern individual callees;
there is no assumed frame or result for the complete compressor. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul (storeLimbs)

structure FieldResults where
  powFirst : Field.Serial
  powSecond : Field.Serial
  squared : Field.Serial
  inverse : Field.Serial
  affineX : Field.Serial
  affineY : Field.Serial

/-- The five exact destination writes made by the lower field calls. The
two-result pow22501 call writes two adjacent five-limb values. The black-box
callee preserves memory but may advance the allocation counter. -/
structure FieldMemory (initial afterBlack : GlobalState) (states : FieldStates)
    (words : FieldResults) : Prop where
  pow22501 : states.powed.mem = storeLimbs
    (storeLimbs (scratchState initial 6).mem (scratch initial 1) words.powFirst)
    ((scratch initial 1).add 40) words.powSecond
  pow2k : states.squared.mem =
    storeLimbs (copySecond initial states.powed).mem (scratch initial 0) words.squared
  inverse : states.inverted.mem =
    storeLimbs states.squared.mem (scratch initial 4) words.inverse
  xMul : states.affineX.mem =
    storeLimbs states.inverted.mem (scratch initial 5) words.affineX
  yMul : states.affineXY.mem =
    storeLimbs states.affineX.mem ((scratch initial 5).add 40) words.affineY
  blackBox : afterBlack.mem = states.affineXY.mem
  counter : initial.alloc.nextFreeBlock ≤ afterBlack.alloc.nextFreeBlock

theorem scratchState_counter (s : GlobalState) (n : Nat) :
    (scratchState s n).alloc.nextFreeBlock = s.alloc.nextFreeBlock + n := by
  induction n with
  | zero => simp [scratchState]
  | succ n ih => simp [scratchState, GlobalState.alloca, ih, Nat.add_assoc]

theorem scratch_fresh (s : GlobalState) (n : Nat) :
    s.alloc.nextFreeBlock ≤ (scratch s n).id.id := by
  simp [scratch, GlobalState.allocaPtr, scratchState_counter]

theorem scratchState_erase (s : GlobalState) (n : Nat) (hwf : s.WF) :
    (scratchState s n).mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  induction n with
  | zero => exact hwf.eraseFrom
  | succ n ih =>
    rw [scratchState, GlobalState.eraseFrom_alloca_of_le]
    · exact ih
    · simp [scratchState_counter]

theorem erase_storeLimbs_fresh (m : MemoryState) (p : Pointer) (v : Field.Serial)
    (n : Nat) (hp : n ≤ p.id.id) :
    (storeLimbs m p v).eraseFrom n = m.eraseFrom n := by
  have hpa (off : BitVec 64) : n ≤ (p.add off).id.id := hp
  simp only [storeLimbs, MemoryState.eraseFrom_storeAt]
  simp only [MemoryState.storeAt_eraseFrom_of_le hp,
    MemoryState.storeAt_eraseFrom_of_le (hpa 8),
    MemoryState.storeAt_eraseFrom_of_le (hpa 16),
    MemoryState.storeAt_eraseFrom_of_le (hpa 24),
    MemoryState.storeAt_eraseFrom_of_le (hpa 32)]

/-- All intermediate writes are into the six freshly allocated objects.
Frame erasure therefore restores the complete original memory, not only
the reads from live caller pointers. -/
theorem FieldMemory.erase (mem : FieldMemory initial afterBlack states words)
    (hwf : initial.WF) :
    afterBlack.mem.eraseFrom initial.alloc.nextFreeBlock = initial.mem := by
  rw [mem.blackBox, mem.yMul,
    erase_storeLimbs_fresh _ _ _ _ (by simpa using scratch_fresh initial 5),
    mem.xMul, erase_storeLimbs_fresh _ _ _ _ (scratch_fresh initial 5),
    mem.inverse, erase_storeLimbs_fresh _ _ _ _ (scratch_fresh initial 4),
    mem.pow2k, erase_storeLimbs_fresh _ _ _ _ (scratch_fresh initial 0)]
  simp only [copySecond, copyFirst, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (scratch_fresh initial 2),
    MemoryState.storeAt_eraseFrom_of_le (scratch_fresh initial 3)]
  rw [mem.pow22501,
    erase_storeLimbs_fresh _ _ _ _ (by simpa using scratch_fresh initial 1),
    erase_storeLimbs_fresh _ _ _ _ (scratch_fresh initial 1),
    scratchState_erase initial 6 hwf]

theorem storeBytes_erase (m : MemoryState) (out : Pointer) (bytes : Bytes) (n : Nat) :
    (storeBytes m out bytes).eraseFrom n = storeBytes (m.eraseFrom n) out bytes := by
  simp only [storeBytes, MemoryState.eraseFrom_storeAt]

theorem smallRange_storeBytes (h : SmallRange m q n) (out : Pointer) (v : Bytes) :
    SmallRange (storeBytes m out v) q n := by
  unfold storeBytes
  repeat apply SmallRange.storeAt
  exact h

theorem wf_storeBytes {s : GlobalState} (h : s.WF) (out : Pointer) (v : Bytes) :
    ({s with mem := storeBytes s.mem out v} : GlobalState).WF := by
  simpa only [storeBytes, GlobalState.WF_storeAt] using h

/-- The byte stores lie wholly inside the live destination, including when
another read uses the same allocation at a disjoint offset. -/
theorem byte_disjoint_of_output (h : SmallRange m out 32)
    (hd : (Range.of q bits).Disjoint (Range.of out 256))
    (k : Nat) (hk : k < 32) :
    (Range.of (out.add (BitVec.ofNat 64 k)) 8).Disjoint (Range.of q bits) := by
  have hoff := Pointer.offsetInBits_add (h.no_wrap (k := k) (by omega))
  have hk64 : k < 2^64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at hoff
  have hd' := hd.symm
  simp only [Range.Disjoint, Range.of] at hd' ⊢
  simp only [Pointer.add_id, hoff]
  rcases hd' with hid | hbefore | hafter
  · exact Or.inl hid
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

theorem storeBytes_frame (m : MemoryState) (out q : Pointer) (bytes : Bytes)
    (bits : Nat) (hout : SmallRange m out 32)
    (hd : (Range.of q bits).Disjoint (Range.of out 256)) :
    (storeBytes m out bytes).readAt q bits = m.readAt q bits := by
  have h0 := byte_disjoint_of_output hout hd 0 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, Pointer.add_zero] at h0
  have hstep (m' : MemoryState) (k : Nat) (hk : k < 32) (v : BitVec 8) :
      (m'.storeAt (out.add (BitVec.ofNat 64 k)) v).readAt q bits = m'.readAt q bits :=
    MemoryState.readAt_storeAt_disjoint (byte_disjoint_of_output hout hd k hk) v
  simp only [storeBytes, BitVec.ofNat_eq_ofNat]
  rw [
    hstep _ 31 (by decide),
    hstep _ 30 (by decide),
    hstep _ 29 (by decide),
    hstep _ 28 (by decide),
    hstep _ 27 (by decide),
    hstep _ 26 (by decide),
    hstep _ 25 (by decide),
    hstep _ 24 (by decide),
    hstep _ 23 (by decide),
    hstep _ 22 (by decide),
    hstep _ 21 (by decide),
    hstep _ 20 (by decide),
    hstep _ 19 (by decide),
    hstep _ 18 (by decide),
    hstep _ 17 (by decide),
    hstep _ 16 (by decide),
    hstep _ 15 (by decide),
    hstep _ 14 (by decide),
    hstep _ 13 (by decide),
    hstep _ 12 (by decide),
    hstep _ 11 (by decide),
    hstep _ 10 (by decide),
    hstep _ 9 (by decide),
    hstep _ 8 (by decide),
    hstep _ 7 (by decide),
    hstep _ 6 (by decide),
    hstep _ 5 (by decide),
    hstep _ 4 (by decide),
    hstep _ 3 (by decide),
    hstep _ 2 (by decide),
    hstep _ 1 (by decide),
    MemoryState.readAt_storeAt_disjoint h0]

end Agave.Ed25519.Encoding.Compress.Execution
