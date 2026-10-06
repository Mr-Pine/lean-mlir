import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionGlobals

/-! Memory transport for the identity construction and the emitted Option copies. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- Restrict a live byte range to the suffix used by an emitted GEP. -/
theorem smallRange_add (h : SmallRange m p bytes) (hk : k + count ≤ bytes) :
    SmallRange m (p.add (BitVec.ofNat 64 k)) count := by
  have hn := h.no_wrap (k := k) (by omega)
  have hk64 : k < 2^64 := by have := h.offset_lt; norm_num at *; omega
  obtain ⟨b, hb, hs, hr⟩ := h
  refine ⟨b, hb, hs, ?_⟩
  simpa only [Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] using (by omega : p.offset.toNat + k + count ≤ b.length)

/-- A caller read disjoint from a whole object is disjoint from each store in it. -/
theorem disjoint_add_subrange (h : SmallRange m p bytes)
    (hd : (Range.of q w).Disjoint (Range.of p (8 * bytes))) (hk : k + count ≤ bytes) :
    (Range.of q w).Disjoint (Range.of (p.add (BitVec.ofNat 64 k)) (8 * count)) := by
  have ho := Pointer.offsetInBits_add (h.no_wrap (k := k) (by omega))
  have hk64 : k < 2^64 := by have := h.offset_lt; norm_num at *; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at ho
  simp only [Range.Disjoint, Range.of, Pointer.add_id, ho] at hd ⊢
  rcases hd with hid | hb | ha
  · exact Or.inl hid
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- Four 40-byte stores emitted in both identity-construction sites. -/
def identityStoreState (state : GlobalState) (dst : Pointer) : GlobalState :=
  { state with mem := (((state.mem.storeAt dst (0#320)).storeAt
    (dst.add 40#64) (1#320)).storeAt (dst.add 80#64) (1#320)).storeAt (dst.add 120#64) (0#320) }

/-- Extended Edwards identity: X=0, Y=1, Z=1, T=0, five u64 limbs each. -/
def identityBytes : PointBytes :=
  Memory.spliceBits (Memory.spliceBits (Memory.spliceBits
    (Memory.spliceBits (0#1280) 0 (0#320)) 320 (1#320)) 640 (1#320)) 960 (0#320)

theorem identity_splice_parts (old : PointBytes) :
    Memory.spliceBits (Memory.spliceBits (Memory.spliceBits
      (Memory.spliceBits old 0 (0#320)) 320 (1#320)) 640 (1#320)) 960 (0#320) =
      identityBytes := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [identityBytes, Memory.getLsbD_spliceBits]
  grind

/-- Readback requires no assumption about the previous contents of the allocation. -/
theorem identity_readback (state : GlobalState) (dst : Pointer)
    (h : SmallRange state.mem dst 160) :
    ReadBytes (identityStoreState state dst) dst 160 identityBytes := by
  constructor
  · exact (((h.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _
  · have h0 := MemoryState.readAt_add_storeAt (p := dst) (off := 0#64)
      (v := 1280) h.fits (h.no_wrap (k := 0) (by decide)) (by decide) (0#320)
    have h40 := MemoryState.readAt_add_storeAt (p := dst) (off := 40#64)
      (v := 1280) (m := state.mem.storeAt dst (0#320)) h.fits.storeAt (h.no_wrap (k := 40) (by decide)) (by decide) (1#320)
    have h80 := MemoryState.readAt_add_storeAt (p := dst) (off := 80#64)
      (v := 1280) (m := (state.mem.storeAt dst (0#320)).storeAt (dst.add 40#64) (1#320)) h.fits.storeAt.storeAt (h.no_wrap (k := 80) (by decide)) (by decide) (1#320)
    have h120 := MemoryState.readAt_add_storeAt (p := dst) (off := 120#64)
      (v := 1280) (m := ((state.mem.storeAt dst (0#320)).storeAt (dst.add 40#64) (1#320)).storeAt (dst.add 80#64) (1#320)) h.fits.storeAt.storeAt.storeAt (h.no_wrap (k := 120) (by decide))
      (by decide) (0#320)
    simp only [Pointer.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.zero_mul, Nat.reduceMul] at h0 h40 h80 h120
    change (identityStoreState state dst).mem.readAt dst 1280 = _
    simp only [identityStoreState, h120, h80, h40, h0, identity_splice_parts]

theorem identity_frame (state : GlobalState) (dst : Pointer)
    (hwf : state.WF) (h : SmallRange state.mem dst 160) :
    OutputFrame state (identityStoreState state dst) dst 160 := by
  constructor
  · simpa only [identityStoreState, GlobalState.WF_storeAt] using hwf
  · intro q n hq
    exact (((hq.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _
  · intro q w hd
    have h0 := disjoint_add_subrange h hd (k := 0) (count := 40) (by decide)
    have h40 := disjoint_add_subrange h hd (k := 40) (count := 40) (by decide)
    have h80 := disjoint_add_subrange h hd (k := 80) (count := 40) (by decide)
    have h120 := disjoint_add_subrange h hd (k := 120) (count := 40) (by decide)
    simp only [Pointer.add_zero] at h0
    simp only [identityStoreState, MemoryState.readAt_storeAt_disjoint h120.symm,
      MemoryState.readAt_storeAt_disjoint h80.symm,
      MemoryState.readAt_storeAt_disjoint h40.symm,
      MemoryState.readAt_storeAt_disjoint h0.symm]

/-- The memory transition of one exact RIR memcpy. -/
def copyPointState (state : GlobalState) (dst src : Pointer) : GlobalState :=
  { state with mem := state.mem.storeAt dst (state.mem.readAt src 1280) }

/-- The generated offsets 8 → 6 → 6 → 0, with each read taken after the
preceding copy, as required by the operational semantics. -/
def optionCopyState (state : GlobalState) (out slot29 slot30 point : Pointer) : GlobalState :=
  copyPointState (copyPointState (copyPointState state (slot29.add 6) (out.add 8))
    (slot30.add 6) (slot29.add 6)) point (slot30.add 6)

theorem copy_point_readback (state : GlobalState) (dst src : Pointer) (value : PointBytes)
    (hd : SmallRange state.mem dst 160) (hs : ReadBytes state src 160 value) :
    ReadBytes (copyPointState state dst src) dst 160 value := by
  refine ⟨hd.storeAt _ _, ?_⟩
  exact (MemoryState.readAt_storeAt_self hd.fits _).trans hs.2

theorem copy_point_frame (state : GlobalState) (dst src : Pointer) (hwf : state.WF) :
    OutputFrame state (copyPointState state dst src) dst 160 := by
  constructor
  · exact hwf.storeAt
  · intro q n hq; exact hq.storeAt _ _
  · intro q w hd; exact MemoryState.readAt_storeAt_disjoint hd.symm _

theorem option_copy_readback (state : GlobalState) (out slot29 slot30 point : Pointer)
    (value : PointBytes) (hs : ReadBytes state (out.add 8) 160 value)
    (h29 : SmallRange state.mem slot29 166) (h30 : SmallRange state.mem slot30 166)
    (hp : SmallRange state.mem point 160) :
    ReadBytes (optionCopyState state out slot29 slot30 point) point 160 value := by
  have h1 := copy_point_readback state (slot29.add 6) (out.add 8) value
    (smallRange_add h29 (k := 6) (by decide)) hs
  have h2 := copy_point_readback _ (slot30.add 6) (slot29.add 6) value
    ((smallRange_add h30 (k := 6) (by decide)).storeAt _ _) h1
  exact copy_point_readback _ point (slot30.add 6) value ((hp.storeAt _ _).storeAt _ _) h2

/-- Every live caller range survives the three copies. -/
theorem option_copy_live (state : GlobalState) (out slot29 slot30 point q : Pointer)
    (n : Nat) (h : SmallRange state.mem q n) :
    SmallRange (optionCopyState state out slot29 slot30 point).mem q n :=
  ((h.storeAt _ _).storeAt _ _).storeAt _ _

theorem option_copy_wf (state : GlobalState) (out slot29 slot30 point : Pointer)
    (h : state.WF) : (optionCopyState state out slot29 slot30 point).WF := by
  simpa only [optionCopyState, copyPointState, GlobalState.WF_storeAt] using h

/-- Reads outside the three destinations are unchanged. -/
theorem option_copy_read_frame (state : GlobalState) (out slot29 slot30 point q : Pointer)
    (w : Nat) (h29 : (Range.of q w).Disjoint (Range.of (slot29.add 6) 1280))
    (h30 : (Range.of q w).Disjoint (Range.of (slot30.add 6) 1280))
    (hp : (Range.of q w).Disjoint (Range.of point 1280)) :
    (optionCopyState state out slot29 slot30 point).mem.readAt q w = state.mem.readAt q w := by
  simp only [optionCopyState, copyPointState, MemoryState.readAt_storeAt_disjoint hp.symm,
    MemoryState.readAt_storeAt_disjoint h30.symm, MemoryState.readAt_storeAt_disjoint h29.symm]

/-- This is the actual RIR memcpy operation, with its live-range and nonalias checks. -/
theorem copy_point_operation (state : GlobalState) (dst src : Pointer) (env : Env Γ)
    (hd : SmallRange state.mem dst 160) (hs : SmallRange state.mem src 160)
    (hdis : (Range.of dst 1280).Disjoint (Range.of src 1280)) :
    Operation.memcpy (.value dst) (.value src) (.value (160#64)) env state =
      .value (env, copyPointState state dst src) := by
  simp [Operation.memcpy, copyPointState, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, hd.fits, hs.fits, hdis, throwUBIf]

/-- A zero-fill emitted by the imported identity constructor. -/
theorem identity_zero_operation (state : GlobalState) (dst : Pointer) (env : Env Γ)
    (h : Fits state.mem dst 320) :
    Operation.memset (.value dst) (.value (0#8)) (.value (40#64)) env state =
      .value (env, { state with mem := state.mem.storeAt dst (0#320) }) := by
  simp [Operation.memset, EffectM.bind_eq, EffectM.pure_eq, mlir_effect, h, throwUBIf]

/-- The 40-byte one is read from the actual imported global initializer. -/
theorem identity_global_read (state : GlobalState) (global : Pointer)
    (hoff : global.offset = 0) (hglobal : identityOne.Present global.id state.mem) :
    state.mem.readAt global 320 = 1#320 := by
  have hg := hglobal.readAt
  have hp : global = ⟨global.id, 0⟩ := by cases global; simp_all
  change state.mem.readAt ⟨global.id, 0⟩ 320 = 1#320 at hg
  exact (congrArg (fun p => state.mem.readAt p 320) hp).trans hg

/-- Each copy of the imported constant executes the real memcpy checks. -/
theorem identity_one_operation (state : GlobalState) (dst global : Pointer) (env : Env Γ)
    (hd : Fits state.mem dst 320) (hg : Fits state.mem global 320)
    (hr : state.mem.readAt global 320 = 1#320)
    (hdis : (Range.of dst 320).Disjoint (Range.of global 320)) :
    Operation.memcpy (.value dst) (.value global) (.value (40#64)) env state =
      .value (env, { state with mem := state.mem.storeAt dst (1#320) }) := by
  simp [Operation.memcpy, EffectM.bind_eq, EffectM.pure_eq, mlir_effect,
    hd, hg, hr, hdis, throwUBIf]

end Agave.Ed25519.Verifier.Execution.Dalek
