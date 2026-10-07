import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ExecutionMemory

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

@[simp] theorem readLimbs_explicit (s : GlobalState) (p : Pointer) :
    readLimbs s p = ![s.mem.readAt p 64, s.mem.readAt (p.add 8) 64,
      s.mem.readAt (p.add 16) 64, s.mem.readAt (p.add 24) 64,
      s.mem.readAt (p.add 32) 64] := by
  funext i
  fin_cases i <;> simp [readLimbs]

/-- Field calls preserve every caller object's allocation and length. -/
@[mlir_transport] theorem smallRange_storeLimbs (h : SmallRange m q bytes)
    (p : Pointer) (v : Fin 5 → BitVec 64) : SmallRange (storeLimbs m p v) q bytes := by
  exact ((((h.storeAt p (v 0)).storeAt (p.add 8) (v 1)).storeAt
    (p.add 16) (v 2)).storeAt (p.add 24) (v 3)).storeAt (p.add 32) (v 4)

@[mlir_transport] theorem fits_storeLimbs (h : Fits m q bits)
    (p : Pointer) (v : Fin 5 → BitVec 64) : Fits (storeLimbs m p v) q bits := by
  exact h.storeAt.storeAt.storeAt.storeAt.storeAt

@[mlir_transport] theorem wf_storeLimbs {s : GlobalState} (h : s.WF)
    (p : Pointer) (v : Fin 5 → BitVec 64) :
    ({ s with mem := storeLimbs s.mem p v } : GlobalState).WF := by
  simpa only [storeLimbs, GlobalState.WF_storeAt] using h

/-- A field call to fresh stack storage preserves reads in every other block. -/
@[mlir_read] theorem readAt_storeLimbs_ne (m : MemoryState) (p q : Pointer)
    (v : Fin 5 → BitVec 64) (bits : Nat) (h : p.id ≠ q.id) :
    (storeLimbs m p v).readAt q bits = m.readAt q bits := by
  have hd (off : BitVec 64) :
      (Range.of (p.add off) 64).Disjoint (Range.of q bits) :=
    Or.inl (by simpa only [Range.of, Pointer.add_id] using h)
  unfold storeLimbs
  erw [MemoryState.readAt_storeAt_disjoint (hd 32),
    MemoryState.readAt_storeAt_disjoint (hd 24),
    MemoryState.readAt_storeAt_disjoint (hd 16),
    MemoryState.readAt_storeAt_disjoint (hd 8),
    MemoryState.readAt_storeAt_disjoint
      (show (Range.of p 64).Disjoint (Range.of q bits) from Or.inl h)]

@[mlir_read] theorem readAt_storeLimbs0 (m : MemoryState) (p : Pointer)
    (v : Fin 5 → BitVec 64) (h : SmallRange m p 40) :
    (storeLimbs m p v).readAt p 64 = v 0 := by
  simpa using storeLimbs_readAt m p v h 0

@[mlir_read] theorem readAt_storeLimbs1 (m : MemoryState) (p : Pointer)
    (v : Fin 5 → BitVec 64) (h : SmallRange m p 40) :
    (storeLimbs m p v).readAt (p.add 8) 64 = v 1 := by
  simpa using storeLimbs_readAt m p v h 1

@[mlir_read] theorem readAt_storeLimbs2 (m : MemoryState) (p : Pointer)
    (v : Fin 5 → BitVec 64) (h : SmallRange m p 40) :
    (storeLimbs m p v).readAt (p.add 16) 64 = v 2 := by
  simpa using storeLimbs_readAt m p v h 2

@[mlir_read] theorem readAt_storeLimbs3 (m : MemoryState) (p : Pointer)
    (v : Fin 5 → BitVec 64) (h : SmallRange m p 40) :
    (storeLimbs m p v).readAt (p.add 24) 64 = v 3 := by
  simpa using storeLimbs_readAt m p v h 3

@[mlir_read] theorem readAt_storeLimbs4 (m : MemoryState) (p : Pointer)
    (v : Fin 5 → BitVec 64) (h : SmallRange m p 40) :
    (storeLimbs m p v).readAt (p.add 32) 64 = v 4 := by
  simpa using storeLimbs_readAt m p v h 4

/-- A limb store is contained in its five-limb output range. -/
theorem limb_disjoint_of_range (h : SmallRange m p 40)
    (hd : (Range.of q bits).Disjoint (Range.of p 320))
    (k : Nat) (hk : k + 8 ≤ 40) :
    (Range.of (p.add (BitVec.ofNat 64 k)) 64).Disjoint (Range.of q bits) := by
  have hoff := Pointer.offsetInBits_add (h.no_wrap (k := k) (by omega))
  have hk64 : k < 2^64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at hoff
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hoff] at hd ⊢
  rcases hd with hne | hbefore | hafter
  · exact Or.inl (Ne.symm hne)
  · exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inl (by omega))

/-- A five-limb result preserves every read disjoint from its complete output. -/
theorem readAt_storeLimbs_frame (m : MemoryState) (p q : Pointer)
    (v : Fin 5 → BitVec 64) (bits : Nat) (h : SmallRange m p 40)
    (hd : (Range.of q bits).Disjoint (Range.of p 320)) :
    (storeLimbs m p v).readAt q bits = m.readAt q bits := by
  have h0 := limb_disjoint_of_range h hd 0 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, Pointer.add_zero] at h0
  unfold storeLimbs
  erw [MemoryState.readAt_storeAt_disjoint (limb_disjoint_of_range h hd 32 (by decide)),
    MemoryState.readAt_storeAt_disjoint (limb_disjoint_of_range h hd 24 (by decide)),
    MemoryState.readAt_storeAt_disjoint (limb_disjoint_of_range h hd 16 (by decide)),
    MemoryState.readAt_storeAt_disjoint (limb_disjoint_of_range h hd 8 (by decide)),
    MemoryState.readAt_storeAt_disjoint h0]

theorem smallRange_add (h : SmallRange m p n) (hk : k + count ≤ n) :
    SmallRange m (p.add (BitVec.ofNat 64 k)) count := by
  have hn := h.no_wrap (k := k) (by omega)
  have hk64 : k < 2^64 := by have := h.offset_lt; norm_num at *; omega
  obtain ⟨b, hb, hsmall, hsize⟩ := h
  refine ⟨b, hb, hsmall, ?_⟩
  simp only [Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  omega

@[mlir_transport] theorem smallRange_alloca {s : GlobalState} (hwf : s.WF)
    (h : SmallRange s.mem p n) : SmallRange (s.alloca bytes).mem p n := by
  have hne := GlobalState.ne_allocaPtr_of_fits hwf h.fits
  obtain ⟨b, hb, hs, hz⟩ := h
  exact ⟨b, (GlobalState.getElem?_alloca hne).trans hb, hs, hz⟩

theorem smallRange_alloca_self (s : GlobalState) (bytes : Nat) (h : bytes < 2^63) :
    SmallRange (s.alloca bytes).mem s.allocaPtr bytes := by
  refine ⟨⟨bytes, 0⟩, ?_, h, ?_⟩
  · simp [GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
  · simp [GlobalState.allocaPtr]

@[mlir_read] theorem readAt_alloca_ne (s : GlobalState) (p : Pointer)
    (bytes bits : Nat) (h : p.id ≠ s.allocaPtr.id) :
    (s.alloca bytes).mem.readAt p bits = s.mem.readAt p bits := by
  simp only [MemoryState.readAt, GlobalState.getElem?_alloca h]

theorem offsetInBits_alloca (s : GlobalState) : s.allocaPtr.offsetInBits = 0 := rfl

theorem offsetInBits_alloca_add (s : GlobalState) (off : BitVec 64) :
    (s.allocaPtr.add off).offsetInBits = 8 * off.toNat := by
  simp [Pointer.offsetInBits, Pointer.add]


/-- A field output preserves all five words in another disjoint field slice. -/
theorem readLimbs_storeLimbs_frame (s : GlobalState) (p q : Pointer)
    (v : Fin 5 → BitVec 64) (hp : SmallRange s.mem p 40)
    (hq : SmallRange s.mem q 40)
    (hd : (Range.of q 320).Disjoint (Range.of p 320)) :
    readLimbs { s with mem := storeLimbs s.mem p v } q = readLimbs s q := by
  funext k
  apply readAt_storeLimbs_frame s.mem p _ v 64 hp
  exact limb_disjoint_of_range hq hd.symm (8*k.val) (by omega)

/-- Whole-field framing with no offset arithmetic when the allocation differs. -/
@[mlir_read] theorem readLimbs_storeLimbs_ne (s : GlobalState) (p q : Pointer)
    (v : Fin 5 → BitVec 64) (hd : p.id ≠ q.id) :
    readLimbs { s with mem := storeLimbs s.mem p v } q = readLimbs s q := by
  funext k
  exact readAt_storeLimbs_ne s.mem p _ v 64 (by simpa using hd)

/-- A value store never creates/removes an allocation or changes its length. -/
theorem storeAt_allocationShape (m : MemoryState) (p : Pointer) (x : BitVec w)
    (id : BlockId) :
    ((m.storeAt p x)[id]?).map MemoryBlock.length = (m[id]?).map MemoryBlock.length := by
  by_cases hid : id = p.id
  · subst id
    cases hb : m[p.id]? with
    | none => simp [MemoryState.storeAt, hb]
    | some b => simp [MemoryState.getElem?_storeAt_self hb]
  · have hne : (⟨id, 0⟩ : Pointer).id ≠ p.id := hid
    rw [MemoryState.getElem?_storeAt_ne (m := m) (p := p)
      (q := ⟨id, 0⟩) (x := x) hne]

theorem storeLimbs_allocationShape (m : MemoryState) (p : Pointer)
    (v : Fin 5 → BitVec 64) (id : BlockId) :
    ((storeLimbs m p v)[id]?).map MemoryBlock.length = (m[id]?).map MemoryBlock.length := by
  simp only [storeLimbs, storeAt_allocationShape]

end Agave.Ed25519.SerialPoint.Execution
