module

public import MLIR.Semantics.Effectful.Memory
public import MLIR.Semantics.Effectful.Memory.Bits

namespace MLIR

@[expose] public section

/-- `p`'s block exists with room for `w` bits at `p`: a load does not trap (a dead object's bits
load as poison). -/
def InBounds (m : MemoryState) (p : Pointer) (w : Nat) : Prop :=
  ∃ b, m[p.id]? = some b ∧ p.offsetInBits + w ≤ b.lengthInBits
deriving Decidable

/-- `p`'s block is live, with room for `w` bits at `p`: a read's source (`memcpy`'s). -/
def Live (m : MemoryState) (p : Pointer) (w : Nat) : Prop :=
  ∃ b, m[p.id]? = some b ∧ b.live = true ∧ p.offsetInBits + w ≤ b.lengthInBits
deriving Decidable

/-- `p`'s block is writable: no `constant` global's. -/
def Writable (m : MemoryState) (p : Pointer) : Prop :=
  ∃ b, m[p.id]? = some b ∧ b.writable = true
deriving Decidable

/-- `p`'s block is live and writable, with room for `w` bits at `p`: a store's target. -/
def Room (m : MemoryState) (p : Pointer) (w : Nat) : Prop :=
  Live m p w ∧ Writable m p

instance : Decidable (Room m p w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `p` holds `w` known bits: its block is live, with room for them, all defined. -/
def Fits (m : MemoryState) (p : Pointer) (w : Nat) : Prop :=
  ∃ b,
    m[p.id]? = some b ∧
      b.live = true ∧
      p.offsetInBits + w ≤ b.lengthInBits ∧
      b.defined.extractLsb' p.offsetInBits w = BitVec.allOnes w
deriving Decidable

/-- `Room`'s block: live, writable, with room at `p`. -/
theorem Room.block (h : Room m p w) :
    ∃ b, m[p.id]? = some b ∧ b.live = true ∧ p.offsetInBits + w ≤ b.lengthInBits ∧
      b.writable = true := by
  obtain ⟨⟨b, hb, hl, hsz⟩, b', hb', hw⟩ := h
  rw [hb] at hb'
  cases hb'
  exact ⟨b, hb, hl, hsz, hw⟩

/-- `Room` from its block. -/
theorem Room.of_block (hb : m[p.id]? = some b) (hl : b.live = true)
    (hsz : p.offsetInBits + w ≤ b.lengthInBits) (hw : b.writable = true) : Room m p w :=
  ⟨⟨b, hb, hl, hsz⟩, b, hb, hw⟩

theorem Live.inBounds (h : Live m p w) : InBounds m p w := by
  obtain ⟨b, hb, _, hw⟩ := h
  exact ⟨b, hb, hw⟩

theorem Room.live (h : Room m p w) : Live m p w :=
  h.1

theorem Room.writable (h : Room m p w) : Writable m p :=
  h.2

theorem Room.inBounds (h : Room m p w) : InBounds m p w :=
  h.live.inBounds

theorem Fits.live (h : Fits m p w) : Live m p w := by
  obtain ⟨b, hb, hl, hw, _⟩ := h
  exact ⟨b, hb, hl, hw⟩

/-- Known bits in a writable block: room for them. -/
theorem Fits.room (h : Fits m p w) (hw : Writable m p) : Room m p w :=
  ⟨h.live, hw⟩

theorem Fits.inBounds (h : Fits m p w) : InBounds m p w :=
  h.live.inBounds

/-- Writability is the block's: the same at any pointer into it. -/
theorem Writable.of_id_eq (h : Writable m p) (he : q.id = p.id) : Writable m q := by
  obtain ⟨b, hb, hw⟩ := h
  exact ⟨b, he ▸ hb, hw⟩

/-- The same block at `p`: the same bounds. -/
theorem InBounds.of_getElem?_eq (he : m'[p.id]? = m[p.id]?) (h : InBounds m p w) :
    InBounds m' p w := by
  obtain ⟨b, hb, hw⟩ := h
  exact ⟨b, he.trans hb, hw⟩

/-- The same block at `p`: the same liveness. -/
theorem Live.of_getElem?_eq (he : m'[p.id]? = m[p.id]?) (h : Live m p w) : Live m' p w := by
  obtain ⟨b, hb, hl, hw⟩ := h
  exact ⟨b, he.trans hb, hl, hw⟩

/-- The same block at `p`: the same writability. -/
theorem Writable.of_getElem?_eq (he : m'[p.id]? = m[p.id]?) (h : Writable m p) : Writable m' p := by
  obtain ⟨b, hb, hw⟩ := h
  exact ⟨b, he.trans hb, hw⟩

/-- The same block at `p`: the same room. -/
theorem Room.of_getElem?_eq (he : m'[p.id]? = m[p.id]?) (h : Room m p w) : Room m' p w :=
  ⟨h.1.of_getElem?_eq he, h.2.of_getElem?_eq he⟩

/-- The same block at `p`: the same known bits. -/
theorem Fits.of_getElem?_eq (he : m'[p.id]? = m[p.id]?) (h : Fits m p w) : Fits m' p w := by
  obtain ⟨b, hb, hl, hw, hd⟩ := h
  exact ⟨b, he.trans hb, hl, hw, hd⟩

theorem InBounds.mono (hv : v ≤ w) (h : InBounds m p w) : InBounds m p v := by
  obtain ⟨blk, hblk, hsz⟩ := h
  exact ⟨blk, hblk, by omega⟩

theorem Live.mono (hv : v ≤ w) (h : Live m p w) : Live m p v := by
  obtain ⟨blk, hblk, hl, hsz⟩ := h
  exact ⟨blk, hblk, hl, by omega⟩

theorem Room.mono (hv : v ≤ w) (h : Room m p w) : Room m p v :=
  ⟨h.1.mono hv, h.2⟩

theorem Fits.mono (hv : v ≤ w) (h : Fits m p w) : Fits m p v := by
  obtain ⟨blk, hblk, hl, hsz, hd⟩ := h
  refine ⟨blk, hblk, hl, by omega, ?_⟩
  have := congrArg (·.extractLsb' 0 v) hd
  simpa only [BitVec.extractLsb'_extractLsb'_add (show 0 + v ≤ w by omega), Nat.add_zero,
    BitVec.extractLsb'_allOnes (show 0 + v ≤ w by omega)] using this

/-- No overflow adding `b` means none adding less. -/
theorem _root_.BitVec.not_uaddOverflow_of_le {x a b : BitVec w} (h : ¬x.uaddOverflow b)
    (hab : a.toNat ≤ b.toNat) : ¬x.uaddOverflow a := by
  simp only [BitVec.uaddOverflow, ge_iff_le, decide_eq_true_eq, Nat.not_le] at h ⊢
  omega

/-- `p.add off`'s offset in bits, for `off < 2 ^ 64`, without overflow. -/
theorem Pointer.offsetInBits_add_nat {p : Pointer} {off : Nat} (hoff : off < 2 ^ 64)
    (hov : ¬p.offset.uaddOverflow off) : (p.add off).offsetInBits = p.offsetInBits + off * 8 := by
  simp only [Pointer.offsetInBits, Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hov]
  dsimp
  have := BitVec.ofNatLT_eq_ofNat hoff ▸ BitVec.toNat_ofNatLT off hoff
  rw [this]
  omega

theorem InBounds.add {off : Nat} (hoff : off < 2 ^ 64) (hov : ¬p.offset.uaddOverflow off)
    (h : InBounds m p (w + off * 8)) : InBounds m (p.add off) w := by
  obtain ⟨blk, hblk, hsz⟩ := h
  exact
    ⟨blk, hblk, by
      rw [Pointer.offsetInBits_add_nat hoff hov]; omega⟩

theorem Live.add {off : Nat} (hoff : off < 2 ^ 64) (hov : ¬p.offset.uaddOverflow off)
    (h : Live m p (w + off * 8)) : Live m (p.add off) w := by
  obtain ⟨blk, hblk, hl, hsz⟩ := h
  exact
    ⟨blk, hblk, hl, by
      rw [Pointer.offsetInBits_add_nat hoff hov]; omega⟩

theorem Room.add {off : Nat} (hoff : off < 2 ^ 64) (hov : ¬p.offset.uaddOverflow off)
    (h : Room m p (w + off * 8)) : Room m (p.add off) w :=
  ⟨h.1.add hoff hov, h.2.of_id_eq rfl⟩

theorem Fits.add {off : Nat} (hoff : off < 2 ^ 64) (hov : ¬p.offset.uaddOverflow off)
    (h : Fits m p (w + off * 8)) : Fits m (p.add off) w := by
  obtain ⟨blk, hblk, hl, hsz, hd⟩ := h
  refine
    ⟨blk, hblk, hl, by
      rw [Pointer.offsetInBits_add_nat hoff hov]; omega, ?_⟩
  have := congrArg (·.extractLsb' (off * 8) w) hd
  simp only [BitVec.extractLsb'_extractLsb'_add (show off * 8 + w ≤ w + off * 8 by omega),
    BitVec.extractLsb'_allOnes (show off * 8 + w ≤ w + off * 8 by omega)] at this
  rw [Pointer.offsetInBits_add_nat hoff hov]
  exact this

end

end MLIR
