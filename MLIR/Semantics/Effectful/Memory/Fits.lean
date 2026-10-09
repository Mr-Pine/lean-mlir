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

/-- `p`'s block is live, with room for `w` bits at `p`: a store's target. -/
def Room (m : MemoryState) (p : Pointer) (w : Nat) : Prop :=
  ∃ b, m[p.id]? = some b ∧ b.live = true ∧ p.offsetInBits + w ≤ b.lengthInBits
deriving Decidable

/-- `p` holds `w` known bits: its block is live, with room for them, all defined. -/
def Fits (m : MemoryState) (p : Pointer) (w : Nat) : Prop :=
  ∃ b,
    m[p.id]? = some b ∧
      b.live = true ∧
      p.offsetInBits + w ≤ b.lengthInBits ∧
      b.defined.extractLsb' p.offsetInBits w = BitVec.allOnes w
deriving Decidable

theorem Room.inBounds (h : Room m p w) : InBounds m p w := by
  obtain ⟨b, hb, _, hw⟩ := h
  exact ⟨b, hb, hw⟩

theorem Fits.room (h : Fits m p w) : Room m p w := by
  obtain ⟨b, hb, hl, hw, _⟩ := h
  exact ⟨b, hb, hl, hw⟩

theorem Fits.inBounds (h : Fits m p w) : InBounds m p w :=
  h.room.inBounds

theorem InBounds.mono (hv : v ≤ w) (h : InBounds m p w) : InBounds m p v := by
  obtain ⟨blk, hblk, hsz⟩ := h
  exact ⟨blk, hblk, by omega⟩

theorem Room.mono (hv : v ≤ w) (h : Room m p w) : Room m p v := by
  obtain ⟨blk, hblk, hl, hsz⟩ := h
  exact ⟨blk, hblk, hl, by omega⟩

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

theorem Room.add {off : Nat} (hoff : off < 2 ^ 64) (hov : ¬p.offset.uaddOverflow off)
    (h : Room m p (w + off * 8)) : Room m (p.add off) w := by
  obtain ⟨blk, hblk, hl, hsz⟩ := h
  exact
    ⟨blk, hblk, hl, by
      rw [Pointer.offsetInBits_add_nat hoff hov]; omega⟩

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
