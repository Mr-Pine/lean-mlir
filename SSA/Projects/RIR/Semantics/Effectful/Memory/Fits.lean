module

public import SSA.Projects.RIR.Semantics.Effectful.Memory

namespace LeanMLIR.RIR

@[expose] public section

/-- `Fits m p w` specifies that `p` is allocated in `m` with enough space for `w` bits -/
def Fits (m : MemoryState) (p : Pointer) (w : Nat) : Prop :=
  ∃ b, m[p.id]? = some b ∧ p.offsetInBits + w ≤ b.lengthInBits
deriving Decidable

theorem Fits.mono (hv : v ≤ w) (h : Fits m p w) : Fits m p v := by
  obtain ⟨blk, hblk, hsz⟩ := h
  exact ⟨blk, hblk, by omega⟩

/-- No overflow adding `b` means none adding less. -/
theorem _root_.BitVec.not_uaddOverflow_of_le {x a b : BitVec w} (h : ¬x.uaddOverflow b)
    (hab : a.toNat ≤ b.toNat) : ¬x.uaddOverflow a := by
  simp only [BitVec.uaddOverflow, ge_iff_le, decide_eq_true_eq, Nat.not_le] at h ⊢
  omega

theorem Fits.add {off : Nat} (hoff : off < 2 ^ 64) (hov : ¬p.offset.uaddOverflow off)
    (h : Fits m p (w + off * 8)) : Fits m (p.add off) w := by
  obtain ⟨blk, hblk, hsz⟩ := h
  refine ⟨blk, hblk, ?_⟩
  simp only [Pointer.offsetInBits, Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hov] at hsz ⊢
  dsimp
  have := BitVec.ofNatLT_eq_ofNat hoff ▸ BitVec.toNat_ofNatLT off hoff
  rw [this]
  omega

end

end LeanMLIR.RIR
