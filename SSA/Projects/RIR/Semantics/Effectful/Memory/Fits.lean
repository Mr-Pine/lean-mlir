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

end

end LeanMLIR.RIR
