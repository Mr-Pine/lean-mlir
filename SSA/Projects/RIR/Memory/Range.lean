module

public import SSA.Projects.RIR.Memory.Pointer

namespace LeanMLIR.RIR

@[expose] public section

/-- A range is a pointer with a width.
    Offset and width are both in bits.
 -/
structure Range where
  id : BlockId
  offset : Nat
  width : Nat

/-- Convert a `Pointer` and a width to a `Range` -/
def Range.of (p : Pointer) (w : Nat) : Range :=
  ⟨p.id, p.offsetInBits, w⟩

/-- Two ranges address different bytes -/
def Range.Disjoint (r r' : Range) : Prop :=
  r.id ≠ r'.id -- different blocks
    ∨
    r.offset + r.width ≤ r'.offset -- `r` is entirely before `r'`
    ∨ r.offset ≥ r'.offset + r'.width -- `r` is entirely after `r'`
deriving Decidable

theorem Range.Disjoint.comm : (Range.Disjoint r r') ↔ (Range.Disjoint r' r) := by
  grind [Range.Disjoint]

theorem Range.Disjoint.symm : (Range.Disjoint r r') → (Range.Disjoint r' r) :=
  comm.mp

end

end LeanMLIR.RIR
