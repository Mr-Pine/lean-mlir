import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.RegisterEmbedding
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerSource
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointConstantTimeEqProgram

namespace Agave.Ed25519.SmallOrder.Execution.SerializerEmbedding
open LeanMLIR.RIR
abbrev Source := Encoding.Decompress.Execution.ToBytes.program.Γ
abbrev Target := Verifier.Execution.PointConstantTimeEq.program.Γ

/-- The compiler shares the 45 constants, and gives each inline copy a fresh
contiguous run of 152 value registers. -/
def index (shift : Nat) (hlo : 12 ≤ shift) (hhi : shift ≤ 471)
    (i : Fin Source.n) : Fin Target.n :=
  ⟨if i.val < 45 then i.val + 2 else i.val + shift, by
    have hi : i.val < 197 := i.isLt
    change (if i.val < 45 then i.val + 2 else i.val + shift) < 671
    split <;> omega⟩

theorem index_injective (shift : Nat) (hlo : 12 ≤ shift) (hhi : shift ≤ 471) :
    Function.Injective (index shift hlo hhi) := by
  intro i j h
  have h' := congrArg Fin.val h
  dsimp [index] at h'
  apply Fin.ext
  split_ifs at h' <;> omega

end Agave.Ed25519.SmallOrder.Execution.SerializerEmbedding
