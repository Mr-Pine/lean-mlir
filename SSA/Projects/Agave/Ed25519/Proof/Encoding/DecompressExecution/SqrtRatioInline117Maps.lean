import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineSerializerRename
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlinePrefixSquare

/-! Exact type-preserving register embedding for the first inlined serializer. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117
open LeanMLIR.RIR SerializerRename
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000

def index (i : Nat) : Nat :=
  if i < 11 then i + 3 else if i = 11 then 1 else if i < 45 then i + 2 else
  i + 39

theorem index_bound (i : Fin ToBytes.program.Γ.n) :
    index i.val < program.Γ.n := by
  have hi := i.isLt
  change i.val < 197 at hi
  change index i.val < 825
  unfold index
  split_ifs <;> omega

def val (i : Fin ToBytes.program.Γ.n) : Dst program.Γ (ToBytes.program.Γ.ty i) :=
  ⟨⟨index i.val, index_bound i⟩, by fin_cases i <;> rfl⟩

theorem index_injective : Function.Injective
    (fun i : Fin ToBytes.program.Γ.n => (val i).i) := by
  intro i j h
  apply Fin.ext
  have hn := congrArg Fin.val h
  change index i.val = index j.val at hn
  unfold index at hn
  split_ifs at hn <;> omega

def arg (i : Fin ToBytes.program.Γ.args.length) :
    Reg program.Γ ToBytes.program.Γ.args[i] :=
  match i with
  | ⟨0, _⟩ => %67
  | ⟨1, _⟩ => %75


theorem arg_disjoint (i : Fin ToBytes.program.Γ.args.length)
    (j : Fin ToBytes.program.Γ.n) :
    valueIndex (arg i) ≠ some (val j).i := by
  fin_cases i
  · intro h
    have hn := congrArg (Option.map Fin.val) h
    change some 67 = some (index j.val) at hn
    simp only [Option.some.injEq] at hn
    unfold index at hn
    split_ifs at hn <;> omega
  · intro h
    have hn := congrArg (Option.map Fin.val) h
    change some 75 = some (index j.val) at hn
    simp only [Option.some.injEq] at hn
    unfold index at hn
    split_ifs at hn <;> omega

def names : Names ToBytes.program.Γ program.Γ :=
  ⟨val, arg, index_injective, arg_disjoint⟩

def rename : Renaming ToBytes.program.Γ program.Γ :=
  names.toRenaming

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117
