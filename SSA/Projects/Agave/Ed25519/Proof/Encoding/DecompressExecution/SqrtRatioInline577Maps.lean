import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineSerializerRename
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Loads

/-! Typed register embeddings for the two original serializer tails. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
open LeanMLIR.RIR SerializerRename
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000

def firstIndex (i : Nat) : Nat :=
  if i < 11 then i + 3 else if i = 11 then 1 else if i < 45 then i + 2 else
  if i < 54 then (if i % 2 = 1 then (i - 45) / 2 + 431 else i + 39) else
  i + 382

theorem firstIndex_bound (i : Fin ToBytes.program.Γ.n) :
    firstIndex i.val < program.Γ.n := by
  have hi := i.isLt
  change i.val < 197 at hi
  change firstIndex i.val < 825
  unfold firstIndex
  split_ifs <;> omega

def firstVal (i : Fin ToBytes.program.Γ.n) : Dst program.Γ (ToBytes.program.Γ.ty i) :=
  ⟨⟨firstIndex i.val, firstIndex_bound i⟩, by fin_cases i <;> rfl⟩

theorem firstIndex_injective : Function.Injective
    (fun i : Fin ToBytes.program.Γ.n => (firstVal i).i) := by
  intro i j h
  apply Fin.ext
  have hn := congrArg Fin.val h
  change firstIndex i.val = firstIndex j.val at hn
  unfold firstIndex at hn
  split_ifs at hn <;> omega

def firstArg (i : Fin ToBytes.program.Γ.args.length) :
    Reg program.Γ ToBytes.program.Γ.args[i] :=
  match i with
  | ⟨0, _⟩ => %63
  | ⟨1, _⟩ => %75

theorem firstArg_disjoint (i : Fin ToBytes.program.Γ.args.length)
    (j : Fin ToBytes.program.Γ.n) :
    valueIndex (firstArg i) ≠ some (firstVal j).i := by
  fin_cases i
  · intro h
    have hn := congrArg (Option.map Fin.val) h
    change some 63 = some (firstIndex j.val) at hn
    simp only [Option.some.injEq] at hn
    unfold firstIndex at hn
    split_ifs at hn <;> omega
  · intro h
    have hn := congrArg (Option.map Fin.val) h
    change some 75 = some (firstIndex j.val) at hn
    simp only [Option.some.injEq] at hn
    unfold firstIndex at hn
    split_ifs at hn <;> omega

def firstNames : Names ToBytes.program.Γ program.Γ :=
  ⟨firstVal, firstArg, firstIndex_injective, firstArg_disjoint⟩

def firstRenaming : Renaming ToBytes.program.Γ program.Γ :=
  firstNames.toRenaming

def secondIndex (i : Nat) : Nat :=
  if i < 11 then i + 3 else if i = 11 then 1 else if i < 45 then i + 2 else
  i + 534

theorem secondIndex_bound (i : Fin ToBytes.program.Γ.n) :
    secondIndex i.val < program.Γ.n := by
  have hi := i.isLt
  change i.val < 197 at hi
  change secondIndex i.val < 825
  unfold secondIndex
  split_ifs <;> omega

def secondVal (i : Fin ToBytes.program.Γ.n) : Dst program.Γ (ToBytes.program.Γ.ty i) :=
  ⟨⟨secondIndex i.val, secondIndex_bound i⟩, by fin_cases i <;> rfl⟩

theorem secondIndex_injective : Function.Injective
    (fun i : Fin ToBytes.program.Γ.n => (secondVal i).i) := by
  intro i j h
  apply Fin.ext
  have hn := congrArg Fin.val h
  change secondIndex i.val = secondIndex j.val at hn
  unfold secondIndex at hn
  split_ifs at hn <;> omega

def secondArg (i : Fin ToBytes.program.Γ.args.length) :
    Reg program.Γ ToBytes.program.Γ.args[i] :=
  match i with
  | ⟨0, _⟩ => %62
  | ⟨1, _⟩ => %73

theorem secondArg_disjoint (i : Fin ToBytes.program.Γ.args.length)
    (j : Fin ToBytes.program.Γ.n) :
    valueIndex (secondArg i) ≠ some (secondVal j).i := by
  fin_cases i
  · intro h
    have hn := congrArg (Option.map Fin.val) h
    change some 62 = some (secondIndex j.val) at hn
    simp only [Option.some.injEq] at hn
    unfold secondIndex at hn
    split_ifs at hn <;> omega
  · intro h
    have hn := congrArg (Option.map Fin.val) h
    change some 73 = some (secondIndex j.val) at hn
    simp only [Option.some.injEq] at hn
    unfold secondIndex at hn
    split_ifs at hn <;> omega

def secondNames : Names ToBytes.program.Γ program.Γ :=
  ⟨secondVal, secondArg, secondIndex_injective, secondArg_disjoint⟩

def secondRenaming : Renaming ToBytes.program.Γ program.Γ :=
  secondNames.toRenaming

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
