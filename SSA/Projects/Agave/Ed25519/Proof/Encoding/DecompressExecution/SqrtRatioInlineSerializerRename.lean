import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytes
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Cutpoint
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.RegisterEmbedding

/-! A typed naming interface for the already checked serializer transport.
All execution and poison simulation is reused from `SmallOrder.Transport`. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SerializerRename
open LeanMLIR.RIR

abbrev Renaming := Agave.Ed25519.SmallOrder.Execution.Transport.Renaming

def valueIndex : Reg Γ t → Option (Fin Γ.n)
  | .arg .. => none
  | .val i _ => some i

/-- An injective, type-preserving naming of values, disjoint from argument
names. These are register identities, not execution premises. -/
structure Names (Γ Δ : Ctx) where
  val : (i : Fin Γ.n) → Dst Δ (Γ.ty i)
  arg : (i : Fin Γ.args.length) → Reg Δ Γ.args[i]
  injective : Function.Injective (fun i => (val i).i)
  disjoint : ∀ i j, valueIndex (arg i) ≠ some (val j).i

namespace Names
variable (N : Names Γ Δ)

def embedding : Agave.Ed25519.SmallOrder.Execution.Transport.Embedding Γ Δ where
  val := fun i => (N.val i).i
  type := fun i => (N.val i).h
  injective := N.injective
  arg := N.arg
  arg_stable := by
    intro E i j v
    have hn := N.disjoint i j
    cases he : N.arg i with
    | arg k h => rfl
    | val k h =>
      simp only [he, valueIndex, ne_eq, Option.some.injEq] at hn
      exact Env.read_write_ne E _ hn

abbrev mapDst (d : Dst Γ t) : Dst Δ t := N.embedding.dst d
abbrev mapReg (r : Reg Γ t) : Reg Δ t := N.embedding.reg r
abbrev project := N.embedding.pull
abbrev toRenaming : Renaming Γ Δ := N.embedding.renaming

theorem project_read (E : ⟪Δ⟫) (r : Reg Γ t) :
    (N.project E).read r = E.read (N.mapReg r) := N.embedding.read E r

theorem project_write (E : ⟪Δ⟫) (d : Dst Γ t) (v : ⟦t⟧) :
    N.project (E.write (N.mapDst d) v) = (N.project E).write d v :=
  N.embedding.write E d v
end Names

namespace Renaming
abbrev project (ρ : Renaming Γ Δ) := ρ.pull
abbrev supported := @Agave.Ed25519.SmallOrder.Execution.Transport.Supported

/-- Exact list simulation includes failure and every memory effect. -/
theorem list_run (ρ : Renaming Γ Δ) (is : List (Instr Γ))
    (hs : ∀ i ∈ is, supported i) (E : ⟪Δ⟫) (s : GlobalState) :
    (fun p => (ρ.project p.1, p.2)) <$> (List.foldlM Instr.run E (is.map ρ.instr)) s =
      (List.foldlM Instr.run (ρ.project E) is) s := ρ.fold is hs E s

theorem list_success (ρ : Renaming Γ Δ) (is : List (Instr Γ))
    (hs : ∀ i ∈ is, supported i) (E : ⟪Δ⟫) (s t : GlobalState) (F : ⟪Γ⟫)
    (h : List.foldlM Instr.run (ρ.project E) is s = .value (F, t)) :
    ∃ G, List.foldlM Instr.run E (is.map ρ.instr) s = .value (G, t) ∧ ρ.project G = F :=
  ρ.fold_success is hs E s t F h
end Renaming
end Agave.Ed25519.Encoding.Decompress.Execution.SerializerRename
