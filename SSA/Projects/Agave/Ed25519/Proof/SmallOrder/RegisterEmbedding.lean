import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.InstructionTransport

namespace Agave.Ed25519.SmallOrder.Execution.Transport
open LeanMLIR.RIR

theorem env_ext (a b : Env Γ) (ha : a.args = b.args) (hv : a.vals = b.vals) : a = b := by
  cases a; cases b; cases ha; cases hv; rfl

/-- A typed injection of local registers. Arguments may become local registers,
but are disjoint from the image of the writable source locals. -/
structure Embedding (Γ Δ : Ctx) where
  val : Fin Γ.n → Fin Δ.n
  type : ∀ i, Δ.ty (val i) = Γ.ty i
  injective : Function.Injective val
  arg : (i : Fin Γ.args.length) → Reg Δ Γ.args[i]
  arg_stable : ∀ (E : Env Δ) (i : Fin Γ.args.length) (j : Fin Γ.n)
    (v : ⟦Γ.ty j⟧),
    (E.write ⟨val j, type j⟩ v).read (arg i) = E.read (arg i)

def Embedding.reg (ρ : Embedding Γ Δ) : Reg Γ t → Reg Δ t
  | .arg i h => h ▸ ρ.arg i
  | .val i h => .val (ρ.val i) ((ρ.type i).trans h)

def Embedding.dst (ρ : Embedding Γ Δ) (d : Dst Γ t) : Dst Δ t :=
  ⟨ρ.val d.i, (ρ.type d.i).trans d.h⟩

def Embedding.pull (ρ : Embedding Γ Δ) (E : Env Δ) : Env Γ where
  args := fun i => E.read (ρ.arg i)
  vals := fun i => E.read (.val (ρ.val i) (ρ.type i))

theorem Embedding.read (ρ : Embedding Γ Δ) (E : Env Δ) (r : Reg Γ t) :
    (ρ.pull E).read r = E.read (ρ.reg r) := by
  cases r with
  | arg i h => cases h; rfl
  | val i h => cases h; rfl

theorem Embedding.write (ρ : Embedding Γ Δ) (E : Env Δ)
    (d : Dst Γ t) (v : ⟦t⟧) :
    ρ.pull (E.write (ρ.dst d) v) = (ρ.pull E).write d v := by
  obtain ⟨j, hj⟩ := d
  subst hj
  apply env_ext
  · funext i
    exact ρ.arg_stable E i j v
  · funext i
    by_cases hij : i = j
    · subst i
      simp [pull, dst, Env.write, Env.set, Env.read]
      apply eq_of_heq
      exact (eqRec_heq _ _).trans (eqRec_heq _ _)
    · have hmap : ρ.val i ≠ ρ.val j := fun h => hij (ρ.injective h)
      simp [pull, dst, Env.write, Env.set, Env.read, hij, hmap]

def Embedding.renaming (ρ : Embedding Γ Δ) : Renaming Γ Δ where
  reg := ρ.reg
  dst := ρ.dst
  pull := ρ.pull
  read := ρ.read
  write := ρ.write

end Agave.Ed25519.SmallOrder.Execution.Transport
