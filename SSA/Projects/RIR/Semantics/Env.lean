module

public import SSA.Projects.RIR.SimpSets
public import SSA.Projects.RIR.Context

namespace LeanMLIR.RIR

@[expose] public section

structure Env (Γ : Ctx) where
  args : (i : Fin Γ.args.length) → ⟦Γ.args[i]⟧
  vals : (i : Fin Γ.vals.length) → ⟦Γ.vals[i]⟧

/-- `⟪Γ⟫` is the `Env` of `Γ`, functions mapping the args
  and vals to a value of the correct type --/
notation "⟪" Γ "⟫" => LeanMLIR.RIR.Env Γ

namespace Env

def init {Γ : Ctx} (args : (i : Fin Γ.args.length) → ⟦Γ.args[i]⟧) : ⟪Γ⟫ :=
  { args := args, vals := fun i => Γ.vals[i].poisoned }

def read (env : ⟪Γ⟫) (reg : Reg Γ t) : ⟦t⟧ :=
  match reg with
  | .arg i h => h.symm ▸ env.args i
  | .val i h => h.symm ▸ env.vals i

def set (env : ⟪Γ⟫) (i : Fin Γ.vals.length) (v : ⟦Γ.vals[i]⟧) : ⟪Γ⟫ :=
  { env with vals := fun j => if h : j = i then h ▸ v else env.vals j }

def write (env : ⟪Γ⟫) (dst : Dst Γ t) (v : ⟦t⟧) : ⟪Γ⟫ :=
  set env dst.i (dst.h.symm ▸ v)

section Lemmas

@[simp, mlir_env]
theorem read_set_self (env : ⟪Γ⟫) : (env.set i v).read (.val (t := t) i ht) = ht ▸ v := by
  simp [set, read]

@[simp, mlir_env]
theorem read_set_ne (env : ⟪Γ⟫) (h : i ≠ j) :
    (env.set i v).read (.val j ht) = env.read (.val j ht) := by simp [set, read, h.symm]

@[simp, mlir_env]
theorem set_set (env : ⟪Γ⟫) : (env.set i v).set i w = env.set i w := by
  simp [set]
  ext j
  split <;> rfl

theorem set_comm (env : ⟪Γ⟫) (h : i ≠ j) : (env.set i v).set j w = (env.set j w).set i v := by
  simp [set]
  ext k
  split <;> try rfl
  rename_i hkj
  simp [h.symm, hkj]

end Lemmas

end Env

end

end LeanMLIR.RIR
