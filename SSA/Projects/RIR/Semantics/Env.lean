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

@[mlir_env]
theorem read_write_self (env : ⟪Γ⟫) (dst : Dst Γ t) :
    (env.write dst v).read (.val dst.i dst.h) = dst.h ▸ v := by
  unfold Env.write
  apply read_set_self

@[mlir_env]
theorem read_write_self' (env : ⟪Γ⟫) : (env.write ⟨i, h⟩ v).read (.val i h) = h ▸ v := by
  apply read_write_self

@[mlir_env]
theorem read_write_ne (env : ⟪Γ⟫) (dst : Dst Γ t) (h : i ≠ dst.i := by decide) :
    (env.write dst v).read (.val (t := t') i ht') = env.read (.val i ht') := by
  unfold Env.write
  apply read_set_ne env h.symm

@[mlir_env]
theorem read_write_ne' (env : ⟪Γ⟫) (hij : i ≠ j := by decide) :
    (env.write ⟨i, h⟩ v).read (.val (t := t') j ht') = env.read (.val j ht') := by
  apply read_write_ne
  apply hij.symm

@[mlir_env]
theorem read_write_arg (env : ⟪Γ⟫) (dst : Dst Γ t) :
    (env.write dst v).read (.arg i h) = env.read (.arg i h) := by rfl

@[mlir_env]
theorem read_init_arg (args : _) : (Env.init args).read (.arg i h) = args i := by rfl

end Lemmas

end Env

end

end LeanMLIR.RIR
