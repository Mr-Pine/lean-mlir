module

public import SSA.Projects.RIR.Instruction
public import SSA.Projects.RIR.Semantics.Env
public import SSA.Projects.RIR.Semantics.Effectful.EffectM

namespace LeanMLIR.RIR

@[expose] public section

inductive Vals : List Ty → Type
  | nil : Vals []
  | cons (v : ⟦t⟧) (vs : Vals ts) : Vals (t :: ts)

def Regs.read (env : ⟪Γ⟫) : (Regs Γ tys) → Vals tys
  | nil => Vals.nil
  | cons r rs => Vals.cons (env.read r) (rs.read env)

@[simp, mlir_env]
theorem Regs.read_cons : (Regs.cons r rs).read env = Vals.cons (env.read r) (rs.read env) :=
  rfl

@[simp, mlir_env]
theorem Regs.read_nil : (Regs.nil).read env = Vals.nil :=
  rfl

end

end LeanMLIR.RIR
