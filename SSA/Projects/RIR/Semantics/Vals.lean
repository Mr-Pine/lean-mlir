module

public import SSA.Projects.RIR.Instruction
public import SSA.Projects.RIR.Semantics.Env
public import SSA.Projects.RIR.Semantics.Effectful.EffectM

namespace LeanMLIR.RIR

@[expose] public section

inductive Vals : List Ty → Type
  | nil : Vals []
  | cons (v : ⟦t⟧) (vs : Vals ts) : Vals (t :: ts)

@[mlir_env]
def Regs.read (env : ⟪Γ⟫) : (Regs Γ tys) → Vals tys
  | nil => Vals.nil
  | cons r rs => Vals.cons (env.read r) (rs.read env)

end

end LeanMLIR.RIR
