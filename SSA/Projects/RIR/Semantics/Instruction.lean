module

public import SSA.Projects.RIR.Instruction
public import SSA.Projects.RIR.Semantics.Effectful.EffectM
public import SSA.Projects.RIR.Semantics.Env
public import SSA.Projects.RIR.Semantics.Vals
public import SSA.Projects.RIR.Semantics.Operations.Scalar

namespace LeanMLIR.RIR

public section

def BinOp.compute : BinOp t₁ t₂ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t⟧
  | and, a, b => Operation.and a b

def Instr.run (env : ⟪Γ⟫) : Instr Γ → EffectM ⟪Γ⟫
  | const v dst => pure (env.write dst (.value v))
  | binop op dst a b => pure (env.write dst (op.compute (env.read a) (env.read b)))

def Exit.run (env : ⟪Γ⟫) : Exit Γ tRets blockParams → EffectM (Vals tRets ⊕ Fin n)
  | ret regs => pure (.inl (regs.read env))

end

end LeanMLIR.RIR
