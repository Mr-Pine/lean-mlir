module

public import MLIR.Instruction
public import MLIR.Semantics.Effectful.EffectM
public import MLIR.Semantics.Env
public import MLIR.Semantics.Vals
public import MLIR.Semantics.Operations.Scalar
public import MLIR.SimpSets

namespace MLIR

@[expose] public section

@[mlir_instr]
def BinOp.compute : BinOp t₁ t₂ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t⟧
  | and => Operation.and
  | smin => Operation.smin

@[mlir_instr]
def Instr.run (env : ⟪Γ⟫) : Instr Γ → EffectM ⟪Γ⟫
  | const v dst => pure (env.write dst (.value v))
  | binop op dst a b => pure (env.write dst (op.compute (env.read a) (env.read b)))

@[mlir_instr]
def Exit.run (env : ⟪Γ⟫) : Exit Γ tRets blockParams → EffectM (Vals tRets ⊕ Fin n)
  | ret regs => pure (.inl (regs.read env))

end

end MLIR
