module

public import MLIR.Instruction
public import MLIR.Semantics.Env
public import MLIR.Semantics.Effectful.EffectM

namespace MLIR

@[expose] public section

inductive Vals : List Ty → Type
  | nil : Vals []
  | cons (v : ⟦t⟧) (vs : Vals ts) : Vals (t :: ts)

def Regs.read (env : ⟪Γ⟫) : (Regs Γ tys) → Vals tys
  | nil => Vals.nil
  | cons r rs => Vals.cons (env.read r) (rs.read env)

end

end MLIR
