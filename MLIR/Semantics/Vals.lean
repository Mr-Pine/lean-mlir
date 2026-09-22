module

public import MLIR.Instruction
public import MLIR.Semantics.Env
public import MLIR.Semantics.Effectful.EffectM

namespace MLIR

@[expose] public section

inductive Vals : List Ty → Type
  | nil : Vals []
  | cons (v : ⟦t⟧) (vs : Vals ts) : Vals (t :: ts)

@[mlir_env]
def Regs.read (env : ⟪Γ⟫) : (Regs Γ tys) → Vals tys
  | nil => Vals.nil
  | cons r rs => Vals.cons (env.read r) (rs.read env)

theorem Regs.read_cons : (Regs.cons r rs).read env = Vals.cons (env.read r) (rs.read env) :=
  rfl

end

end MLIR
