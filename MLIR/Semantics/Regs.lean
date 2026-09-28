module

public import MLIR.Instruction
public import MLIR.Semantics.Env
public import MLIR.Semantics.Vals
public import MLIR.Semantics.Effectful.EffectM

namespace MLIR

@[expose] public section

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

end MLIR
