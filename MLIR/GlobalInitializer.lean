module

public import MLIR.Context
public import MLIR.Instruction
public import MLIR.Func

namespace MLIR

@[expose] public section

/-- A constant global's initializer region: one block without arguments that returns the
global's value of type `t`. -/
structure GlobalInitializer where
  Γ : Ctx
  hΓ : Γ.args = []
  t : Ty
  block : BasicBlock Γ [t] (fun _ : Fin 1 => [])

end

end MLIR
