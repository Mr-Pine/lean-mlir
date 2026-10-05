module

public import SSA.Projects.RIR.Context
public import SSA.Projects.RIR.Instruction
public import SSA.Projects.RIR.Func

namespace LeanMLIR.RIR

@[expose] public section

/-- A constant global's initializer region: one block without arguments that returns the
global's value of type `t`. -/
structure GlobalInitializer where
  Γ : Ctx
  hΓ : Γ.args = []
  t : Ty
  block : BasicBlock Γ [t] (fun _ : Fin 1 => [])

end

end LeanMLIR.RIR
