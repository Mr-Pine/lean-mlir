module

public import SSA.Projects.RIR.GlobalInitializer
public import SSA.Projects.RIR.Semantics.Func

namespace LeanMLIR.RIR

public section

def GlobalInitializer.value (initializer : GlobalInitializer) := do
  let (_, blockVal) ←
    initializer.block.run (fun _ : Fin 1 => Dsts.nil)
        (Env.init
          (fun i => by
            simp [initializer.hΓ] at i
            exact i.elim0))
  let .inl (Vals.cons v Vals.nil) := blockVal | throwUB
  return v

end

end LeanMLIR.RIR
