module
public import SSA.Projects.RIR.Semantics.Func
import all SSA.Projects.RIR.Semantics.Func

@[expose] public section
namespace LeanMLIR.RIR

theorem Func.run_of_successful_evalFrom (f : Func) (args : Vals f.Γ.args) (mem : GlobalState)
    (fuel : Nat) (v : Vals f.tRets) (mout : GlobalState)
    (h : f.evalFrom fuel (Env.init args.get) ⟨0,f.hhasBlock⟩ mem = .value (some v,mout)) :
    f.run args mem = .value (v,mout) :=
  Func.run_eq_of_eval f args mem h

end LeanMLIR.RIR
