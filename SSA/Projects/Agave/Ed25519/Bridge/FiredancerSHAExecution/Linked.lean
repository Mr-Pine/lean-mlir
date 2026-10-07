import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Initialize
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendZero
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.InitializerLink

/-! Concrete linkage to the imported Firedancer scalar core. No abstract SHA
primitive is substituted: all core calls enter its original imported CFG.
Only initialization and empty append have execution refinements here. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution
open LeanMLIR.RIR

noncomputable def coreCall (constants : Pointer) :
    Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []) :=
  (Core.program constants).call

noncomputable def appendProgram (constants : Pointer) : Func :=
  Append.program (coreCall constants)

noncomputable def finishProgram (constants : Pointer) : Func :=
  Finish.program (coreCall constants)

/-- Actual linked C append on empty input, without any readiness or
compression-correctness assumption. Data and context may even be poison. -/
theorem append_empty_call (constants : Pointer) (context data : PoisonOr Pointer)
    (s : GlobalState) (hwf : s.WF) :
    (appendProgram constants).call (Append.program.args context data (.value 0#64)) s =
      .value (.cons context .nil, s) :=
  Append.zero_call (coreCall constants) context data s hwf

end Agave.Ed25519.Bridge.FiredancerSHAExecution
