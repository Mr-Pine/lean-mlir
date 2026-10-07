module

public import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Program
import all SSA.Projects.RIR.Semantics.Func

/-! Exact empty-input path: no memory access and no compression call, even
when the supplied context/data pointers are poison. This is a RIR result. -/
@[expose] public section

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem zero_eval (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (context data : PoisonOr Pointer) (s : GlobalState) :
    (program core).eval 2 (program.args context data (.value 0#64)) s =
      .value (some (.cons context .nil), s) := by
  rfl

theorem zero_run (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (context data : PoisonOr Pointer) (s : GlobalState) :
    (program core).run (program.args context data (.value 0#64)) s =
      .value (.cons context .nil, s) :=
  Func.run_eq_of_eval _ _ _ (zero_eval core context data s)

theorem zero_call (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (context data : PoisonOr Pointer) (s : GlobalState) (hwf : s.WF) :
    (program core).call (program.args context data (.value 0#64)) s =
      .value (.cons context .nil, s) := by
  simpa only [GlobalState.eraseFrom_self hwf] using
    Func.call_of_run (zero_run core context data s)

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append

end
