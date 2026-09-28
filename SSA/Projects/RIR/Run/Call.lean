module

public import SSA.Projects.RIR.Semantics.Func

namespace LeanMLIR.RIR

public section

/-- A call whose callee returns `rs` in `s'` writes them to `rets`. -/
theorem run_call {f : Vals ts → EffectM (Vals us)} {rets : Dsts Γ us} {env : ⟪Γ⟫}
    (h : f vs s = .value (rs, s')) :
    (do
          let r ← f vs;
          pure (env.writeMany rets r) : EffectM ⟪Γ⟫)
        s =
      .value (env.writeMany rets rs, s') := by
  simp [h]

/-- A frame-free callee: when `run` allocates nothing, `call` has the same result. -/
theorem Func.call_eq_of_run_eq {f : Func} {args : Vals f.Γ.args} {r : Vals f.tRets}
    {s t : GlobalState} (h : f.run args s = .value (r, t)) (hwf : t.WF)
    (halloc : t.alloc = s.alloc) : f.call args s = .value (r, t) := by
  rw [Func.call_of_run h, ← halloc]
  rw [GlobalState.eraseFrom_self hwf]

end

end LeanMLIR.RIR
