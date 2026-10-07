import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialCacheMemory

/-! Expose the successful original instruction-list executions, retaining the
result environment for subsequent whole-constructor composition. -/
namespace Agave.Ed25519.Tables.SerialCacheExecution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- A one-block fragment returning no values succeeds only after its exact
instruction list succeeds. No execution fact is assumed by the caller. -/
private theorem body_of_fragment {Γ : Ctx} (body : List (Instr Γ))
    (E : ⟪Γ⟫) (s final : GlobalState)
    (h : (Func.runFrom
      { Γ := Γ, tRets := [], n := 1, blockTys := fun _ => [],
        blockParams := fun _ => .nil, hhasBlock := by decide, hentry := rfl,
        blocks := fun _ => {body := body, exit := .ret .nil} }
      E ⟨0, by exact Nat.zero_lt_succ 0⟩ s) = .value (.nil, final)) :
    ∃ E', List.foldlM Instr.run E body s = .value (E', final) := by
  rw [Func.runFrom_eq] at h
  simp only [BasicBlock.run, EffectM.bind_eq] at h
  cases hb : List.foldlM Instr.run E body s with
  | poison => simp only [hb, PoisonOr.poison_bind] at h; cases h
  | value result =>
      rcases result with ⟨E', s'⟩
      simp only [hb, PoisonOr.value_bind, Exit.run, Regs.read_nil,
        EffectM.pure_eq, Func.continue] at h
      have hs : s' = final := congrArg Prod.snd (PoisonOr.value_inj.mp h)
      subst s'
      exact ⟨E', rfl⟩

/-- Exact original constants and first cache-conversion instructions. -/
theorem phase_body (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (ho : SmallRange s.mem out 160) (hi : SmallRange s.mem input 160)
    (hg : SmallRange s.mem g.address0 40) (hne : out.id ≠ input.id)
    (hng : out.id ≠ g.address0.id) (harg : E.args 1 = .value input) :
    ∃ E', List.foldlM Instr.run (E[%35 := .value out])
      (((SerialConstructor.kernel.bb0 (primitives p) g).body.take 29) ++
        (((SerialConstructor.kernel.bb0 (primitives p) g).body.drop 37).take 80)) s =
      .value (E', cacheState s out input g.address0) :=
  body_of_fragment _ _ _ _ (phase_run p g E s out input hwf ho hi hg hne hng harg)

/-- Exact original constants and successor cache-conversion instructions. -/
theorem loopPhase_body (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (ho : SmallRange s.mem out 160) (hi : SmallRange s.mem input 160)
    (hg : SmallRange s.mem g.address0 40) (hne : out.id ≠ input.id)
    (hng : out.id ≠ g.address0.id) :
    ∃ E', List.foldlM Instr.run (loopInput E out input)
      (((SerialConstructor.kernel.bb0 (primitives p) g).body.take 29) ++
        (((SerialConstructor.kernel.bb2 (primitives p)).body.drop 10).take 57)) s =
      .value (E', cacheState s out input g.address0) :=
  body_of_fragment _ _ _ _ (loopPhase_run p g E s out input hwf ho hi hg hne hng)

end Agave.Ed25519.Tables.SerialCacheExecution
