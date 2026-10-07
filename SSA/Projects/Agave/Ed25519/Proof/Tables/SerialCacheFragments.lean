import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorStack

/-! Cache fragments with their original instruction boundaries and saved
register frames, suitable for whole-constructor composition. -/
namespace Agave.Ed25519.Tables.SerialCacheExecution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open DoubleBase.RIR (PrefixEq)
open SerialConstructorRegisters
open SerialConstructorStack (constants constants_run)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev firstBody (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals) :=
  ((SerialConstructor.kernel.bb0 (primitives p) g).body.drop 37).take 80

abbrev successorBody (p : SerialConstructor.Primitives) :=
  ((SerialConstructor.kernel.bb2 (primitives p)).body.drop 10).take 57

theorem firstBody_above (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals) :
    ∀ i ∈ firstBody p g, Instr.above 37 i := by
  simp [firstBody, SerialConstructor.kernel.bb0, Instr.above, Dsts.above]

theorem successorBody_above (p : SerialConstructor.Primitives) :
    ∀ i ∈ successorBody p, Instr.above 143 i := by
  simp [successorBody, SerialConstructor.kernel.bb2, Instr.above, Dsts.above]

/-- The successful initial cache body retains every incoming scratch pointer. -/
theorem firstBody_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (ho : SmallRange s.mem out 160) (hi : SmallRange s.mem input 160)
    (hg : SmallRange s.mem g.address0 40) (hne : out.id ≠ input.id)
    (hng : out.id ≠ g.address0.id) (harg : E.args 1 = .value input)
    (hout : E.read (%35) = .value out) (hc : constants E g = E) :
    ∃ E', List.foldlM Instr.run E (firstBody p g) s =
      .value (E', cacheState s out input g.address0) ∧ PrefixEq E E' 37 := by
  obtain ⟨E', hr⟩ := phase_body p g E s out input hwf ho hi hg hne hng harg
  rw [Env.write_of_read E (%35) hout, List.foldlM_append, EffectM.bind_eq,
    constants_run, hc, PoisonOr.value_bind] at hr
  exact ⟨E', hr, body_prefix _ (firstBody_above p g) _ _ _ _ hr⟩

/-- The successor cache body retains the loop cursor and all saved addresses. -/
theorem successorBody_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (ho : SmallRange s.mem out 160) (hi : SmallRange s.mem input 160)
    (hg : SmallRange s.mem g.address0 40) (hne : out.id ≠ input.id)
    (hng : out.id ≠ g.address0.id)
    (hinput : loopInput E out input = E) (hc : constants E g = E) :
    ∃ E', List.foldlM Instr.run E (successorBody p) s =
      .value (E', cacheState s out input g.address0) ∧ PrefixEq E E' 143 := by
  obtain ⟨E', hr⟩ := loopPhase_body p g E s out input hwf ho hi hg hne hng
  rw [hinput, List.foldlM_append, EffectM.bind_eq, constants_run, hc,
    PoisonOr.value_bind] at hr
  exact ⟨E', hr, body_prefix _ (successorBody_above p) _ _ _ _ hr⟩

end Agave.Ed25519.Tables.SerialCacheExecution
