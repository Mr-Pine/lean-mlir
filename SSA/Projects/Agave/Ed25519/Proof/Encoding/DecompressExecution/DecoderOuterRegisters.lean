import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderOuterExecution

/-! Arguments are immutable throughout every source slice, regardless of helper
behavior or poison in intermediate register values. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.OuterComposition
open LeanMLIR.RIR
set_option linter.unusedSimpArgs false

private theorem effect_throw (s : GlobalState) :
    (throwUB : EffectM α) s = .poison := rfl

private theorem writeMany_args (E : ⟪Γ⟫) (ds : Dsts Γ ts) (vs : Vals ts) :
    (E.writeMany ds vs).args = E.args := by
  induction ds generalizing E with
  | nil => cases vs; rfl
  | cons d ds ih =>
    cases vs with
    | cons v vs => exact ih (E.write d v) vs

/-- An instruction cannot assign a function argument, including an arbitrary
external helper instruction. This statement assumes only a successful step. -/
theorem instruction_args (i : Instr Γ) (E E' : ⟪Γ⟫) (s t : GlobalState)
    (h : Instr.run E i s = .value (E', t)) : E'.args = E.args := by
  cases i
  all_goals
    try
      simp only [Instr.run, EffectM.pure_eq, EffectM.bind_eq, EffectM.get_eq,
        LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.value_inj, Prod.mk.injEq] at h
      exact (congrArg Env.args h.1).symm
  case alloca dst bytes =>
    change LeanMLIR.RIR.PoisonOr.value (E.write dst (.value s.allocaPtr), s.alloca bytes) = LeanMLIR.RIR.PoisonOr.value (E', t) at h
    exact (congrArg Env.args (congrArg Prod.fst (LeanMLIR.RIR.PoisonOr.value_inj.mp h))).symm
  case call f args rets =>
    simp only [Instr.run, EffectM.bind_eq, EffectM.pure_eq] at h
    cases hc : f (args.read E) s <;>
      simp only [hc, LeanMLIR.RIR.PoisonOr.value_bind,
        LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value,
        LeanMLIR.RIR.PoisonOr.value_inj, Prod.mk.injEq] at h
    simpa only [writeMany_args] using (congrArg Env.args h.1).symm
  case assume cond =>
    cases h0 : E.read cond using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals simp only [Instr.run, Operation.load, Operation.store, Operation.memset,
      Operation.memcpy, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
      EffectM.set_eq, LeanMLIR.RIR.PoisonOr.value_bind,
      LeanMLIR.RIR.PoisonOr.poison_bind] at h
    all_goals simp only [h0] at h
    all_goals
      try simp only [throwUBIf, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
        EffectM.set_eq, effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
        LeanMLIR.RIR.PoisonOr.poison_bind] at h
      try split_ifs at h
      all_goals
        try simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq, EffectM.set_eq,
          effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
          LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value,
          LeanMLIR.RIR.PoisonOr.value_inj, Prod.mk.injEq] at h
      all_goals simpa only [Env.write_args, writeMany_args] using (congrArg Env.args h.1).symm
  case load dst p =>
    cases h0 : E.read p using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals simp only [Instr.run, Operation.load, Operation.store, Operation.memset,
      Operation.memcpy, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
      EffectM.set_eq, LeanMLIR.RIR.PoisonOr.value_bind,
      LeanMLIR.RIR.PoisonOr.poison_bind] at h
    all_goals simp only [h0] at h
    all_goals
      try simp only [throwUBIf, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
        EffectM.set_eq, effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
        LeanMLIR.RIR.PoisonOr.poison_bind] at h
      try split_ifs at h
      all_goals
        try simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq, EffectM.set_eq,
          effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
          LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value,
          LeanMLIR.RIR.PoisonOr.value_inj, Prod.mk.injEq] at h
      all_goals simpa only [Env.write_args, writeMany_args] using (congrArg Env.args h.1).symm
  case loadMonotonic dst p =>
    cases h0 : E.read p using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals simp only [Instr.run, Operation.load, Operation.store, Operation.memset,
      Operation.memcpy, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
      EffectM.set_eq, LeanMLIR.RIR.PoisonOr.value_bind,
      LeanMLIR.RIR.PoisonOr.poison_bind] at h
    all_goals simp only [h0] at h
    all_goals
      try simp only [throwUBIf, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
        EffectM.set_eq, effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
        LeanMLIR.RIR.PoisonOr.poison_bind] at h
      try split_ifs at h
      all_goals
        try simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq, EffectM.set_eq,
          effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
          LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value,
          LeanMLIR.RIR.PoisonOr.value_inj, Prod.mk.injEq] at h
      all_goals simpa only [Env.write_args, writeMany_args] using (congrArg Env.args h.1).symm
  case store p v =>
    cases h0 : E.read p using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals cases h1 : Ty.flatten _ (E.read v) using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals simp only [Instr.run, Operation.load, Operation.store, Operation.memset,
      Operation.memcpy, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
      EffectM.set_eq, LeanMLIR.RIR.PoisonOr.value_bind,
      LeanMLIR.RIR.PoisonOr.poison_bind] at h
    all_goals simp only [h0, h1] at h
    all_goals
      try simp only [throwUBIf, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
        EffectM.set_eq, effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
        LeanMLIR.RIR.PoisonOr.poison_bind] at h
      try split_ifs at h
      all_goals
        try simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq, EffectM.set_eq,
          effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
          LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value,
          LeanMLIR.RIR.PoisonOr.value_inj, Prod.mk.injEq] at h
      all_goals simpa only [Env.write_args, writeMany_args] using (congrArg Env.args h.1).symm
  case memset dst val len =>
    cases h0 : E.read dst using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals cases h1 : E.read val using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals cases h2 : E.read len using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals simp only [Instr.run, Operation.load, Operation.store, Operation.memset,
      Operation.memcpy, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
      EffectM.set_eq, LeanMLIR.RIR.PoisonOr.value_bind,
      LeanMLIR.RIR.PoisonOr.poison_bind] at h
    all_goals simp only [h0, h1, h2] at h
    all_goals
      try simp only [throwUBIf, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
        EffectM.set_eq, effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
        LeanMLIR.RIR.PoisonOr.poison_bind] at h
      try split_ifs at h
      all_goals
        try simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq, EffectM.set_eq,
          effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
          LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value,
          LeanMLIR.RIR.PoisonOr.value_inj, Prod.mk.injEq] at h
      all_goals simpa only [Env.write_args, writeMany_args] using (congrArg Env.args h.1).symm
  case memcpy dst src len =>
    cases h0 : E.read dst using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals cases h1 : E.read src using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals cases h2 : E.read len using LeanMLIR.RIR.PoisonOr.casesOn'
    all_goals simp only [Instr.run, Operation.load, Operation.store, Operation.memset,
      Operation.memcpy, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
      EffectM.set_eq, LeanMLIR.RIR.PoisonOr.value_bind,
      LeanMLIR.RIR.PoisonOr.poison_bind] at h
    all_goals simp only [h0, h1, h2] at h
    all_goals
      try simp only [throwUBIf, EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq,
        EffectM.set_eq, effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
        LeanMLIR.RIR.PoisonOr.poison_bind] at h
      try split_ifs at h
      all_goals
        try simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq, EffectM.set_eq,
          effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
          LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value,
          LeanMLIR.RIR.PoisonOr.value_inj, Prod.mk.injEq] at h
      all_goals
        repeat' (split_ifs at h <;>
          simp only [EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq, EffectM.set_eq,
            effect_throw, LeanMLIR.RIR.PoisonOr.pure_def, LeanMLIR.RIR.PoisonOr.value_bind,
            LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value,
            LeanMLIR.RIR.PoisonOr.value_inj, Prod.mk.injEq] at h)
      all_goals simpa only [Env.write_args, writeMany_args] using (congrArg Env.args h.1).symm

/-- Successful finite source execution retains the original argument vector. -/
theorem segment_args (f : Func) (block : Fin f.n) (first count : Nat)
    (E E' : ⟪f.Γ⟫) (s t : GlobalState)
    (h : Cutpoint.segment f block first count E s = .value (E', t)) :
    E'.args = E.args := by
  unfold Cutpoint.segment at h
  generalize (List.take count (List.drop first (f.blocks block).body)) = code at h
  induction code generalizing E s with
  | nil =>
    simp only [List.foldlM_nil, EffectM.pure_eq, LeanMLIR.RIR.PoisonOr.value_inj,
      Prod.mk.injEq] at h
    exact congrArg Env.args h.1.symm
  | cons inst rest ih =>
    simp only [List.foldlM_cons, EffectM.bind_eq] at h
    cases step : Instr.run E inst s with
    | poison => simp only [step, LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value] at h
    | value pair =>
      rcases pair with ⟨F, u⟩
      simp only [step, LeanMLIR.RIR.PoisonOr.value_bind] at h
      exact (ih F u h).trans (instruction_args inst E F s u step)

theorem pieces_args (f : Func) (block : Fin f.n) (first : Nat) (counts : List Nat)
    (E E' : ⟪f.Γ⟫) (s t : GlobalState)
    (h : pieces f block first counts E s = .value (E', t)) : E'.args = E.args := by
  induction counts generalizing first E s with
  | nil =>
    simp only [pieces, EffectM.pure_eq, LeanMLIR.RIR.PoisonOr.value_inj,
      Prod.mk.injEq] at h
    exact congrArg Env.args h.1.symm
  | cons count rest ih =>
    simp only [pieces, EffectM.bind_eq] at h
    cases step : Cutpoint.segment f block first count E s with
    | poison => simp only [step, LeanMLIR.RIR.PoisonOr.poison_bind, LeanMLIR.RIR.PoisonOr.poison_ne_value] at h
    | value pair =>
      rcases pair with ⟨F, u⟩
      simp only [step, LeanMLIR.RIR.PoisonOr.value_bind] at h
      exact (ih (first + count) F u h).trans (segment_args f block first count E F s u step)

end Agave.Ed25519.Encoding.Decompress.Execution.OuterComposition

namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR

namespace Decode

theorem outerEntryPrefix_outputRegister (p : Primitives) (g : Globals)
    (E E' : ⟪program.Γ⟫) (s t : GlobalState) (out : Pointer)
    (hout : E.read (%arg0) = .value out)
    (hprefix : outerEntryPrefix p g E s = .value (E', t)) :
    E'.read (%arg0) = .value out := by
  have hargs := OuterComposition.segment_args (program p g) 0 0 137 E E' s t hprefix
  change E'.args 0 = .value out
  change E.args 0 = .value out at hout
  rw [hargs]
  exact hout

theorem outerSuccessPrefix_outputRegister (p : Primitives) (g : Globals)
    (E E' : ⟪program.Γ⟫) (s t : GlobalState) (out : Pointer)
    (hout : E.read (%arg0) = .value out)
    (hprefix : outerSuccessPrefix p g E s = .value (E', t)) :
    E'.read (%arg0) = .value out := by
  have hargs := OuterComposition.segment_args (program p g) 1 0 50 E E' s t hprefix
  change E'.args 0 = .value out
  change E.args 0 = .value out at hout
  rw [hargs]
  exact hout

end Decode

namespace SqrtRatio

theorem executionPrefix_outputRegister (g : Globals)
    (E E' : ⟪program.Γ⟫) (s t : GlobalState) (out : Pointer)
    (hout : E.read (%arg0) = .value out)
    (hprefix : executionPrefix g E s = .value (E', t)) :
    E'.read (%arg0) = .value out := by
  have hargs := OuterComposition.pieces_args (program sqrtRatioPrimitives g)
    0 0 executionPieceLengths E E' s t hprefix
  change E'.args 0 = .value out
  change E.args 0 = .value out at hout
  rw [hargs]
  exact hout

end SqrtRatio
end Agave.Ed25519.Encoding.Decompress.Execution
