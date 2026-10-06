import SSA.Projects.RIR.Semantics.Func

/-! A finite-rank termination argument for the branch-only CFG used by the
challenge. This proves fuel sufficiency, not absence of memory poison. -/

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR

def exitRanked {n : Nat} {Γ : Ctx} {ts : List Ty} {bt : Fin n → List Ty}
    (rank : Fin n → Nat) (current : Nat) : Exit Γ ts bt → Prop
  | .ret _ | .unreachable => True
  | .br jump => rank jump.target < current
  | .condBr _ left right => rank left.target < current ∧ rank right.target < current
  | .switch _ _ _ => False

theorem exitRanked_next {n : Nat} {Γ : Ctx} {ts : List Ty} {bt : Fin n → List Ty}
    (rank : Fin n → Nat) (current : Nat) (exit : Exit Γ ts bt)
    (params : (k : Fin n) → Dsts Γ (bt k))
    (env env' : ⟪Γ⟫) (state after : GlobalState) (next : Fin n)
    (hrank : exitRanked rank current exit)
    (hexec : exit.run params env state = .value ((env', .inr next), after)) :
    rank next < current := by
  cases exit with
  | ret regs => simp [Exit.run, mlir_effect] at hexec
  | unreachable => exact False.elim (PoisonOr.poison_ne_value _ hexec)
  | br jump =>
      simp [Exit.run, Jump.run, mlir_effect] at hexec
      rcases hexec with ⟨⟨_, heq⟩, _⟩
      simpa [exitRanked, ← heq] using hrank
  | condBr cond left right =>
      cases hc : (env.read cond : PoisonOr (BitVec 1)) using PoisonOr.casesOn' with
      | poison =>
          simp [Exit.run, hc, mlir_effect] at hexec
          exact False.elim (PoisonOr.poison_ne_value _ hexec)
      | value value =>
          by_cases hv : value == 1#1
          · simp [Exit.run, hc, hv, Jump.run, mlir_effect] at hexec
            rcases hexec with ⟨⟨_, heq⟩, _⟩
            simpa [← heq] using hrank.1
          · simp [Exit.run, hc, hv, Jump.run, mlir_effect] at hexec
            rcases hexec with ⟨⟨_, heq⟩, _⟩
            simpa [← heq] using hrank.2
  | switch _ _ _ => exact False.elim hrank

theorem blockRanked_next (f : Func) (rank : Fin f.n → Nat) (block next : Fin f.n)
    (env env' : ⟪f.Γ⟫) (state after : GlobalState)
    (hrank : exitRanked rank (rank block) (f.blocks block).exit)
    (hexec : (f.blocks block).run f.blockParams env state =
      .value ((env', .inr next), after)) : rank next < rank block := by
  unfold BasicBlock.run at hexec
  cases hb : List.foldlM Instr.run env (f.blocks block).body state with
  | poison =>
      simp [EffectM.bind_eq, hb] at hexec
      exact False.elim (PoisonOr.poison_ne_value _ hexec)
  | value pair =>
      simp only [EffectM.bind_eq, hb, PoisonOr.value_bind] at hexec
      exact exitRanked_next rank (rank block) _ f.blockParams pair.1 env' pair.2 after next
        hrank hexec

/-- A strictly decreasing positive block rank prevents exhaustion. Primitive
effects remain arbitrary and may return poison; this does not silently turn
poison into success. -/
theorem evalFrom_fuel_sufficient (f : Func) (rank : Fin f.n → Nat)
    (hpositive : ∀ k, 0 < rank k)
    (hranked : ∀ k, exitRanked rank (rank k) (f.blocks k).exit)
    (fuel : Nat) (env : ⟪f.Γ⟫) (block : Fin f.n) (state after : GlobalState)
    (hbound : rank block ≤ fuel) :
    f.evalFrom fuel env block state ≠ .value (none, after) := by
  induction fuel generalizing env block state after with
  | zero => have := hpositive block; omega
  | succ fuel ih =>
      cases hb : (f.blocks block).run f.blockParams env state with
      | poison =>
          simpa [Func.evalFrom, EffectM.bind_eq, hb] using
            PoisonOr.poison_ne_value (none, after)
      | value pair =>
          rcases pair with ⟨⟨env', result⟩, state'⟩
          cases result with
          | inl result => simp [Func.evalFrom, EffectM.bind_eq, EffectM.pure_eq, hb]
          | inr next =>
              have hnext := blockRanked_next f rank block next env env' state state'
                (hranked block) hb
              simpa only [Func.evalFrom, EffectM.bind_eq, hb, PoisonOr.value_bind] using
                ih env' next state' after (by omega)

end Agave.Ed25519.Verifier.Execution.Challenge
