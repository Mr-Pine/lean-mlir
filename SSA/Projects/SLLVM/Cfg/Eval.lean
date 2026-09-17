/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.SLLVM.Cfg.Basic

/-!
# The fueled interpreter agrees with the denotation

`Cfg.denote` takes a classical limit over fuel; `Cfg.eval` is the computable
interpreter `#guard` tests run. This file connects them:

- fuel monotonicity: a completed result never changes with more fuel
  (`BlockCom.eval_mono`, `Blocks.iterate_mono`);
- the master theorem `BlockCom.run_denote`: the denotation *is* the limit of
  the fueled interpreter, pointwise in the state;
- `Blocks.run_step`: one block transition of `run`, in terms of the entered
  block's `denote` -- the equation loop proofs walk with;
- `Cfg.eval_sound`: a completed `Cfg.eval` result is the denotation.
-/

@[expose] public section

namespace LeanMLIR.SLLVM

/-! ## `FuelMono` -/

theorem FuelMono.of_succ {f : Nat → Option α} (h : ∀ n r, f n = some r → f (n + 1) = some r) :
    FuelMono f := by
  intro m n hmn r hm
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ n _ ih => exact h n r ih

theorem FuelMono.const {x : Option α} : FuelMono (fun _ => x) := fun _ _ _ _ h => h

/-! ## `Fuel.limit` -/

namespace Fuel

/-- `limit` returns a value only if some fuel reaches it. -/
theorem exists_of_limit_eq_some {f : Nat → Option α} {r : α} (h : limit f = some r) :
    ∃ n, f n = some r := by
  unfold limit at h
  split at h
  · exact ⟨_, h⟩
  · exact absurd h (by simp)

theorem limit_eq_none_iff {f : Nat → Option α} : limit f = none ↔ ∀ n, f n = none := by
  constructor
  · intro h n
    cases hn : f n with
    | none => rfl
    | some r =>
      unfold limit at h
      rw [dif_pos ⟨n, by simp [hn]⟩] at h
      exact
        absurd h
          (by
            have := Nat.find_spec (⟨n, by simp [hn]⟩ : ∃ n, (f n).isSome)
            simpa [Option.isSome_iff_ne_none] using this)
  · intro h
    unfold limit
    rw [dif_neg]
    rintro ⟨n, hn⟩
    simp [h n] at hn

/-- With monotonicity, any completed result is the limit. -/
theorem limit_eq_of {f : Nat → Option α} (hf : FuelMono f) {n : Nat} {r : α} (h : f n = some r) :
    limit f = some r := by
  unfold limit
  have hex : ∃ n, (f n).isSome := ⟨n, by simp [h]⟩
  rw [dif_pos hex]
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
  rcases le_total (Nat.find hex) n with hle | hle
  · have h2 := hf hle hr'
    rw [h] at h2
    rw [hr', Option.some.injEq]
    exact (Option.some.inj h2).symm
  · exact hf hle h

theorem limit_const {x : Option α} : limit (fun _ => x) = x := by
  cases x with
  | none => exact limit_eq_none_iff.mpr fun _ => rfl
  | some r => exact limit_eq_of .const (n := 0) rfl

/-- Dropping the first step does not change the limit of a monotone chain. -/
theorem limit_shift {f : Nat → Option α} (hf : FuelMono f) :
    limit (fun n => f (n + 1)) = limit f := by
  cases hlim : limit f with
  | some r =>
    obtain ⟨n, hn⟩ := exists_of_limit_eq_some hlim
    exact limit_eq_of (fun _ _ hmn r hm => hf (by omega) hm) (hf (Nat.le_succ n) hn)
  | none =>
    rw [limit_eq_none_iff] at hlim ⊢
    exact fun n => hlim (n + 1)

theorem andThen_le {x x' : Option (PoisonOr α)} {k k' : α → Option (PoisonOr β)}
    (hx : ∀ r, x = some r → x' = some r) (hk : ∀ a r, k a = some r → k' a = some r) :
    ∀ r, andThen x k = some r → andThen x' k' = some r := by
  intro r h
  match x, h with
  | some .poison, h =>
    rw [hx _ rfl]; exact h
  | some (.value a), h =>
    rw [hx _ rfl]; exact hk a r h

theorem mono_andThen {f : Nat → Option (PoisonOr α)} {g : Nat → α → Option (PoisonOr β)}
    (hf : FuelMono f) (hg : ∀ a, FuelMono (g · a)) : FuelMono (fun n => andThen (f n) (g n)) :=
  fun _ _ hmn _ h => andThen_le (fun _ hr => hf hmn hr) (fun a _ hr => hg a hmn hr) _ h

/-- The limit distributes over `andThen`: run the first stage to its limit,
then the second. -/
theorem limit_andThen {f : Nat → Option (PoisonOr α)} {g : Nat → α → Option (PoisonOr β)}
    (hf : FuelMono f) (hg : ∀ a, FuelMono (g · a)) :
    limit (fun n => andThen (f n) (g n)) = andThen (limit f) (fun a => limit (g · a)) := by
  cases hlf : limit f with
  | none =>
    rw [limit_eq_none_iff] at hlf
    simpa using limit_eq_none_iff.mpr fun n => by simp [hlf n]
  | some r =>
    obtain ⟨n₀, hn₀⟩ := exists_of_limit_eq_some hlf
    cases r with
    | poison =>
      rw [andThen_poison]
      exact limit_eq_of (mono_andThen hf hg) (n := n₀) (by simp [hn₀])
    | value a =>
      rw [andThen_value]
      cases hlg : limit (g · a) with
      | some r =>
        obtain ⟨m, hm⟩ := exists_of_limit_eq_some hlg
        refine limit_eq_of (mono_andThen hf hg) (n := max n₀ m) ?_
        rw [hf (le_max_left n₀ m) hn₀, andThen_value]
        exact hg a (le_max_right n₀ m) hm
      | none =>
        rw [limit_eq_none_iff] at hlg ⊢
        intro n
        cases hn : f n with
        | none => simp [Fuel.andThen]
        | some
          r' =>
          have hr' : r' = .value a := by
            rcases le_total n n₀ with hle | hle
            · have h2 := hf hle hn
              rw [hn₀] at h2
              exact (Option.some.inj h2).symm
            · have h2 := hf hle hn₀
              rw [hn] at h2
              exact Option.some.inj h2
          subst hr'
          simp [Fuel.andThen, hlg n]

end Fuel

/-! ## Fuel monotonicity of the interpreter -/

mutual

theorem BlockCom.eval_succ {n : Nat} :
    ∀ {Γ Γout : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty} {all : List (List SLLVM.Ty)}
      (c : BlockCom Γ Γout rets all) (V : Γ.Valuation) (s : GlobalState) {r}
      (_ : c.eval n V s = some r), c.eval (n + 1) V s = some r
  | _, _, _, _, .term t, V, s, r, h => by
      simp only [BlockCom.eval] at h ⊢
      exact h
  | _, _, _, _, .var e body, V, s, r, h => by
      simp only [BlockCom.eval] at h ⊢
      exact Fuel.andThen_le (fun _ hr => hr)
        (fun p _ hr => body.eval_succ p.1 p.2 hr) _ h
  | _, _, _, _, .call callee centry cblocks args body, V, s, r, h => by
      simp only [BlockCom.eval] at h ⊢
      refine Fuel.andThen_le ?_ (fun p _ hr => body.eval_succ _ _ hr) _ h
      intro r₁ h₁
      exact Fuel.andThen_le (fun _ hr => centry.eval_succ _ _ hr)
        (fun p _ hr => Blocks.next_succ p.1.1 p.1.2 p.2 hr) _ h₁
  termination_by _ _ _ _ c _ _ _ _ => (n, sizeOf c, 0)

theorem Blocks.iterate_succ {n : Nat} {Γamb : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty}
    {all : List (List SLLVM.Ty)}
    (bs : Blocks Γamb rets all all) (Vamb : Γamb.Valuation) (t : SuccArgs all)
    (s : GlobalState) {r} (h : bs.iterate n Vamb t s = some r) :
    bs.iterate (n + 1) Vamb t s = some r := by
  match n, h with
  | 0, h => rw [Blocks.iterate] at h; exact absurd h (by simp)
  | m + 1, h => ?_
  rw [Blocks.iterate] at h
  rw [Blocks.iterate]
  exact Fuel.andThen_le (fun _ hr => BlockCom.eval_succ _ _ _ hr)
    (fun p _ hr => Blocks.next_succ Vamb p.1.2 p.2 hr) _ h
  termination_by (n, 0, 0)

theorem Blocks.next_succ {n : Nat} {Γamb : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty}
    {all : List (List SLLVM.Ty)} {bs : Blocks Γamb rets all all}
    (Vamb : Γamb.Valuation) (t : HVector toType rets ⊕ SuccArgs all)
    (s : GlobalState) {r} (h : bs.next n Vamb t s = some r) :
    bs.next (n + 1) Vamb t s = some r := by
  match t with
  | .inl rets => rw [Blocks.next] at h ⊢; exact h
  | .inr t =>
      rw [Blocks.next] at h ⊢
      exact bs.iterate_succ Vamb t s h
  termination_by (n, 0, 1)

end

theorem BlockCom.eval_mono {c : BlockCom Γ Γout rets all} {V : Γ.Valuation} {s : GlobalState} :
    FuelMono (fun n => c.eval n V s) :=
  FuelMono.of_succ fun _ _ => c.eval_succ V s

theorem Blocks.iterate_mono {bs : Blocks Γamb rets all all} {Vamb : Γamb.Valuation}
    {t : SuccArgs all} {s : GlobalState} : FuelMono (fun n => bs.iterate n Vamb t s) :=
  FuelMono.of_succ fun _ _ => bs.iterate_succ Vamb t s

theorem Blocks.next_mono {bs : Blocks Γamb rets all all} {Vamb : Γamb.Valuation}
    {t : HVector toType rets ⊕ SuccArgs all} {s : GlobalState} :
    FuelMono (fun n => bs.next n Vamb t s) :=
  FuelMono.of_succ fun _ _ => Blocks.next_succ Vamb t s

/-! ## The master theorem -/

/-- `runFunction` propagates UB. The value case is `run_runFunction`. -/
theorem run_runFunction_poison {α : Type} {body : EffectM α} {s : GlobalState}
    (h : StateT.run body s = .poison) : StateT.run (runFunction body) s = .poison := by
  simp only [runFunction, EffectM.run_bind, run_getThe_state, PoisonOr.value_bind, h]
  rfl

/-- `Blocks.run` is *defined* as the limit of `Blocks.iterate`; restated for
rewriting. -/
theorem Blocks.run_eq_limit {bs : Blocks Γamb rets all all} {Vamb : Γamb.Valuation}
    {t : SuccArgs all} {s : GlobalState} :
    StateT.run (bs.run Vamb t) s = Fuel.force (Fuel.limit fun n => bs.iterate n Vamb t s) :=
  rfl

/-- The limit of the dispatch continuation, in `denote` terms. -/
theorem Blocks.force_limit_next {bs : Blocks Γamb rets all all} {Vamb : Γamb.Valuation}
    {t : HVector toType rets ⊕ SuccArgs all} {s : GlobalState} :
    Fuel.force (Fuel.limit fun n => bs.next n Vamb t s) =
      StateT.run
        (match t with
        | .inl rets => pure rets
        | .inr t => bs.run Vamb t)
        s := by
  cases t with
  | inl
    rets =>
    have : (fun n => bs.next n Vamb (.inl rets) s) = fun _ => some (.value (rets, s)) :=
      funext fun n => by rw [Blocks.next]
    rw [this, Fuel.limit_const]
    rfl
  | inr
    t =>
    have : (fun n => bs.next n Vamb (.inr t) s) = fun n => bs.iterate n Vamb t s :=
      funext fun n => by rw [Blocks.next]
    rw [this]
    rfl

/-- The denotation is the limit of the fueled interpreter. -/
theorem BlockCom.run_denote :
    ∀ {Γ Γout : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty} {all : List (List SLLVM.Ty)}
      (c : BlockCom Γ Γout rets all) (V : Γ.Valuation) (s : GlobalState),
      StateT.run (c.denote V) s = Fuel.force (Fuel.limit fun n => c.eval n V s)
  | _, _, _, _, .term t, V, s => by
    simp only [BlockCom.denote, BlockCom.eval, Fuel.limit_const, Fuel.force_some]
  | _, _, _, _, .var e body, V, s => by
    simp only [BlockCom.denote_var, EffectM.run_bind, BlockCom.eval]
    cases he : StateT.run (e.denote V) s with
    | poison =>
      simp only [PoisonOr.poison_bind, Fuel.andThen_poison, Fuel.limit_const, Fuel.force_some]
    | value p =>
      obtain ⟨V', s'⟩ := p
      simp only [PoisonOr.value_bind, Fuel.andThen_value]
      exact run_denote body V' s'
  | Γ, Γout, rets, all, .call callee centry cblocks args body, V, s => by
    simp only [BlockCom.denote_call, EffectM.run_bind, BlockCom.eval]
    rw [Fuel.limit_andThen (f := fun n =>
        Fuel.andThen (centry.eval n (Ctxt.Valuation.ofHVector (args.map V).reverse) s) fun p =>
          cblocks.next n p.1.1 p.1.2 p.2)
        (g := fun n p => body.eval n (p.1 ++ V) (s.popFrame p.2.mem))
        (Fuel.mono_andThen BlockCom.eval_mono fun _ => Blocks.next_mono)
        (fun _ => BlockCom.eval_mono),
      Fuel.limit_andThen (f := fun n =>
        centry.eval n (Ctxt.Valuation.ofHVector (args.map V).reverse) s) (g := fun n p =>
        cblocks.next n p.1.1 p.1.2 p.2) BlockCom.eval_mono (fun _ => Blocks.next_mono)]
    have hcentry := run_denote centry (Ctxt.Valuation.ofHVector (args.map V).reverse) s
    cases hlim :
      Fuel.limit fun n => centry.eval n (Ctxt.Valuation.ofHVector (args.map V).reverse) s with
    | none =>
      rw [hlim, Fuel.force_none] at hcentry
      rw [run_runFunction_poison
          (by
            rw [EffectM.run_bind, hcentry]; rfl)]
      simp
    | some r =>
      rw [hlim, Fuel.force_some] at hcentry
      cases r with
      | poison =>
        rw [run_runFunction_poison
            (by
              rw [EffectM.run_bind, hcentry]; rfl)]
        simp
      | value p =>
        obtain ⟨⟨Vc, rr⟩, s₁⟩ := p
        simp only [Fuel.andThen_value]
        cases rr with
        | inl
          rs =>
          have h1 : (fun n => cblocks.next n Vc (.inl rs) s₁) = fun _ => some (.value (rs, s₁)) :=
            funext fun n => by rw [Blocks.next]
          rw [h1, Fuel.limit_const]
          simp only [Fuel.andThen_value]
          rw [run_runFunction (r := rs) (s' := s₁)
              (by
                rw [EffectM.run_bind, hcentry, PoisonOr.value_bind]
                dsimp only
                exact EffectM.run_pure)]
          exact run_denote body _ (s.popFrame s₁.mem)
        | inr
          tn =>
          have h1 :
            (fun n => cblocks.next n Vc (.inr tn) s₁) = fun n => cblocks.iterate n Vc tn s₁ :=
            funext fun n => by rw [Blocks.next]
          rw [h1]
          cases hlimn : Fuel.limit fun n => cblocks.iterate n Vc tn s₁ with
          | none =>
            rw [run_runFunction_poison
                (by
                  rw [EffectM.run_bind, hcentry, PoisonOr.value_bind]
                  dsimp only
                  show StateT.run (cblocks.run Vc tn) s₁ = _
                  rw [Blocks.run_eq_limit, hlimn, Fuel.force_none])]
            simp
          | some r =>
            cases r with
            | poison =>
              rw [run_runFunction_poison
                  (by
                    rw [EffectM.run_bind, hcentry, PoisonOr.value_bind]
                    dsimp only
                    show StateT.run (cblocks.run Vc tn) s₁ = _
                    rw [Blocks.run_eq_limit, hlimn, Fuel.force_some])]
              simp
            | value q =>
              obtain ⟨rs, s₂⟩ := q
              rw [run_runFunction (r := rs) (s' := s₂)
                  (by
                    rw [EffectM.run_bind, hcentry, PoisonOr.value_bind]
                    dsimp only
                    show StateT.run (cblocks.run Vc tn) s₁ = _
                    rw [Blocks.run_eq_limit, hlimn, Fuel.force_some])]
              simp only [Fuel.andThen_value, PoisonOr.value_bind]
              exact run_denote body _ (s.popFrame s₂.mem)
termination_by _ _ _ _ c _ _ => sizeOf c

/-! ## Stepping the walk -/

/-- One transition of the block walk: enter the targeted block, run it via its
*denotation*, and either return or continue the walk. This is the equation
loop proofs step with -- note the continuation carries the whole `bs`, so
nothing unfolds. -/
theorem Blocks.run_step {bs : Blocks Γamb rets all all} {Vamb : Γamb.Valuation} {t : SuccArgs all} :
    bs.run Vamb t =
      (do
        let (_, r) ←
          (bs.get t.idx t.hidx).2.denote (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb)
        match r with
        | .inl rets =>
          pure rets
        | .inr next =>
          bs.run Vamb next) := by
  funext s
  show StateT.run (bs.run Vamb t) s = StateT.run _ s
  rw [Blocks.run_eq_limit, ← Fuel.limit_shift Blocks.iterate_mono]
  have hit :
    (fun n => bs.iterate (n + 1) Vamb t s) = fun n =>
      Fuel.andThen
        ((bs.get t.idx t.hidx).2.eval n (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb) s)
        fun p => bs.next n Vamb p.1.2 p.2 :=
    funext fun n => by rw [Blocks.iterate]
  rw [hit,
    Fuel.limit_andThen (f := fun n =>
      (bs.get t.idx t.hidx).2.eval n (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb) s) (g :=
      fun n p => bs.next n Vamb p.1.2 p.2) BlockCom.eval_mono (fun _ => Blocks.next_mono),
    EffectM.run_bind]
  have hhead :=
    (bs.get t.idx t.hidx).2.run_denote (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb) s
  cases hlim :
    Fuel.limit fun n =>
      (bs.get t.idx t.hidx).2.eval n (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb) s with
  | none =>
    rw [hlim, Fuel.force_none] at hhead
    rw [hhead]
    rfl
  | some r =>
    rw [hlim, Fuel.force_some] at hhead
    rw [hhead]
    cases r with
    | poison => rfl
    | value p =>
      obtain ⟨⟨Vb, rr⟩, s'⟩ := p
      simp only [Fuel.andThen_value, PoisonOr.value_bind]
      cases rr with
      | inl
        rets =>
        have h1 : (fun n => bs.next n Vamb (.inl rets) s') = fun _ => some (.value (rets, s')) :=
          funext fun n => by rw [Blocks.next]
        rw [h1, Fuel.limit_const]
        rfl
      | inr
        tn =>
        have h1 : (fun n => bs.next n Vamb (.inr tn) s') = fun n => bs.iterate n Vamb tn s' :=
          funext fun n => by rw [Blocks.next]
        rw [h1]
        rfl

/-! ## The `Cfg`-level agreement -/

theorem Cfg.run_denote (cfg : Cfg Γin rets) (V : Γin.Valuation) (s : GlobalState) :
    StateT.run (cfg.denote V) s = Fuel.force (Fuel.limit fun n => Cfg.eval n cfg V s) := by
  simp only [Cfg.denote, Cfg.eval, EffectM.run_bind]
  rw [Fuel.limit_andThen (f := fun n => cfg.entry.eval n V s) (g := fun n p =>
      cfg.blocks.next n p.1.1 p.1.2 p.2) BlockCom.eval_mono (fun _ => Blocks.next_mono)]
  have hentry := cfg.entry.run_denote V s
  cases hlim : Fuel.limit fun n => cfg.entry.eval n V s with
  | none =>
    rw [hlim, Fuel.force_none] at hentry
    rw [hentry]
    rfl
  | some r =>
    rw [hlim, Fuel.force_some] at hentry
    rw [hentry]
    cases r with
    | poison => rfl
    | value p =>
      obtain ⟨⟨Vout, rr⟩, s'⟩ := p
      simp only [Fuel.andThen_value, PoisonOr.value_bind]
      cases rr with
      | inl
        rs =>
        have h1 :
          (fun n => cfg.blocks.next n Vout (.inl rs) s') = fun _ => some (.value (rs, s')) :=
          funext fun n => by rw [Blocks.next]
        rw [h1, Fuel.limit_const]
        rfl
      | inr
        tn =>
        have h1 :
          (fun n => cfg.blocks.next n Vout (.inr tn) s') = fun n =>
            cfg.blocks.iterate n Vout tn s' :=
          funext fun n => by rw [Blocks.next]
        rw [h1]
        rfl

theorem Cfg.eval_mono {cfg : Cfg Γin rets} {V : Γin.Valuation} {s : GlobalState} :
    FuelMono (fun n => Cfg.eval n cfg V s) :=
  Fuel.mono_andThen BlockCom.eval_mono fun _ => Blocks.next_mono

/-- A completed fueled run *is* the denotation: what a differential `#guard`
checks transfers to `Cfg.denote`. -/
theorem Cfg.eval_sound {cfg : Cfg Γin rets} {V : Γin.Valuation} {s : GlobalState} {fuel : Nat}
    {r : PoisonOr (HVector toType rets × GlobalState)} (h : Cfg.eval fuel cfg V s = some r) :
    StateT.run (cfg.denote V) s = r := by
  rw [Cfg.run_denote, Fuel.limit_eq_of Cfg.eval_mono h, Fuel.force_some]

end LeanMLIR.SLLVM
