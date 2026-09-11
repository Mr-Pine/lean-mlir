/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory

/-!
# Partial-correctness walks

Frame statements -- "if this returns, it wrote only there" -- need neither
termination nor poison freedom, so they are proved by *partial* correctness:
a block that goes to UB, or a loop that never ends, produces no value and makes
the obligation vacuous.

* `Blocks.run_inv` is the loop rule: an invariant each block preserves
  *whenever it produces a value* holds of any value the walk produces.
* `load_run_cases`/`store_run_cases` say what a memory access does when it does
  not trap -- a load writes nothing, a store splices into the block its pointer
  names -- without knowing whether it traps.
* The `walk_*` combinators consume one impure instruction of a goal in the
  named-result shape `∃ res, run … = res ∧ P res`, splitting on the
  instruction's outcome in continuation form, so the rest of the block stays
  stepable by `denote_step_all`.

Staged beside the SHA-512 proofs that use them.
-/

namespace LeanMLIR.SLLVM
open InstCombine (LLVM)

/-- Partial correctness for a block walk: if every block entered in `Inv`
either returns with `Q` or branches in `Inv` *whenever it produces a value*,
then any value the walk produces satisfies `Q`. Nothing about termination or
poison: a step that is UB, or a walk that never ends, is simply not a value. -/
theorem Blocks.run_inv {Γamb : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty}
    {all : List (List SLLVM.Ty)} {bs : Blocks Γamb rets all all} {Vamb : Γamb.Valuation}
    (Inv : GlobalState → Prop) (Q : HVector toType rets → GlobalState → Prop)
    (hstep : ∀ (t : SuccArgs all) (s : GlobalState), Inv s →
      ∀ p (s' : GlobalState),
        StateT.run ((bs.get t.idx t.hidx).2.denote
            (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb)) s = .value (p, s') →
        (∀ res, p.2 = .inl res → Q res s') ∧ (∀ t', p.2 = .inr t' → Inv s'))
    {t₀ : SuccArgs all} {s₀ : GlobalState} (h₀ : Inv s₀) :
    ∀ rs s', StateT.run (bs.run Vamb t₀) s₀ = .value (rs, s') → Q rs s' := by
  intro rs s' h
  rw [Blocks.run_eq_limit] at h
  have hl : Fuel.limit (fun n => bs.iterate n Vamb t₀ s₀) = some (.value (rs, s')) := by
    cases hlim : Fuel.limit (fun n => bs.iterate n Vamb t₀ s₀) with
    | none => rw [hlim, Fuel.force_none] at h; exact absurd h.symm (PoisonOr.value_ne_poison _)
    | some r => rw [hlim, Fuel.force_some] at h; rw [h]
  obtain ⟨n, hn⟩ := Fuel.exists_of_limit_eq_some hl
  clear h hl
  induction n generalizing t₀ s₀ with
  | zero => rw [Blocks.iterate] at hn; exact absurd hn (by simp)
  | succ n ih =>
    rw [Blocks.iterate] at hn
    cases he : (bs.get t₀.idx t₀.hidx).2.eval n
        (Ctxt.Valuation.ofHVector t₀.args.reverse ++ Vamb) s₀ with
    | none => rw [he] at hn; exact absurd hn (by simp)
    | some r =>
      cases r with
      | poison =>
          rw [he, Fuel.andThen_poison, Option.some.injEq] at hn
          exact absurd hn.symm (PoisonOr.value_ne_poison _)
      | value q =>
        rw [he, Fuel.andThen_value] at hn
        have hd := BlockCom.run_denote (bs.get t₀.idx t₀.hidx).2
          (Ctxt.Valuation.ofHVector t₀.args.reverse ++ Vamb) s₀
        rw [Fuel.limit_eq_of BlockCom.eval_mono he, Fuel.force_some] at hd
        obtain ⟨hinl, hinr⟩ := hstep t₀ s₀ h₀ q.1 q.2 hd
        obtain ⟨⟨Vout, r⟩, s₁⟩ := q
        cases r with
        | inl res =>
            rw [Blocks.next] at hn
            simp only [Option.some.injEq, PoisonOr.value_inj, Prod.mk.injEq] at hn
            obtain ⟨rfl, rfl⟩ := hn
            exact hinl res rfl
        | inr t' =>
            rw [Blocks.next] at hn
            exact ih (hinr t' rfl) hn

/-- A load either traps or reads, and never writes. -/
theorem load_run_cases (p : SLLVM.Ptr) (t : LLVM.Ty) (m : MemoryState) :
    (load p t).run m = .poison ∨ ∃ x, (load p t).run m = .value (x, m) := by
  rcases p with ⟨_ | q⟩
  · left; simp [load, PoisonOr.getOrUB]
  · rcases hb : m[q.id]? with _ | ⟨_ | blk⟩
    · left; simp [load, getLiveBlockOrUB, hb, PoisonOr.getOrUB]
    · left; simp [load, getLiveBlockOrUB, hb, PoisonOr.getOrUB]
    · by_cases hlen : q.offsetInBits + LLVM.Ty.width t > blk.lengthInBits
      · left; simp [load, getLiveBlockOrUB, hb, throwUBIf, hlen, PoisonOr.getOrUB]
      · right; exact ⟨_, run_load hb (Nat.le_of_not_gt hlen)⟩

/-- A store either traps or splices the bits it was handed into the block its
pointer addresses -- that block and no other. -/
theorem store_run_cases (p : SLLVM.Ptr) (t : LLVM.Ty) (x : TyDenote.toType t) (m : MemoryState) :
    (store p t x).run m = .poison
      ∨ ∃ (q : Pointer) (b : BitVec (LLVM.Ty.width t)),
          p = .value q ∧ (store p t x).run m = .value ((), m.splice q b) := by
  rcases p with ⟨_ | q⟩
  · left; simp [store, PoisonOr.getOrUB]
  · rcases hx : LLVM.Ty.flatten t x with ⟨_ | b⟩
    · left; simp [store, PoisonOr.getOrUB, hx]
    · rcases hb : m[q.id]? with _ | ⟨_ | blk⟩
      · left; simp [store, getLiveBlockOrUB, hb, hx, PoisonOr.getOrUB]
      · left; simp [store, getLiveBlockOrUB, hb, hx, PoisonOr.getOrUB]
      · by_cases hlen : q.offsetInBits + LLVM.Ty.width t > blk.lengthInBits
        · left; simp [store, getLiveBlockOrUB, hb, hx, throwUBIf, hlen, PoisonOr.getOrUB]
        · right
          exact ⟨q, b, rfl, run_store hx ⟨blk, hb, Nat.le_of_not_gt hlen⟩⟩


/-! ## Poison propagation -/

/-- An impure instruction that is UB poisons the rest of the block. -/
theorem BlockCom.run_bind_denote_var_of_poison' {Γ Γout : Ctxt SLLVM.Ty} {tys rets succs β}
    {e : Expr SLLVM Γ .impure tys} {body : BlockCom (tys ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s : GlobalState}
    (h : StateT.run (e.denoteOp V) s = .poison) :
    StateT.run ((BlockCom.var e body).denote V >>= k) s = .poison := by
  rw [BlockCom.denote_var, bind_assoc, Expr.denote_unfold, EffectM.run_bind, EffectM.run_map, h]
  rfl

/-- `BlockCom.call` as `runFunction` of the callee, then the body. -/
theorem BlockCom.denote_call_eq {Γ Γout : Ctxt SLLVM.Ty} {rets succs}
    {argTys retTys : List SLLVM.Ty} {csigs : List (List SLLVM.Ty)} {cΓout : Ctxt SLLVM.Ty}
    {callee : String} {centry : BlockCom (Ctxt.ofList argTys.reverse) cΓout retTys csigs}
    {cblocks : Blocks cΓout retTys csigs csigs} {args : HVector Γ.Var argTys}
    {body : BlockCom (retTys ++ Γ) Γout rets succs} {V : Γ.Valuation} :
    BlockCom.denote (.call callee centry cblocks args body) V
      = (runFunction (Cfg.denote ⟨centry, cblocks⟩
            (Ctxt.Valuation.ofHVector (args.map V).reverse))
          >>= fun rs => body.denote (rs ++ V)) := by
  rw [BlockCom.denote_call]
  refine congrArg (fun m => runFunction m >>= fun rs => body.denote (rs ++ V)) ?_
  simp only [Cfg.denote]
  refine congrArg (Bind.bind (centry.denote _)) ?_
  funext y
  obtain ⟨Vc, r⟩ := y
  cases r <;> rfl

/-! ## Walk combinators

Each takes the goal `∃ res, StateT.run (c.denote V >>= k) s = res ∧ P res` for a
block `c` starting with the instruction in question, a proof that `P` holds of
poison, and the instruction's outcome as a disjunction; the continuation
receives the instruction's result and a fact about the state it left. -/

theorem walk_var_nil {Γ Γout : Ctxt SLLVM.Ty} {rets succs β} {e : Expr SLLVM Γ .impure []}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs} {V : Γ.Valuation}
    {k : _ → EffectM β} {s : GlobalState} {P : PoisonOr (β × GlobalState) → Prop}
    {R : GlobalState → Prop} (hp : P .poison)
    (hcase : StateT.run (e.denoteOp V) s = .poison
      ∨ ∃ s₁, StateT.run (e.denoteOp V) s = .value (.nil, s₁) ∧ R s₁)
    (hk : ∀ s₁, R s₁ → ∃ res, StateT.run (body.denote V >>= k) s₁ = res ∧ P res) :
    ∃ res, StateT.run ((BlockCom.var e body).denote V >>= k) s = res ∧ P res := by
  rcases hcase with h | ⟨s₁, h, hR⟩
  · exact ⟨.poison, BlockCom.run_bind_denote_var_of_poison' h, hp⟩
  · obtain ⟨res, hres, hP⟩ := hk s₁ hR
    exact ⟨res, (BlockCom.run_bind_denote_var_of_nil h).trans hres, hP⟩

theorem walk_var_single {Γ Γout : Ctxt SLLVM.Ty} {t rets succs β}
    {e : Expr SLLVM Γ .impure [t]} {body : BlockCom (([t] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s : GlobalState}
    {P : PoisonOr (β × GlobalState) → Prop} {R : ⟦t⟧ → GlobalState → Prop} (hp : P .poison)
    (hcase : StateT.run (e.denoteOp V) s = .poison
      ∨ ∃ x s₁, StateT.run (e.denoteOp V) s = .value ([x]ₕ, s₁) ∧ R x s₁)
    (hk : ∀ x s₁, R x s₁ → ∃ res, StateT.run (body.denote (x ::ᵥ V) >>= k) s₁ = res ∧ P res) :
    ∃ res, StateT.run ((BlockCom.var e body).denote V >>= k) s = res ∧ P res := by
  rcases hcase with h | ⟨x, s₁, h, hR⟩
  · exact ⟨.poison, BlockCom.run_bind_denote_var_of_poison' h, hp⟩
  · obtain ⟨res, hres, hP⟩ := hk x s₁ hR
    exact ⟨res, (BlockCom.run_bind_denote_var_of_value h).trans hres, hP⟩

theorem walk_call_single {Γ Γout : Ctxt SLLVM.Ty} {t rets succs β}
    {argTys : List SLLVM.Ty} {csigs : List (List SLLVM.Ty)} {cΓout : Ctxt SLLVM.Ty}
    {callee : String} {centry : BlockCom (Ctxt.ofList argTys.reverse) cΓout [t] csigs}
    {cblocks : Blocks cΓout [t] csigs csigs} {args : HVector Γ.Var argTys}
    {body : BlockCom (([t] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s : GlobalState}
    {P : PoisonOr (β × GlobalState) → Prop} {R : ⟦t⟧ → GlobalState → Prop} (hp : P .poison)
    (hcase : StateT.run (runFunction (Cfg.denote ⟨centry, cblocks⟩
          (Ctxt.Valuation.ofHVector (args.map V).reverse))) s = .poison
      ∨ ∃ x s₁, StateT.run (runFunction (Cfg.denote ⟨centry, cblocks⟩
          (Ctxt.Valuation.ofHVector (args.map V).reverse))) s = .value ([x]ₕ, s₁) ∧ R x s₁)
    (hk : ∀ x s₁, R x s₁ → ∃ res, StateT.run (body.denote (x ::ᵥ V) >>= k) s₁ = res ∧ P res) :
    ∃ res, StateT.run ((BlockCom.call callee centry cblocks args body).denote V >>= k) s = res
      ∧ P res := by
  rcases hcase with h | ⟨x, s₁, h, hR⟩
  · refine ⟨.poison, ?_, hp⟩
    rw [BlockCom.denote_call_eq, bind_assoc, EffectM.run_bind, h]; rfl
  · obtain ⟨res, hres, hP⟩ := hk x s₁ hR
    exact ⟨res, (BlockCom.run_bind_denote_call_of_value h).trans hres, hP⟩

/-- A terminator never touches the state: it traps on a poison scrutinee or
names where to go. -/
theorem run_term_cases {Γ : Ctxt SLLVM.Ty} {rets succs} (t : Terminator Γ rets succs)
    (V : Γ.Valuation) (s : GlobalState) :
    StateT.run ((BlockCom.term t).denote V) s = .poison
      ∨ ∃ r, StateT.run ((BlockCom.term t).denote V) s = .value ((V, r), s) := by
  cases t with
  | ret vs => exact .inr ⟨_, rfl⟩
  | br tg => exact .inr ⟨_, rfl⟩
  | condBr c tT tF =>
      rcases hc : V c with ⟨_ | b⟩
      · left
        rw [BlockCom.denote_term, Terminator.denote_condBr_poison hc]; rfl
      · right; exact ⟨_, by rw [BlockCom.denote_term, Terminator.denote_condBr_value hc]; rfl⟩
  | switch v dflt cases =>
      rcases hc : V v with ⟨_ | x⟩
      · left
        rw [BlockCom.denote_term, Terminator.denote_switch_poison hc]; rfl
      · right; exact ⟨_, by rw [BlockCom.denote_term, Terminator.denote_switch_value hc]; rfl⟩

/-! ## Instruction outcomes -/

theorem run_liftM_cases {α : Type} {x : MemorySSAM α} {s : GlobalState} {R : α → MemoryState → Prop}
    (h : x.run s.mem = .poison ∨ ∃ y m, x.run s.mem = .value (y, m) ∧ R y m) :
    (liftM x : EffectM α).run s = .poison
      ∨ ∃ y m, (liftM x : EffectM α).run s = .value (y, { s with mem := m }) ∧ R y m := by
  rcases h with h | ⟨y, m, h, hR⟩
  · left; cases s; simp only [liftM, monadLift, MonadLift.monadLift, StateT.run] at *; rw [h]
  · exact .inr ⟨y, m, run_liftM h, hR⟩

@[simp_denote] theorem denoteOp_store {Γ : Ctxt SLLVM.Ty} (t : LLVM.Ty)
    (p : Ctxt.Var Γ .ptr) (v : Ctxt.Var Γ (.arith t)) (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
      (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
        (SLLVMOp.store t) rfl (EffectKind.le_refl _) (p ::ₕ v ::ₕ .nil) Regions.nil) V
      = ((fun _ => HVector.nil) <$> (liftM (SLLVM.store (V p) t (V v))) :
          EffectM (HVector TyDenote.toType [])) := by
  simp [Expr.denoteOp, EffectKind.liftEffect,
    DialectSignature.effectKind, DialectSignature.signature, DialectDenote.denote]
  rfl

/-- A `load` instruction: UB, or a value and the state it was handed. -/
theorem load_expr_cases {Γ : Ctxt SLLVM.Ty} (t : LLVM.Ty) (p : Ctxt.Var Γ .ptr)
    (V : Ctxt.Valuation Γ) (s : GlobalState) :
    StateT.run (Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
          (SLLVMOp.load t) rfl (EffectKind.le_refl _) (p ::ₕ .nil) Regions.nil) V) s = .poison
      ∨ ∃ x s₁, StateT.run (Expr.denoteOp
          (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
            (SLLVMOp.load t) rfl (EffectKind.le_refl _) (p ::ₕ .nil) Regions.nil) V) s
          = .value ([x]ₕ, s₁) ∧ s₁ = s := by
  rw [denoteOp_load, EffectM.run_map]
  rcases run_liftM_cases (R := fun _ m => m = s.mem) (x := SLLVM.load (V p) t) (s := s)
    ((load_run_cases (V p) t s.mem).imp id fun ⟨x, h⟩ => ⟨x, _, h, rfl⟩)
    with h | ⟨y, m, h, rfl⟩
  · left; rw [h]; rfl
  · right; exact ⟨y, _, by rw [h]; rfl, rfl⟩

/-- A `store` instruction: UB, or the state with the stored bits spliced into
the block the pointer operand names. -/
theorem store_expr_cases {Γ : Ctxt SLLVM.Ty} (t : LLVM.Ty) (p : Ctxt.Var Γ .ptr)
    (v : Ctxt.Var Γ (.arith t)) (V : Ctxt.Valuation Γ) (s : GlobalState) :
    StateT.run (Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
          (SLLVMOp.store t) rfl (EffectKind.le_refl _) (p ::ₕ v ::ₕ .nil) Regions.nil) V) s
        = .poison
      ∨ ∃ s₁, StateT.run (Expr.denoteOp
          (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
            (SLLVMOp.store t) rfl (EffectKind.le_refl _) (p ::ₕ v ::ₕ .nil) Regions.nil) V) s
          = .value (.nil, s₁)
        ∧ ∃ (q : Pointer) (b : BitVec (LLVM.Ty.width t)), V p = .value q
          ∧ s₁ = { s with mem := s.mem.splice q b } := by
  rw [denoteOp_store, EffectM.run_map]
  rcases run_liftM_cases
      (R := fun _ m => ∃ (q : Pointer) (b : BitVec (LLVM.Ty.width t)), V p = .value q ∧ m = s.mem.splice q b)
      (x := SLLVM.store (V p) t (V v)) (s := s)
      ((store_run_cases (V p) t (V v) s.mem).imp id fun ⟨q, b, hq, h⟩ => ⟨(), _, h, q, b, hq, rfl⟩)
    with h | ⟨y, m, h, q, b, hq, rfl⟩
  · left; rw [h]; rfl
  · right; exact ⟨_, by rw [h]; rfl, q, b, hq, rfl⟩

/-- A lifetime marker: no effect at all. -/
theorem lifetime_expr_cases {Γ : Ctxt SLLVM.Ty} (start : Bool) (p : Ctxt.Var Γ .ptr)
    (V : Ctxt.Valuation Γ) (s : GlobalState) :
    StateT.run (Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
          (SLLVMOp.lifetime start) rfl (EffectKind.le_refl _) (p ::ₕ .nil) Regions.nil) V) s
        = .poison
      ∨ ∃ s₁, StateT.run (Expr.denoteOp
          (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
            (SLLVMOp.lifetime start) rfl (EffectKind.le_refl _) (p ::ₕ .nil) Regions.nil) V) s
          = .value (.nil, s₁) ∧ s₁ = s :=
  .inr ⟨s, by rw [denoteOp_lifetime]; rfl, rfl⟩

/-- `addressof`: UB for an unknown symbol, otherwise a value and the same state. -/
theorem addressof_expr_cases {Γ : Ctxt SLLVM.Ty} (name : String) (V : Ctxt.Valuation Γ)
    (s : GlobalState) :
    StateT.run (Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
          (SLLVMOp.addressof name) rfl (EffectKind.le_refl _) HVector.nil Regions.nil) V) s
        = .poison
      ∨ ∃ x s₁, StateT.run (Expr.denoteOp
          (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
            (SLLVMOp.addressof name) rfl (EffectKind.le_refl _) HVector.nil Regions.nil) V) s
          = .value ([x]ₕ, s₁) ∧ s₁ = s := by
  rw [denoteOp_addressof, EffectM.run_map]
  cases h : s.globals[name]? with
  | none => left; simp [SLLVM.addressof, h]
  | some p => right; exact ⟨_, s, by rw [run_addressof h]; rfl, rfl⟩

/-- `alloca`: always a fresh zeroed block at the counter. -/
theorem alloca_expr_cases {Γ : Ctxt SLLVM.Ty} (w : Nat) (V : Ctxt.Valuation Γ) (s : GlobalState) :
    StateT.run (Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
          (SLLVMOp.alloca w) rfl (EffectKind.le_refl _) HVector.nil Regions.nil) V) s
        = .poison
      ∨ ∃ x s₁, StateT.run (Expr.denoteOp
          (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
            (SLLVMOp.alloca w) rfl (EffectKind.le_refl _) HVector.nil Regions.nil) V) s
          = .value ([x]ₕ, s₁)
        ∧ x = .value ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ ∧ s₁ = s.afterAlloca w :=
  .inr ⟨_, _, by rw [denoteOp_alloca, EffectM.run_map, run_alloca]; rfl, rfl, rfl⟩

/-- A `gep` that produced a pointer was applied to one, in the same block. -/
theorem gep_eq_value {p : SLLVM.Ptr} {sz off : Nat} {i : LLVM.IntW 64} {q : Pointer}
    (h : SLLVM.gep p sz off i = .value q) : ∃ p' : Pointer, p = .value p' ∧ q.id = p'.id := by
  rcases p with ⟨_ | p'⟩
  · exact absurd h (by simp [SLLVM.gep, SLLVM.ptradd]; exact fun e => PoisonOr.value_ne_poison _ e.symm)
  · refine ⟨p', rfl, ?_⟩
    rcases i with ⟨_ | i⟩
    · exact absurd h (by simp [SLLVM.gep, SLLVM.ptradd, LLVM.add, LLVM.mul]; exact fun e => PoisonOr.value_ne_poison _ e.symm)
    · simp [SLLVM.gep, SLLVM.ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?] at h
      rw [← h]

/-- A two-index `gep` that produced a pointer was applied to one, in the same block. -/
theorem gep2_eq_value {p : SLLVM.Ptr} {s₀ o₀ s₁ o₁ : Nat} {i j : LLVM.IntW 64} {q : Pointer}
    (h : SLLVM.gep2 p s₀ o₀ s₁ o₁ i j = .value q) : ∃ p' : Pointer, p = .value p' ∧ q.id = p'.id := by
  obtain ⟨m, hm, hq⟩ := gep_eq_value (show SLLVM.gep (SLLVM.gep p s₀ o₀ i) s₁ o₁ j = _ from h)
  obtain ⟨p', hp', hm'⟩ := gep_eq_value hm
  exact ⟨p', hp', hq.trans hm'⟩

/-- A pointer register defined by a `gep` of a base in block `X` is in `X`. -/
theorem id_of_gep_eq {v base : SLLVM.Ptr} {sz off : Nat} {i : LLVM.IntW 64} {q : Pointer}
    {X : BlockId} (hv : v = SLLVM.gep base sz off i) (hq : v = .value q)
    (hb : ∀ p', base = .value p' → p'.id = X) : q.id = X := by
  obtain ⟨p', hp', hid⟩ := gep_eq_value (hv ▸ hq)
  exact hid.trans (hb p' hp')

/-- ... and likewise for a two-index `gep`. -/
theorem id_of_gep2_eq {v base : SLLVM.Ptr} {s₀ o₀ s₁ o₁ : Nat} {i j : LLVM.IntW 64} {q : Pointer}
    {X : BlockId} (hv : v = SLLVM.gep2 base s₀ o₀ s₁ o₁ i j) (hq : v = .value q)
    (hb : ∀ p', base = .value p' → p'.id = X) : q.id = X := by
  obtain ⟨p', hp', hid⟩ := gep2_eq_value (hv ▸ hq)
  exact hid.trans (hb p' hp')

/-- A `gep` of a pointer by a value is a pointer in the same block. -/
theorem gep_value_value (p : Pointer) (sz off : Nat) (i : BitVec 64) :
    ∃ q : Pointer, SLLVM.gep (.value p) sz off (.value i) = .value q ∧ q.id = p.id :=
  ⟨p.withOffset (i * BitVec.ofNat 64 sz + BitVec.ofNat 64 off),
    by simp [SLLVM.gep, SLLVM.ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
      Pointer.withOffset], rfl⟩

/-- A lookup past the prefix of an appended valuation reads the suffix. Tail
blocks read ambient values through `ofHVector args.reverse ++ Vamb`, with
`args` opaque; its length is known, and this skips it. -/
theorem valuation_append_right {Γ Δ : Ctxt SLLVM.Ty} (V : Γ.Valuation) (W : Δ.Valuation)
    {t : SLLVM.Ty} (n m : Nat) (h : (Γ ++ Δ)[n]? = some t) (hnm : n = Γ.length + m) :
    (V ++ W) ⟨n, h⟩ = W ⟨m, by subst hnm; simpa [Ctxt.getElem?_append] using h⟩ := by
  have : (⟨n, h⟩ : (Γ ++ Δ).Var t) =
      Ctxt.Var.appendInr (Γ := Γ) (⟨m, by subst hnm; simpa [Ctxt.getElem?_append] using h⟩ :
        Δ.Var t) := by
    apply Subtype.ext; simp [Ctxt.Var.appendInr]; omega
  rw [this, Ctxt.Valuation.append_appendInr]

/-- `valuation_append_right` with the target index left as the subtraction,
for `rw` at a lookup whose index is not known in advance. -/
theorem valuation_append_right' {Γ Δ : Ctxt SLLVM.Ty} (V : Γ.Valuation) (W : Δ.Valuation)
    {t : SLLVM.Ty} (n : Nat) (h : (Γ ++ Δ)[n]? = some t) (hn : Γ.length ≤ n) :
    (V ++ W) ⟨n, h⟩ = W ⟨n - Γ.length, by
      have e : n = Γ.length + (n - Γ.length) := by omega
      rw [e] at h; simpa [Ctxt.getElem?_append] using h⟩ :=
  valuation_append_right V W n (n - Γ.length) h (by omega)

/-! ## Entering and leaving a block -/

/-- A bare block denotation, as the loop rule states it, in the `>>= pure` form
the combinators consume. -/
theorem walk_bare {α : Type} {m : EffectM α} {s : GlobalState} {P : PoisonOr (α × GlobalState) → Prop}
    (h : ∃ res, StateT.run (m >>= pure) s = res ∧ P res) :
    ∃ res, StateT.run m s = res ∧ P res := by
  simpa only [bind_pure] using h

/-- The poison outcome satisfies any "if it returns" obligation. -/
theorem vacuous_poison {α : Type} {Post : α → GlobalState → Prop} :
    (fun res : PoisonOr (α × GlobalState) => ∀ p s', res = .value (p, s') → Post p s') .poison :=
  fun _ _ h => absurd h.symm (PoisonOr.value_ne_poison _)

/-- The end of a block: whatever the terminator picks, the state is the one it
was handed. -/
theorem walk_term {Γ : Ctxt SLLVM.Ty} {rets succs} {t : Terminator Γ rets succs}
    {V : Γ.Valuation} {s : GlobalState}
    {Post : (Γ.Valuation × (HVector toType rets ⊕ SuccArgs succs)) → GlobalState → Prop}
    (h : ∀ r, Post (V, r) s) :
    ∃ res, StateT.run ((BlockCom.term t).denote V >>= pure) s = res
      ∧ ∀ p s', res = .value (p, s') → Post p s' := by
  rw [bind_pure]
  refine ⟨_, rfl, fun p s' hps => ?_⟩
  rcases run_term_cases t V s with h' | ⟨r, h'⟩
  · rw [h'] at hps; exact absurd hps.symm (PoisonOr.value_ne_poison _)
  · rw [h', PoisonOr.value_inj, Prod.mk.injEq] at hps
    obtain ⟨rfl, rfl⟩ := hps
    exact h r

/-! ## More instruction outcomes -/

/-- A `memset` traps or splices into the block its pointer names. -/
theorem memset_run_cases (p : SLLVM.Ptr) (b : LLVM.IntW 8) (len : LLVM.IntW 64) (m : MemoryState) :
    (memset p b len).run m = .poison
      ∨ ∃ (q : Pointer) (n : Nat) (x : BitVec n), p = .value q ∧ (memset p b len).run m = .value ((), m.splice q x) := by
  rcases p with ⟨_ | q⟩
  · left; simp [memset, PoisonOr.getOrUB]
  · rcases b with ⟨_ | b⟩
    · left; simp [memset, PoisonOr.getOrUB]
    · rcases len with ⟨_ | len⟩
      · left; simp [memset, PoisonOr.getOrUB]
      · rcases hb : m[q.id]? with _ | ⟨_ | blk⟩
        · left; simp [memset, getLiveBlockOrUB, hb, PoisonOr.getOrUB]
        · left; simp [memset, getLiveBlockOrUB, hb, PoisonOr.getOrUB]
        · by_cases hlen : q.offsetInBits + 8 * len.toNat > blk.lengthInBits
          · left; simp [memset, getLiveBlockOrUB, hb, throwUBIf, hlen, PoisonOr.getOrUB]
          · right
            exact ⟨q, _, _, rfl, run_memset ⟨blk, hb, Nat.le_of_not_gt hlen⟩⟩

/-- A `memcpy` traps or splices into the block its destination names. -/
theorem memcpy_run_cases (dst src : SLLVM.Ptr) (len : LLVM.IntW 64) (m : MemoryState) :
    (memcpy dst src len).run m = .poison
      ∨ ∃ (q : Pointer) (n : Nat) (x : BitVec n), dst = .value q
          ∧ (memcpy dst src len).run m = .value ((), m.splice q x) := by
  rcases dst with ⟨_ | q⟩
  · left; simp [memcpy, PoisonOr.getOrUB]
  · rcases src with ⟨_ | r⟩
    · left; simp [memcpy, PoisonOr.getOrUB]
    · rcases len with ⟨_ | len⟩
      · left; simp [memcpy, PoisonOr.getOrUB]
      · rcases hr : m[r.id]? with _ | ⟨_ | sblk⟩
        · left; simp [memcpy, getLiveBlockOrUB, hr, PoisonOr.getOrUB]
        · left; simp [memcpy, getLiveBlockOrUB, hr, PoisonOr.getOrUB]
        · by_cases hslen : r.offsetInBits + 8 * len.toNat > sblk.lengthInBits
          · left; simp [memcpy, getLiveBlockOrUB, hr, throwUBIf, hslen, PoisonOr.getOrUB]
          · rcases hq : m[q.id]? with _ | ⟨_ | dblk⟩
            · left; simp [memcpy, getLiveBlockOrUB, hr, hq, throwUBIf, hslen, PoisonOr.getOrUB]
            · left; simp [memcpy, getLiveBlockOrUB, hr, hq, throwUBIf, hslen, PoisonOr.getOrUB]
            · by_cases hdlen : q.offsetInBits + 8 * len.toNat > dblk.lengthInBits
              · left; simp [memcpy, getLiveBlockOrUB, hr, hq, throwUBIf, hslen, hdlen, PoisonOr.getOrUB]
              · right
                exact ⟨q, _, _, rfl,
                  run_memcpy hr (Nat.le_of_not_gt hslen) ⟨dblk, hq, Nat.le_of_not_gt hdlen⟩⟩

@[simp_denote] theorem denoteOp_memset {Γ : Ctxt SLLVM.Ty} (p : Ctxt.Var Γ .ptr)
    (b : Ctxt.Var Γ (SLLVM.Ty.bitvec 8)) (len : Ctxt.Var Γ (SLLVM.Ty.bitvec 64)) (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
      (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
        SLLVMOp.memset rfl (EffectKind.le_refl _) (p ::ₕ b ::ₕ len ::ₕ .nil) Regions.nil) V
      = ((fun _ => HVector.nil) <$> (liftM (SLLVM.memset (V p) (V b) (V len))) :
          EffectM (HVector TyDenote.toType [])) := by
  simp [Expr.denoteOp, EffectKind.liftEffect,
    DialectSignature.effectKind, DialectSignature.signature, DialectDenote.denote]
  rfl

@[simp_denote] theorem denoteOp_memcpy {Γ : Ctxt SLLVM.Ty} (d r : Ctxt.Var Γ .ptr)
    (len : Ctxt.Var Γ (SLLVM.Ty.bitvec 64)) (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
      (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
        SLLVMOp.memcpy rfl (EffectKind.le_refl _) (d ::ₕ r ::ₕ len ::ₕ .nil) Regions.nil) V
      = ((fun _ => HVector.nil) <$> (liftM (SLLVM.memcpy (V d) (V r) (V len))) :
          EffectM (HVector TyDenote.toType [])) := by
  simp [Expr.denoteOp, EffectKind.liftEffect,
    DialectSignature.effectKind, DialectSignature.signature, DialectDenote.denote]
  rfl

/-- A `memset` instruction: UB, or a splice into the block its pointer names. -/
theorem memset_expr_cases {Γ : Ctxt SLLVM.Ty} (p : Ctxt.Var Γ .ptr) (b : Ctxt.Var Γ (SLLVM.Ty.bitvec 8))
    (len : Ctxt.Var Γ (SLLVM.Ty.bitvec 64)) (V : Ctxt.Valuation Γ) (s : GlobalState) :
    StateT.run (Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
          SLLVMOp.memset rfl (EffectKind.le_refl _) (p ::ₕ b ::ₕ len ::ₕ .nil) Regions.nil) V) s
        = .poison
      ∨ ∃ s₁, StateT.run (Expr.denoteOp
          (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
            SLLVMOp.memset rfl (EffectKind.le_refl _) (p ::ₕ b ::ₕ len ::ₕ .nil) Regions.nil) V) s
          = .value (.nil, s₁)
        ∧ ∃ (q : Pointer) (n : Nat) (x : BitVec n), V p = .value q
          ∧ s₁ = { s with mem := s.mem.splice q x } := by
  rw [denoteOp_memset, EffectM.run_map]
  rcases run_liftM_cases
      (R := fun _ m => ∃ (q : Pointer) (n : Nat) (x : BitVec n), V p = .value q ∧ m = s.mem.splice q x)
      (x := SLLVM.memset (V p) (V b) (V len)) (s := s)
      ((memset_run_cases (V p) (V b) (V len) s.mem).imp id
        fun ⟨q, n, x, hq, h⟩ => ⟨(), _, h, q, n, x, hq, rfl⟩)
    with h | ⟨y, m, h, q, n, x, hq, rfl⟩
  · left; rw [h]; rfl
  · right; exact ⟨_, by rw [h]; rfl, q, n, x, hq, rfl⟩

/-- A `memcpy` instruction: UB, or a splice into the block its destination names. -/
theorem memcpy_expr_cases {Γ : Ctxt SLLVM.Ty} (d r : Ctxt.Var Γ .ptr)
    (len : Ctxt.Var Γ (SLLVM.Ty.bitvec 64)) (V : Ctxt.Valuation Γ) (s : GlobalState) :
    StateT.run (Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
          SLLVMOp.memcpy rfl (EffectKind.le_refl _) (d ::ₕ r ::ₕ len ::ₕ .nil) Regions.nil) V) s
        = .poison
      ∨ ∃ s₁, StateT.run (Expr.denoteOp
          (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
            SLLVMOp.memcpy rfl (EffectKind.le_refl _) (d ::ₕ r ::ₕ len ::ₕ .nil) Regions.nil) V) s
          = .value (.nil, s₁)
        ∧ ∃ (q : Pointer) (n : Nat) (x : BitVec n), V d = .value q
          ∧ s₁ = { s with mem := s.mem.splice q x } := by
  rw [denoteOp_memcpy, EffectM.run_map]
  rcases run_liftM_cases
      (R := fun _ m => ∃ (q : Pointer) (n : Nat) (x : BitVec n), V d = .value q ∧ m = s.mem.splice q x)
      (x := SLLVM.memcpy (V d) (V r) (V len)) (s := s)
      ((memcpy_run_cases (V d) (V r) (V len) s.mem).imp id
        fun ⟨q, n, x, hq, h⟩ => ⟨(), _, h, q, n, x, hq, rfl⟩)
    with h | ⟨y, m, h, q, n, x, hq, rfl⟩
  · left; rw [h]; rfl
  · right; exact ⟨_, by rw [h]; rfl, q, n, x, hq, rfl⟩

/-! ## Frame invariants -/

/-- Well formed, and every block below `s₀`'s counter that `W` does not allow
reads as it did in `s₀`. -/
def FrameInv (s₀ : GlobalState) (W : BlockId → Prop) (s : GlobalState) : Prop :=
  s.WF ∧ ∀ b : BlockId, b.id < s₀.alloc.nextFreeBlock → ¬ W b → s.mem.live? b = s₀.mem.live? b

theorem FrameInv.of_equiv {s₀ s s₁ : GlobalState} {W : BlockId → Prop} (h : FrameInv s₀ W s)
    (he : s ≈ s₁) : FrameInv s₀ W s₁ :=
  ⟨h.1.of_equiv he, fun b hb hbw => (he.live b).symm.trans (h.2 b hb hbw)⟩

/-- A store keeps the invariant if it writes an allowed block, or one at or
above the entry counter. -/
theorem FrameInv.splice {s₀ s : GlobalState} {W : BlockId → Prop} (h : FrameInv s₀ W s)
    {q : Pointer} {n : Nat} {b : BitVec n} (hq : W q.id ∨ s₀.alloc.nextFreeBlock ≤ q.id.id) :
    FrameInv s₀ W { s with mem := s.mem.splice q b } := by
  refine ⟨h.1.splice, fun c hc hcw => ?_⟩
  have hne : q.id ≠ c := by
    rintro rfl
    rcases hq with hq | hq
    · exact hcw hq
    · omega
  rw [live?_splice_ne hne]
  exact h.2 c hc hcw

/-- A callee that keeps the counter, keeps well-formedness, and changes only
allowed blocks keeps the invariant. -/
theorem FrameInv.of_call {s₀ s s₁ : GlobalState} {W : BlockId → Prop} (h : FrameInv s₀ W s)
    (hwf : s₁.WF) (hlive : ∀ b : BlockId, ¬ W b → s₁.mem.live? b = s.mem.live? b) :
    FrameInv s₀ W s₁ :=
  ⟨hwf, fun b hb hbw => (hlive b hbw).trans (h.2 b hb hbw)⟩

theorem FrameInv.refl {s : GlobalState} (hs : s.WF) (W : BlockId → Prop) : FrameInv s W s :=
  ⟨hs, fun _ _ _ => rfl⟩

/-- What a frame pop leaves, given the invariant held of the body's state. -/
theorem popFrame_frameInv {s t : GlobalState} {W : BlockId → Prop} (hs : s.WF)
    (hI : FrameInv s W t) :
    (s.popFrame t.mem).WF ∧ (s.popFrame t.mem).alloc = s.alloc ∧ (s.popFrame t.mem).globals = s.globals
      ∧ ∀ b : BlockId, ¬ W b → (s.popFrame t.mem).mem.live? b = s.mem.live? b := by
  refine ⟨fun b hb => live?_killFrom_of_le hb, rfl, rfl, fun b hb => ?_⟩
  show (t.mem.killFrom s.alloc.nextFreeBlock).live? b = _
  by_cases hlt : b.id < s.alloc.nextFreeBlock
  · rw [live?_killFrom_of_lt hlt]; exact hI.2 b hlt hb
  · rw [live?_killFrom_of_le (by omega)]; exact (hs b (by omega)).symm

/-- Crossing the call boundary: the frame dies, so the invariant below the
entry counter is the whole of what the caller sees. -/
theorem runFunction_frameInv {α : Type} {body : EffectM α} {s : GlobalState} (hs : s.WF)
    {W : BlockId → Prop}
    (h : ∃ res, StateT.run body s = res ∧ ∀ p t, res = .value (p, t) → FrameInv s W t) :
    ∃ res, StateT.run (runFunction body) s = res ∧ ∀ r s', res = .value (r, s') →
      s'.WF ∧ s'.alloc = s.alloc ∧ s'.globals = s.globals
        ∧ ∀ b : BlockId, ¬ W b → s'.mem.live? b = s.mem.live? b := by
  obtain ⟨res, hres, hQ⟩ := h
  cases res with
  | poison =>
      exact ⟨.poison, run_runFunction_poison hres,
        fun _ _ h => absurd h.symm (PoisonOr.value_ne_poison _)⟩
  | value q =>
      obtain ⟨r, t⟩ := q
      refine ⟨.value (r, s.popFrame t.mem), run_runFunction hres, fun r' s' h' => ?_⟩
      rw [PoisonOr.value_inj, Prod.mk.injEq] at h'
      obtain ⟨-, rfl⟩ := h'
      have hI := hQ r t rfl
      refine ⟨fun b hb => live?_killFrom_of_le hb, rfl, rfl, fun b hb => ?_⟩
      show (t.mem.killFrom s.alloc.nextFreeBlock).live? b = _
      by_cases hlt : b.id < s.alloc.nextFreeBlock
      · rw [live?_killFrom_of_lt hlt]; exact hI.2 b hlt hb
      · rw [live?_killFrom_of_le (by omega)]; exact (hs b (by omega)).symm

/-! ## Calls without a result, and branches -/

theorem walk_call_nil {Γ Γout : Ctxt SLLVM.Ty} {rets succs β}
    {argTys : List SLLVM.Ty} {csigs : List (List SLLVM.Ty)} {cΓout : Ctxt SLLVM.Ty}
    {callee : String} {centry : BlockCom (Ctxt.ofList argTys.reverse) cΓout [] csigs}
    {cblocks : Blocks cΓout [] csigs csigs} {args : HVector Γ.Var argTys}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s : GlobalState}
    {P : PoisonOr (β × GlobalState) → Prop} {R : GlobalState → Prop} (hp : P .poison)
    (hcase : StateT.run (runFunction (Cfg.denote ⟨centry, cblocks⟩
          (Ctxt.Valuation.ofHVector (args.map V).reverse))) s = .poison
      ∨ ∃ s₁, StateT.run (runFunction (Cfg.denote ⟨centry, cblocks⟩
          (Ctxt.Valuation.ofHVector (args.map V).reverse))) s = .value (.nil, s₁) ∧ R s₁)
    (hk : ∀ s₁, R s₁ → ∃ res, StateT.run (body.denote V >>= k) s₁ = res ∧ P res) :
    ∃ res, StateT.run ((BlockCom.call callee centry cblocks args body).denote V >>= k) s = res
      ∧ P res := by
  rcases hcase with h | ⟨s₁, h, hR⟩
  · refine ⟨.poison, ?_, hp⟩
    rw [BlockCom.denote_call_eq, bind_assoc, EffectM.run_bind, h]; rfl
  · obtain ⟨res, hres, hP⟩ := hk s₁ hR
    exact ⟨res, (BlockCom.run_bind_denote_call_of_nil h).trans hres, hP⟩

theorem walk_condBr {Γ : Ctxt SLLVM.Ty} {rets succs β} {c : Γ.Var (Ty.bitvec 1)}
    {tT tF : Target Γ succs} {V : Γ.Valuation} {k : _ → EffectM β} {s : GlobalState}
    {P : PoisonOr (β × GlobalState) → Prop} (hp : P .poison)
    (hk : ∀ b, V c = .value b →
      ∃ res, StateT.run (k (V, .inr ((if b = 1 then tT else tF).denote V))) s = res ∧ P res) :
    ∃ res, StateT.run ((BlockCom.term (rets := rets) (.condBr c tT tF)).denote V >>= k) s = res
      ∧ P res := by
  rcases hc : V c with ⟨_ | b⟩
  · refine ⟨.poison, ?_, hp⟩
    rw [BlockCom.denote_term, Terminator.denote_condBr_poison hc]; rfl
  · obtain ⟨res, hres, hP⟩ := hk b hc
    refine ⟨res, ?_, hP⟩
    rw [BlockCom.denote_term, Terminator.denote_condBr_value hc]
    simpa only [bind_pure_comp, map_pure, pure_bind] using hres

theorem walk_br {Γ : Ctxt SLLVM.Ty} {rets succs β} {t : Target Γ succs} {V : Γ.Valuation}
    {k : _ → EffectM β} {s : GlobalState} {P : PoisonOr (β × GlobalState) → Prop}
    (hk : ∃ res, StateT.run (k (V, .inr (t.denote V))) s = res ∧ P res) :
    ∃ res, StateT.run ((BlockCom.term (rets := rets) (.br t)).denote V >>= k) s = res ∧ P res := by
  simpa only [BlockCom.denote_term, Terminator.denote_br, bind_pure_comp, map_pure, pure_bind]
    using hk

theorem walk_ret {Γ : Ctxt SLLVM.Ty} {rets succs β} {vs : HVector Γ.Var rets} {V : Γ.Valuation}
    {k : _ → EffectM β} {s : GlobalState} {P : PoisonOr (β × GlobalState) → Prop}
    (hk : ∃ res, StateT.run (k (V, .inl (vs.map V))) s = res ∧ P res) :
    ∃ res, StateT.run ((BlockCom.term (succs := succs) (.ret vs)).denote V >>= k) s = res
      ∧ P res := by
  simpa only [BlockCom.denote_term, Terminator.denote_ret, bind_pure_comp, map_pure, pure_bind]
    using hk

end LeanMLIR.SLLVM
