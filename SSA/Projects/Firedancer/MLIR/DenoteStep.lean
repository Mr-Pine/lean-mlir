/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.SLLVM.Tactic

/-!
# Sharing-preserving symbolic execution of pure `Com`s and CFG blocks

`simp_peephole` denotes a program by substituting every SSA value's defining
expression into all of its use sites. That turns the SSA DAG into a tree: for
programs that use intermediate values more than once (like
`fd_r43x6_mul_fast`, where the `t`-vectors, `zl` and `zb` all have fan-out
2-3), the fully inlined term grows multiplicatively and becomes intractable.

This file provides `denote_step_all`, which instead peels one let-binding at a
time: each instruction's value is `generalize`d to a fresh opaque variable
before the next instruction is processed, so a use of an intermediate value is
just a variable and sharing is preserved. The per-instruction definitions are
recorded as hypotheses `hv0 : v0 = …`, `hv1 : v1 = …`, …, which can then be
processed *individually* (each one is small), and used via `simp only [*]` to
expand uses of the `v<i>` on demand.

The same stepper drives the CFG layer's `BlockCom` (`SLLVM/Cfg/Basic.lean`),
whose cons shape is `Com`'s with the terminator generalised. Two differences
show up in the tactic rather than in the caller: a `BlockCom` is fixed
`.impure`, so only the pure-*operation* step applies, and a `Cfg`'s entry
block sits under a `bind` (`entry.denote V >>= fun (Vout, r) => …`), so the
step equation is transported through that as well as through `StateT.run`.
-/

namespace Firedancer.StepTactic
-- NOTE: `Expr`/`Com` live in the root namespace, so our helper defs do too;
-- this namespace only scopes the section variables.
end Firedancer.StepTactic

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  [Monad d.m] [LawfulMonad d.m]

/-- `Expr.denoteOp`, at the `HVector` type it definitionally has for a pure
expression. Having this as its own definition gives the stepping tactic a
stable head symbol to generalize, with a type that type-class resolution is
happy with. -/
def Expr.denoteOpPure {Γ : Ctxt d.Ty} {ts : List d.Ty}
    (e : Expr d Γ .pure ts) (V : Γ.Valuation) : HVector TyDenote.toType ts :=
  e.denoteOp V

/-- The head value of a pure single-result expression. -/
def Expr.denoteOp1 {Γ : Ctxt d.Ty} {t : d.Ty}
    (e : Expr d Γ .pure [t]) (V : Γ.Valuation) : TyDenote.toType t :=
  (e.denoteOpPure V).head

theorem Com.denote_var_pure {Γ : Ctxt d.Ty} {ts' ts : List d.Ty}
    (e : Expr d Γ .pure ts') (body : Com d e.outContext .pure ts)
    (V : Γ.Valuation) :
    (Com.var e body).denote V
      = body.denote (e.denoteOpPure V ++ V) := by
  rcases e with ⟨op, rfl, eff_le, args, regArgs⟩
  simp only [Com.denote_var, Expr.denote, Expr.denoteOpPure, Expr.denoteOp]
  rfl

/-- As `Com.denote_var_pure`, but for the (common) single-result case, pushing
the value into the valuation as a `Valuation.cons`. -/
theorem Com.denote_var_pure_single {Γ : Ctxt d.Ty} {t : d.Ty} {ts : List d.Ty}
    (e : Expr d Γ .pure [t]) (body : Com d e.outContext .pure ts)
    (V : Γ.Valuation) :
    (Com.var e body).denote V
      = body.denote (e.denoteOp1 V ::ᵥ V) := by
  rw [Com.denote_var_pure]
  congr 1
  show e.denoteOpPure V ++ V = (e.denoteOpPure V).head ::ᵥ V
  generalize e.denoteOpPure V = w
  cases w
  case cons a as =>
    cases as
    show (Ctxt.Valuation.ofHVector (a ::ₕ .nil)) ++ V = a ::ᵥ V
    simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
      Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]

/-- The impure counterpart of `Com.denote_var_pure`.

A region that ends in a store parses as one `.impure` `Com`, so *every*
instruction in it -- including all the arithmetic -- is an `Expr … .impure …`
carrying `eff_le : .pure ≤ .impure`. `Com.denote_var_pure` does not apply, but
the denotation still collapses: `Expr.denote` of a pure-op expression is
`pure (…)`, and `pure x >>= f = f x`. -/
theorem Com.denote_var_pureOp {Γ : Ctxt d.Ty} {ts' ts : List d.Ty}
    (e : Expr d Γ .impure ts') (h : e.HasPureOp)
    (body : Com d e.outContext .impure ts) (V : Γ.Valuation) :
    (Com.var e body).denote V = body.denote ((e.toPure h).denoteOpPure V ++ V) := by
  simp only [Com.denote_var, Expr.denote_unfold]
  rw [← Expr.pure_denoteOp_toPure e h]
  simp only [map_pure, pure_bind, Expr.denoteOpPure]

/-- As `Com.denote_var_pureOp`, for the single-result case, pushing the value
into the valuation as a `Valuation.cons`. -/
theorem Com.denote_var_pureOp_single {Γ : Ctxt d.Ty} {t : d.Ty} {ts : List d.Ty}
    (e : Expr d Γ .impure [t]) (h : e.HasPureOp)
    (body : Com d e.outContext .impure ts) (V : Γ.Valuation) :
    (Com.var e body).denote V = body.denote ((e.toPure h).denoteOp1 V ::ᵥ V) := by
  rw [Com.denote_var_pureOp e h]
  congr 1
  show (e.toPure h).denoteOpPure V ++ V = ((e.toPure h).denoteOpPure V).head ::ᵥ V
  generalize (e.toPure h).denoteOpPure V = w
  cases w
  case cons a as =>
    cases as
    show (Ctxt.Valuation.ofHVector (a ::ₕ .nil)) ++ V = a ::ᵥ V
    simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
      Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]

/-! ## The CFG layer

`BlockCom`'s effect is fixed `.impure`, so there is no counterpart to
`Com.denote_var_pure_single` here: every instruction in a block, arithmetic
included, is an `Expr … .impure …` carrying a pure operation, and the
`pureOp` step is the only one needed. -/

namespace LeanMLIR.SLLVM

/-- `Com.denote_var_pureOp`, for a CFG block. -/
theorem BlockCom.denote_var_pureOp {Γ Γout : Ctxt SLLVM.Ty} {ts rets succs}
    (e : Expr SLLVM Γ .impure ts) (h : e.HasPureOp)
    (body : BlockCom (ts ++ Γ) Γout rets succs) (V : Γ.Valuation) :
    (BlockCom.var e body).denote V = body.denote ((e.toPure h).denoteOpPure V ++ V) := by
  simp only [BlockCom.denote_var, Expr.denote_unfold]
  rw [← Expr.pure_denoteOp_toPure e h]
  simp only [map_pure, pure_bind, Expr.denoteOpPure]

/-- As `BlockCom.denote_var_pureOp`, for the single-result case, pushing the
value into the valuation as a `Valuation.cons`. -/
theorem BlockCom.denote_var_pureOp_single {Γ Γout : Ctxt SLLVM.Ty} {t rets succs}
    (e : Expr SLLVM Γ .impure [t]) (h : e.HasPureOp)
    (body : BlockCom ([t] ++ Γ) Γout rets succs) (V : Γ.Valuation) :
    (BlockCom.var e body).denote V = body.denote ((e.toPure h).denoteOp1 V ::ᵥ V) := by
  rw [BlockCom.denote_var_pureOp e h]
  congr 1
  show (e.toPure h).denoteOpPure V ++ V = ((e.toPure h).denoteOpPure V).head ::ᵥ V
  generalize (e.toPure h).denoteOpPure V = w
  cases w
  rename_i a as
  cases as
  · show (Ctxt.Valuation.ofHVector (a ::ₕ .nil)) ++ V = a ::ᵥ V
    simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
      Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]

/-! ### Peeling an impure instruction

The stepper stops at a load or a store: its value is not a function of the
valuation, so nothing can name it until the proof has shown the access does
not trap. These lemmas are the manual continuation -- supply "this
instruction succeeds, with this value and this resulting state" and the goal
peels exactly as a pure step does, staying in `body.denote (v ::ᵥ V)` form
rather than unfolding into `do`-notation. The `>>= k` variant is the one a
`Cfg` entry block needs, `k` being the dispatch on its terminator. -/

/-- Sequencing on a *successful* `EffectM` step: the continuation runs at the
state the first step produced. -/
theorem EffectM.run_bind_of_value {α β} {x : EffectM α} {f : α → EffectM β}
    {s s' : GlobalState} {a : α} (h : StateT.run x s = .value (a, s')) :
    StateT.run (x >>= f) s = StateT.run (f a) s' := by
  rw [EffectM.run_bind, h]; rfl

/-- `[x]ₕ ++ V` is `V` extended by `x`; the bridge between `Expr.denote`'s
`HVector` append and the `cons` spine the stepper maintains. -/
private theorem single_append {Γ : Ctxt SLLVM.Ty} {t} (x : ⟦t⟧) (V : Γ.Valuation) :
    ((x ::ₕ .nil : HVector _ [t]) ++ V) = x ::ᵥ V := by
  show (Ctxt.Valuation.ofHVector (x ::ₕ .nil)) ++ V = x ::ᵥ V
  simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
    Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]

/-- One impure instruction, given that it succeeds with value `x` and leaves
the state at `s'`. -/
theorem BlockCom.run_denote_var_of_value {Γ Γout : Ctxt SLLVM.Ty} {t rets succs}
    {e : Expr SLLVM Γ .impure [t]} {body : BlockCom ([t] ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {s s' : GlobalState} {x : ⟦t⟧}
    (h : StateT.run (e.denoteOp V) s = .value ([x]ₕ, s')) :
    StateT.run ((BlockCom.var e body).denote V) s
      = StateT.run (body.denote (x ::ᵥ V)) s' := by
  rw [BlockCom.denote_var, Expr.denote_unfold,
    EffectM.run_bind_of_value (a := ([x]ₕ : HVector _ [t]) ++ V) (s' := s')
      (by rw [EffectM.run_map, h]; rfl),
    single_append]

/-- As `BlockCom.run_denote_var_of_value`, under the `bind` a `Cfg`'s entry
block sits in. -/
theorem BlockCom.run_bind_denote_var_of_value {Γ Γout : Ctxt SLLVM.Ty} {t rets succs β}
    {e : Expr SLLVM Γ .impure [t]} {body : BlockCom ([t] ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s s' : GlobalState} {x : ⟦t⟧}
    (h : StateT.run (e.denoteOp V) s = .value ([x]ₕ, s')) :
    StateT.run ((BlockCom.var e body).denote V >>= k) s
      = StateT.run (body.denote (x ::ᵥ V) >>= k) s' := by
  rw [BlockCom.denote_var, bind_assoc, Expr.denote_unfold,
    EffectM.run_bind_of_value (a := ([x]ₕ : HVector _ [t]) ++ V) (s' := s')
      (by rw [EffectM.run_map, h]; rfl),
    single_append]

/-- `.nil ++ V` is `V`; the nil-result counterpart of `single_append`, for the
instructions that bind nothing. -/
private theorem nil_append {Γ : Ctxt SLLVM.Ty} (V : Γ.Valuation) :
    ((.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)) ++ V) = V := by
  show (Ctxt.Valuation.ofHVector
      (.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty))) ++ V = V
  simp only [Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.nil_append]

/-- One impure instruction that binds no variable -- a `store` -- given that it
succeeds and leaves the state at `s'`. The valuation is untouched, so unlike
`run_bind_denote_var_of_value` this does not extend the `cons` spine. -/
theorem BlockCom.run_bind_denote_var_of_nil {Γ Γout : Ctxt SLLVM.Ty} {rets succs β}
    {e : Expr SLLVM Γ .impure []}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s s' : GlobalState}
    (h : StateT.run (e.denoteOp V) s = .value (.nil, s')) :
    StateT.run ((BlockCom.var e body).denote V >>= k) s
      = StateT.run (body.denote V >>= k) s' := by
  rw [BlockCom.denote_var, bind_assoc, Expr.denote_unfold,
    EffectM.run_bind_of_value
      (a := (HVector.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)) ++ V) (s' := s')
      (by rw [EffectM.run_map, h]; rfl),
    nil_append]

/-- Step a lifetime marker: it denotes to `pure []ₕ`, so neither the state nor
the valuation moves. Unlike `run_bind_denote_var_of_nil` this leaves no `s'`
for the use site to determine, so it applies as a bare `rw`. -/
theorem BlockCom.run_bind_denote_lifetime {Γ Γout : Ctxt SLLVM.Ty} {rets succs β}
    {start : Bool} {p : Ctxt.Var Γ .ptr}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s : GlobalState} :
    StateT.run ((BlockCom.var
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
          (SLLVMOp.lifetime start) rfl (EffectKind.le_refl _)
          (p ::ₕ .nil) Regions.nil) body).denote V >>= k) s
      = StateT.run (body.denote V >>= k) s :=
  BlockCom.run_bind_denote_var_of_nil (by simp only [denoteOp_lifetime, EffectM.run_pure])

/-- One `call` that returns nothing, given that the callee -- run as a function
on the call's arguments -- succeeds and leaves the state at `s'`. The callee is
a `Cfg` in `h`, which is the form its own conformance theorem is stated in, so
a proven callee is a single rewrite here rather than a re-derivation. -/
theorem BlockCom.run_bind_denote_call_of_nil {Γ Γout : Ctxt SLLVM.Ty} {rets succs β}
    {argTys : List SLLVM.Ty} {csigs : List (List SLLVM.Ty)} {cΓout : Ctxt SLLVM.Ty}
    {callee : String}
    {centry : BlockCom (Ctxt.ofList argTys.reverse) cΓout [] csigs}
    {cblocks : Blocks cΓout [] csigs csigs}
    {args : HVector Γ.Var argTys}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s s' : GlobalState}
    (h : StateT.run (runFunction
        (Cfg.denote ⟨centry, cblocks⟩ (Ctxt.Valuation.ofHVector (args.map V).reverse))) s
      = .value (.nil, s')) :
    StateT.run ((BlockCom.call callee centry cblocks args body).denote V >>= k) s
      = StateT.run (body.denote V >>= k) s' := by
  -- `denote_call` inlines the callee rather than naming it, and its `match`es
  -- are a different auxiliary from `Cfg.denote`'s, so the two forms have to be
  -- reconciled by destructing rather than by `rfl`.
  have hcall : BlockCom.denote (.call callee centry cblocks args body) V
      = (runFunction (Cfg.denote ⟨centry, cblocks⟩
            (Ctxt.Valuation.ofHVector (args.map V).reverse))
          >>= fun rs => body.denote (rs ++ V)) := by
    rw [BlockCom.denote_call]
    refine congrArg (fun m => runFunction m >>= fun rs => body.denote (rs ++ V)) ?_
    simp only [Cfg.denote]
    refine congrArg (Bind.bind (centry.denote _)) ?_
    funext x
    obtain ⟨Vc, r⟩ := x
    cases r <;> rfl
  rw [hcall, bind_assoc,
    EffectM.run_bind_of_value
      (a := (HVector.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)))
      (s' := s') h,
    nil_append]

/-- As `run_bind_denote_call_of_nil`, for a call that binds its result: the
returned value enters the valuation and the state advances to `s'`. -/
theorem BlockCom.run_bind_denote_call_of_value {Γ Γout : Ctxt SLLVM.Ty} {t rets succs β}
    {argTys : List SLLVM.Ty} {csigs : List (List SLLVM.Ty)} {cΓout : Ctxt SLLVM.Ty}
    {callee : String}
    {centry : BlockCom (Ctxt.ofList argTys.reverse) cΓout [t] csigs}
    {cblocks : Blocks cΓout [t] csigs csigs}
    {args : HVector Γ.Var argTys}
    {body : BlockCom (([t] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s s' : GlobalState} {x : ⟦t⟧}
    (h : StateT.run (runFunction
        (Cfg.denote ⟨centry, cblocks⟩ (Ctxt.Valuation.ofHVector (args.map V).reverse))) s
      = .value ([x]ₕ, s')) :
    StateT.run ((BlockCom.call callee centry cblocks args body).denote V >>= k) s
      = StateT.run (body.denote (x ::ᵥ V) >>= k) s' := by
  have hcall : BlockCom.denote (.call callee centry cblocks args body) V
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
  rw [hcall, bind_assoc,
    EffectM.run_bind_of_value (a := ([x]ₕ : HVector _ [t])) (s' := s') h,
    single_append]

/-! ### Calls in a bare block denotation

`Blocks.run_loop`'s step obligation states a block's denotation on its own,
with no `>>=` continuation -- unlike `Cfg.denote`, which binds the entry
block's result. These are the `k := pure` specialisations of the two lemmas
above, in the shape a loop-body goal actually has. -/

theorem BlockCom.run_denote_call_of_nil {Γ Γout : Ctxt SLLVM.Ty} {rets succs}
    {argTys : List SLLVM.Ty} {csigs : List (List SLLVM.Ty)} {cΓout : Ctxt SLLVM.Ty}
    {callee : String}
    {centry : BlockCom (Ctxt.ofList argTys.reverse) cΓout [] csigs}
    {cblocks : Blocks cΓout [] csigs csigs}
    {args : HVector Γ.Var argTys}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {s s' : GlobalState}
    (h : StateT.run (runFunction
        (Cfg.denote ⟨centry, cblocks⟩ (Ctxt.Valuation.ofHVector (args.map V).reverse))) s
      = .value (.nil, s')) :
    StateT.run ((BlockCom.call callee centry cblocks args body).denote V) s
      = StateT.run (body.denote V) s' := by
  have h2 : StateT.run ((BlockCom.call callee centry cblocks args body).denote V >>= pure) s
      = StateT.run (body.denote V >>= pure) s' :=
    BlockCom.run_bind_denote_call_of_nil h
  simpa only [bind_pure] using h2

/-- `run_bind_denote_call_of_value` for a callee held by reference, with the
operand vector supplied rather than inferred.

This is what a *tail* block needs. There the ambient valuation is an opaque
variable, so `(args.map V).reverse` is not defeq to the callee's argument list
-- it becomes so only after the block's pinned-entry facts are rewritten in,
which is what `hargs` is for. Without it the plain bind lemma's `exact` grinds
on a defeq check it cannot discharge. -/
theorem BlockCom.run_bind_denote_call_cfg_of_value {Γ Γout : Ctxt SLLVM.Ty} {t rets succs β}
    {argTys : List SLLVM.Ty} {callee : String}
    {c : Cfg (Ctxt.ofList argTys.reverse) [t]}
    {args : HVector Γ.Var argTys}
    {body : BlockCom (([t] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s s' : GlobalState} {x : ⟦t⟧}
    {argVals : HVector toType argTys.reverse}
    (hargs : (args.map V).reverse = argVals)
    (h : StateT.run (runFunction (c.denote (Ctxt.Valuation.ofHVector argVals))) s
      = .value ([x]ₕ, s')) :
    StateT.run ((BlockCom.call callee c.entry c.blocks args body).denote V >>= k) s
      = StateT.run (body.denote (x ::ᵥ V) >>= k) s' :=
  BlockCom.run_bind_denote_call_of_value (by rw [Cfg.denote_mk_self, hargs]; exact h)

theorem BlockCom.run_denote_call_of_value {Γ Γout : Ctxt SLLVM.Ty} {t rets succs}
    {argTys : List SLLVM.Ty} {csigs : List (List SLLVM.Ty)} {cΓout : Ctxt SLLVM.Ty}
    {callee : String}
    {centry : BlockCom (Ctxt.ofList argTys.reverse) cΓout [t] csigs}
    {cblocks : Blocks cΓout [t] csigs csigs}
    {args : HVector Γ.Var argTys}
    {body : BlockCom (([t] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {s s' : GlobalState} {x : ⟦t⟧}
    (h : StateT.run (runFunction
        (Cfg.denote ⟨centry, cblocks⟩ (Ctxt.Valuation.ofHVector (args.map V).reverse))) s
      = .value ([x]ₕ, s')) :
    StateT.run ((BlockCom.call callee centry cblocks args body).denote V) s
      = StateT.run (body.denote (x ::ᵥ V)) s' := by
  have h2 : StateT.run ((BlockCom.call callee centry cblocks args body).denote V >>= pure) s
      = StateT.run (body.denote (x ::ᵥ V) >>= pure) s' :=
    BlockCom.run_bind_denote_call_of_value h
  simpa only [bind_pure] using h2

/-- `run_denote_call_of_value` for a callee embedded *by reference*: the call
node holds `c.entry`/`c.blocks` for a lifted constant `c`, and the hypothesis
is that constant's own conformance statement. Stating it over an abstract `c`
is what keeps it cheap -- the `⟨c.entry, c.blocks⟩ = c` eta step is discharged
here, once, rather than at each call site where `c` is a large constant. -/
theorem BlockCom.run_denote_call_cfg_of_value {Γ Γout : Ctxt SLLVM.Ty} {t rets succs}
    {argTys : List SLLVM.Ty} {callee : String}
    {c : Cfg (Ctxt.ofList argTys.reverse) [t]}
    {args : HVector Γ.Var argTys}
    {body : BlockCom (([t] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {s s' : GlobalState} {x : ⟦t⟧}
    {argVals : HVector toType argTys.reverse}
    (hargs : (args.map V).reverse = argVals)
    (h : StateT.run (runFunction
        (c.denote (Ctxt.Valuation.ofHVector argVals))) s
      = .value ([x]ₕ, s')) :
    StateT.run ((BlockCom.call callee c.entry c.blocks args body).denote V) s
      = StateT.run (body.denote (x ::ᵥ V)) s' :=
  BlockCom.run_denote_call_of_value
    (by rw [Cfg.denote_mk_self, hargs]; exact h)

/-- `run_bind_denote_call_of_nil` for a callee held by reference, with the
operand vector supplied rather than inferred.

Without `hargs` the only route is the plain bind lemma, whose `exact` unifies
the operand vector against the block's valuation by `whnf`. That cost grows
with every instruction already peeled, so in a long block the later calls
dominate everything else. Staged here; belongs in `MLIR/DenoteStep.lean`
beside its non-bind sibling. -/
theorem BlockCom.run_bind_denote_call_cfg_of_nil
    {Γ Γout : Ctxt SLLVM.Ty} {rets succs β} {argTys : List SLLVM.Ty} {callee : String}
    {c : Cfg (Ctxt.ofList argTys.reverse) []}
    {args : HVector Γ.Var argTys}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s s' : GlobalState}
    {argVals : HVector toType argTys.reverse}
    (hargs : (args.map V).reverse = argVals)
    (h : StateT.run (runFunction (c.denote (Ctxt.Valuation.ofHVector argVals))) s
      = .value (.nil, s')) :
    StateT.run ((BlockCom.call callee c.entry c.blocks args body).denote V >>= k) s
      = StateT.run (body.denote V >>= k) s' :=
  BlockCom.run_bind_denote_call_of_nil (by rw [Cfg.denote_mk_self, hargs]; exact h)

/-- `run_denote_call_cfg_of_value`, for a callee that returns nothing. -/
theorem BlockCom.run_denote_call_cfg_of_nil {Γ Γout : Ctxt SLLVM.Ty} {rets succs}
    {argTys : List SLLVM.Ty} {callee : String}
    {c : Cfg (Ctxt.ofList argTys.reverse) []}
    {args : HVector Γ.Var argTys}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {s s' : GlobalState}
    {argVals : HVector toType argTys.reverse}
    (hargs : (args.map V).reverse = argVals)
    (h : StateT.run (runFunction
        (c.denote (Ctxt.Valuation.ofHVector argVals))) s
      = .value (.nil, s')) :
    StateT.run ((BlockCom.call callee c.entry c.blocks args body).denote V) s
      = StateT.run (body.denote V) s' :=
  BlockCom.run_denote_call_of_nil
    (by rw [Cfg.denote_mk_self, hargs]; exact h)

/-! ### Entering a block

With back-edges, the walk through the tail blocks is `Blocks.run`, and
`Blocks.run_step` (`Cfg/Eval.lean`) is its one-transition equation. The
`denote_enter_block` tactic below applies it and then reduces the
`Blocks.get` lookup away, so only the entered block is materialised -- the
skipped blocks and the continuation's `bs` stay folded behind the region's
definition. -/

/-- Walk a loop by its invariant: `t k` is the program point at iteration `k`
(the header with its φ values), `Inv k` the state invariant there, and each
step runs the block at `t k` and lands on `t (k + 1)`. After `n` iterations
the walk stands at `t n` -- typically the loop's exit target -- with `Inv n`.
Proof-time only: `n` is supplied here, the transform never computes it. -/
theorem _root_.LeanMLIR.SLLVM.Blocks.run_loop {Γamb : Ctxt SLLVM.Ty}
    {rets : List SLLVM.Ty} {all : List (List SLLVM.Ty)}
    {bs : Blocks Γamb rets all all} {Vamb : Γamb.Valuation}
    (Inv : Nat → GlobalState → Prop) (t : Nat → SuccArgs all) (n : Nat)
    (hstep : ∀ k s, k < n → Inv k s → ∃ Vout s',
      StateT.run ((bs.get (t k).idx (t k).hidx).2.denote
          (Ctxt.Valuation.ofHVector (t k).args.reverse ++ Vamb)) s
        = .value ((Vout, .inr (t (k + 1))), s') ∧ Inv (k + 1) s')
    {s₀ : GlobalState} (h₀ : Inv 0 s₀) :
    ∃ s', StateT.run (bs.run Vamb (t 0)) s₀ = StateT.run (bs.run Vamb (t n)) s'
      ∧ Inv n s' := by
  suffices h : ∀ d k s, n = k + d → Inv k s → ∃ s',
      StateT.run (bs.run Vamb (t k)) s = StateT.run (bs.run Vamb (t n)) s'
        ∧ Inv n s' from h n 0 s₀ (by omega) h₀
  intro d
  induction d with
  | zero =>
      intro k s hkd hInv
      have hk : k = n := by omega
      subst hk
      exact ⟨s, rfl, hInv⟩
  | succ d ih =>
      intro k s hkd hInv
      obtain ⟨Vout, s', hrun, hInv'⟩ := hstep k s (by omega) hInv
      obtain ⟨s'', heq, hInvn⟩ := ih (k + 1) s' (by omega) hInv'
      refine ⟨s'', ?_, hInvn⟩
      rw [Blocks.run_step (t := t k), EffectM.run_bind, hrun, PoisonOr.value_bind]
      show StateT.run (bs.run Vamb (t (k + 1))) s' = _
      exact heq

/-- The general termination rule: any walk whose steps preserve `Inv` and
strictly decrease `μ` until a `ret` fires ends in a state satisfying `Q`.
Covers multi-block and nested loops -- it never mentions loop structure. -/
theorem _root_.LeanMLIR.SLLVM.Blocks.run_of_variant {Γamb : Ctxt SLLVM.Ty}
    {rets : List SLLVM.Ty} {all : List (List SLLVM.Ty)}
    {bs : Blocks Γamb rets all all} {Vamb : Γamb.Valuation}
    (Inv : SuccArgs all → GlobalState → Prop)
    (μ : SuccArgs all → GlobalState → Nat)
    (Q : HVector toType rets → GlobalState → Prop)
    (hstep : ∀ t s, Inv t s → ∃ p s',
      StateT.run ((bs.get t.idx t.hidx).2.denote
          (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb)) s = .value (p, s')
      ∧ (∀ res, p.2 = .inl res → Q res s')
      ∧ (∀ t', p.2 = .inr t' → Inv t' s' ∧ μ t' s' < μ t s))
    {t₀ : SuccArgs all} {s₀ : GlobalState} (h₀ : Inv t₀ s₀) :
    ∃ rs s', StateT.run (bs.run Vamb t₀) s₀ = .value (rs, s') ∧ Q rs s' := by
  suffices h : ∀ m t s, μ t s ≤ m → Inv t s → ∃ rs s',
      StateT.run (bs.run Vamb t) s = .value (rs, s') ∧ Q rs s' from
    h (μ t₀ s₀) t₀ s₀ le_rfl h₀
  intro m
  induction m with
  | zero =>
      intro t s hμ hInv
      obtain ⟨⟨Vout, r⟩, s', hrun, hinl, hinr⟩ := hstep t s hInv
      cases r with
      | inl res =>
          refine ⟨res, s', ?_, hinl res rfl⟩
          rw [Blocks.run_step, EffectM.run_bind, hrun, PoisonOr.value_bind]
          rfl
      | inr t' => exact absurd (hinr t' rfl).2 (by omega)
  | succ m ih =>
      intro t s hμ hInv
      obtain ⟨⟨Vout, r⟩, s', hrun, hinl, hinr⟩ := hstep t s hInv
      cases r with
      | inl res =>
          refine ⟨res, s', ?_, hinl res rfl⟩
          rw [Blocks.run_step, EffectM.run_bind, hrun, PoisonOr.value_bind]
          rfl
      | inr t' =>
          obtain ⟨hInv', hlt⟩ := hinr t' rfl
          obtain ⟨rs, s'', heq, hQ⟩ := ih t' s' (by omega) hInv'
          refine ⟨rs, s'', ?_, hQ⟩
          rw [Blocks.run_step, EffectM.run_bind, hrun, PoisonOr.value_bind]
          exact heq

end LeanMLIR.SLLVM

open Lean Meta in
/-- Peel the wrappers that can sit between the goal's left-hand side and the
denotation being stepped, returning the core denotation, a function rebuilding
the wrappers around a new core, and whether anything was peeled at all.

Two shapes occur, and they nest. A derivation that threads a state works on
`(com.denote V).run s`; a pure(-op) step does not touch the state, so the
denote-level step equation still applies -- it just has to be transported
through the `StateT.run … s` wrapper. A `Cfg`'s entry block additionally sits
under a `bind`: `simp only [Cfg.denote]` leaves
`entry.denote V >>= fun (Vout, r) => …`, of which only the first argument is
being stepped. In both the payload is the second-to-last argument of the head,
so one descent covers them.

`whnfR` does not unfold `bind`, so a `do` block keeps its shape here. -/
private partial def peelWrappers (e : Lean.Expr) :
    MetaM (Lean.Expr × (Lean.Expr → Lean.Expr) × Bool) := do
  let e ← whnfR e
  if e.isAppOf ``StateT.run || e.isAppOf ``Bind.bind then
    let fn := e.getAppFn
    let args := e.getAppArgs
    if args.size ≥ 2 then
      let i := args.size - 2
      let (core, rebuild, _) ← peelWrappers args[i]!
      return (core, (fun X => mkAppN fn (args.set! i (rebuild X))), true)
  return (e, id, false)

open Lean Meta in
/-- Is this the denotation a stepper works on? -/
private def isDenoteTerm (e : Lean.Expr) : MetaM Bool := do
  let (core, _, _) ← peelWrappers e
  return core.isAppOf ``Com.denote || core.isAppOf ``LeanMLIR.SLLVM.BlockCom.denote
    || core.isAppOf ``LeanMLIR.SLLVM.Cfg.denote

open Lean Meta in
/-- The denotation a stepper works on, and the goal's own right-hand side when
the goal *is* that equation.

Usually it is: the walk's goal is `StateT.run … s = …`. In the exec clause of a
conformance statement -- `∃ s', StateT.run … = .value (rets, s') ∧ …` -- the
equation sits inside the binder instead, so the search descends the goal's
logical structure to find it. Only that structure is descended, never the
denotation's own subterms, or a `Blocks.run` goal would match something nested
inside the region it mentions.

The bound state never occurs in the denotation, which is what the
`hasLooseBVars` guard checks; without a right-hand side the caller rewrites the
goal in place rather than by transitivity. -/
private partial def findDenoteTerm? (tgt : Lean.Expr) :
    MetaM (Option (Lean.Expr × Option Lean.Expr)) := do
  let tgt ← whnfR tgt
  -- an equation goal is what the steppers have always worked on: its left-hand
  -- side is the term, whatever it denotes -- `Blocks.run` included
  if let some (_, lhs, rhs) := tgt.eq? then
    if lhs.hasLooseBVars then return none
    return some (lhs, some rhs)
  if tgt.isAppOf ``Exists || tgt.isAppOf ``And then
    for arg in tgt.getAppArgs do
      let body := if arg.isLambda then arg.bindingBody! else arg
      if let some (lhs, _) ← findDenoteTerm? body then
        unless lhs.hasLooseBVars do return some (lhs, none)
  return none

open Lean Meta in
/-- A proof of `e.HasPureOp`, or `none` when the operation is not pure.

`mkDecideProof` does *not* check that `decide p` reduces to `true`: it emits
`of_decide_eq_true (id rfl)` with a type ascription and leaves the failure to
the kernel. Evaluating the decision here is what makes the stepper stop at an
impure instruction (a load, a store) instead of stepping it and producing a
proof the kernel rejects at the end of the declaration. -/
private def mkPurityProof? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  try
    let hasPure ← mkAppM ``Expr.HasPureOp #[e]
    unless (← whnf (← mkDecide hasPure)).isConstOf ``Bool.true do return none
    return some (← mkDecideProof hasPure)
  catch _ => return none

open Lean Meta in
/-- The program argument of a `denote`, reduced far enough to expose its head
constructor. A hand-written `Com` is already a constructor application, but a
quoted region's entry block reaches the goal as `cfg.entry`, whose projection
hides behind the auxiliary definitions the elaborator generates -- reducible
transparency does not see through those, so fall back to `whnf`, which stops
at the constructor. -/
private def whnfProgram (e : Lean.Expr) : MetaM Lean.Expr := do
  let e' ← whnfR e
  if e'.isAppOf ``Com.var || e'.isAppOf ``LeanMLIR.SLLVM.BlockCom.var then
    return e'
  try whnf e catch _ => return e'

open Lean Meta Elab Tactic in
/-- One step of `denote_step_all`: if the main goal has the shape
`(Com.var e body).denote V = rhs` (or the `BlockCom.var` counterpart, under
any of the wrappers `peelWrappers` handles), introduce `v<i> : _` together
with `hv<i> : v<i> = e.denoteOp1 V` and return the goal
`body.denote (v<i> ::ᵥ V) = rhs`. Returns `none` if the goal is not of that
shape (i.e. the program is exhausted). -/
private def denoteStep1 (goal : MVarId) (baseName : Name) (i : Nat)
    (inline : Bool := false) : MetaM (Option MVarId) :=
  goal.withContext do
    let tgt ← whnfR (← instantiateMVars (← goal.getType))
    let some (lhs, rhs?) ← findDenoteTerm? tgt | return none
    let (core, rebuild, wrapped) ← peelWrappers lhs
    if core.isAppOf ``LeanMLIR.SLLVM.Cfg.denote then
      throwError "denote_step_all: the goal is still a whole `Cfg.denote`. Run \
        `simp only [Cfg.denote]` first, which splits it into the entry block \
        and the dispatch on its terminator; the entry block is what steps."
    let isBlock := core.isAppOf ``LeanMLIR.SLLVM.BlockCom.denote
    unless core.isAppOf ``Com.denote || isBlock do return none
    let coreArgs := core.getAppArgs
    unless coreArgs.size ≥ 2 do return none
    let com ← whnfProgram coreArgs[coreArgs.size - 2]!
    let V := coreArgs[coreArgs.size - 1]!
    unless com.isAppOf (if isBlock then ``LeanMLIR.SLLVM.BlockCom.var else ``Com.var) do
      return none
    let comArgs := com.getAppArgs
    unless comArgs.size ≥ 2 do return none
    let e := comArgs[comArgs.size - 2]!
    let body := comArgs[comArgs.size - 1]!
    -- stepEq : (Com.var e body).denote V = body.denote (e.denoteOp1 V ::ᵥ V)
    --
    -- A `Com` that ends in a store is `.impure` throughout, so its arithmetic
    -- instructions are impure-typed expressions carrying pure *operations*.
    -- Try the pure lemma first; if the expression is impure-typed, fall back to
    -- `Com.denote_var_pureOp_single`, which needs a purity proof for the op and
    -- steps through `e.toPure`. Both leave a pure `Expr.denoteOp1` behind, so
    -- everything downstream is unaffected.
    --
    -- A `BlockCom` has no `.pure`-typed form at all, so it takes the `pureOp`
    -- path unconditionally; an instruction that is genuinely impure (a load,
    -- a store) has no purity proof and stops the stepper there.
    let mkStep : MetaM (Option (Lean.Expr × Lean.Expr)) := do
      if isBlock then
        let some hProof ← mkPurityProof? e | return none
        try
          let stepEq ← mkAppM ``LeanMLIR.SLLVM.BlockCom.denote_var_pureOp_single
            #[e, hProof, body, V]
          let tVal ← mkAppM ``Expr.denoteOp1 #[← mkAppM ``Expr.toPure #[e, hProof], V]
          return some (stepEq, tVal)
        catch _ => return none
      try
        let stepEq ← mkAppM ``Com.denote_var_pure_single #[e, body, V]
        let tVal ← mkAppM ``Expr.denoteOp1 #[e, V]
        return some (stepEq, tVal)
      catch _ =>
        let some hProof ← mkPurityProof? e | return none
        try
          let stepEq ← mkAppM ``Com.denote_var_pureOp_single #[e, hProof, body, V]
          -- The `hv<i>` this leaves behind reads `(e.toPure h).denoteOp1 V`
          -- rather than the pure path's `e.denoteOp1 V`. `simp_denote` carries
          -- `Expr.op_toPure` and friends so that the projections still reduce to
          -- those of the underlying `Expr.mk`, which is what keeps every
          -- downstream tactic working unchanged.
          let tVal ← mkAppM ``Expr.denoteOp1 #[← mkAppM ``Expr.toPure #[e, hProof], V]
          return some (stepEq, tVal)
        catch _ => return none
    let some (stepEq, tVal) ← mkStep | return none
    -- Transport the denote-level step equation through whatever wrappers the
    -- goal has around the denotation: `congrArg (fun X => <wrappers> X)`.
    let stepEq ←
      if wrapped then
        let some (ty, _, _) := (← inferType stepEq).eq?
          | throwError "denote_step_all: step equation is not an equality"
        let lam ← withLocalDeclD `X ty fun X => mkLambdaFVars #[X] (rebuild X)
        mkCongrArg lam stepEq
      else
        pure stepEq
    -- `inline`: drop the value straight into the valuation spine instead of
    -- naming it, so no `v<i>`/`hv<i>` is introduced for this instruction.
    -- The goal's own equation is rewritten by transitivity; a denotation found
    -- inside a larger goal, by `Eq.mpr` through the abstraction.
    let mkNewGoal (newLhs : Lean.Expr) : MetaM Lean.Expr := do
      match rhs? with
      | some rhs => mkEq newLhs rhs
      | none => return (← kabstract tgt lhs).instantiate1 newLhs
    let close (contPrf : Lean.Expr) : MetaM Lean.Expr := do
      match rhs? with
      | some _ => mkEqTrans stepEq contPrf
      | none =>
        let motive := Lean.Expr.lam `X (← inferType lhs) (← kabstract tgt lhs) .default
        mkEqMPR (← mkCongrArg motive stepEq) contPrf
    if inline then
      let consV ← mkAppM ``Ctxt.Valuation.cons #[tVal, V]
      let newLhs ← mkAppM
        (if isBlock then ``LeanMLIR.SLLVM.BlockCom.denote else ``Com.denote) #[body, consV]
      let newLhs := if wrapped then rebuild newLhs else newLhs
      let newGoal ← mkFreshExprSyntheticOpaqueMVar (← mkNewGoal newLhs)
      goal.assign (← close newGoal)
      return some newGoal.mvarId!
    let vName := baseName.appendAfter (toString i)
    let hName := Name.mkSimple ("h" ++ vName.toString)
    -- newType : ∀ v, v = e.denoteOp1 V → body.denote (v ::ᵥ V) = rhs
    -- (oriented `v = def` so `simp only [*]` expands uses of `v` on demand);
    -- the conclusion's left-hand side keeps whatever wrappers it had.
    let newType ← withLocalDeclD vName (← inferType tVal) fun v => do
      let defEq ← mkEq v tVal
      let consV ← mkAppM ``Ctxt.Valuation.cons #[v, V]
      let newLhs ← mkAppM
        (if isBlock then ``LeanMLIR.SLLVM.BlockCom.denote else ``Com.denote) #[body, consV]
      let newLhs := if wrapped then rebuild newLhs else newLhs
      let concl ← mkNewGoal newLhs
      withLocalDeclD hName defEq fun h =>
        mkForallFVars #[v, h] concl
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
    -- oldGoal := (goal at the stepped denotation) (e.denoteOp1 V) rfl, cast back
    let rflPrf ← mkEqRefl tVal
    let contPrf := mkApp2 newGoal tVal rflPrf
    goal.assign (← close contPrf)
    let (_, goal2) ← newGoal.mvarId!.introN 2 [vName, hName]
    return some goal2

/-- Marker hypothesis pinning the stepper's numbering: the value that sits at
valuation depth `depth` is MLIR's `%base`. `nextStepIndex` offsets by it, so
the `v<i>` keep matching the source once the two have drifted apart. -/
structure DenoteNumbering (base depth : Nat) : Prop where
  intro ::

theorem denoteNumbering (base depth : Nat) : DenoteNumbering base depth := ⟨⟩

open Lean Meta in
/-- The number of `HVector.cons`es in an `HVector`, after reduction -- a
block's argument list reaches the goal as `args.reverse`, which is not a
syntactic spine. -/
private partial def hvectorLength (X : Lean.Expr) : MetaM Nat := do
  let X ← whnf X
  if X.isAppOf ``HVector.cons then
    let args := X.getAppArgs
    if args.size ≥ 1 then return (← hvectorLength args[args.size - 1]!) + 1
  return 0

open Lean Meta in
/-- The length of a valuation's `Ctxt.Valuation.cons` spine. Only the
syntactic head is inspected, so a base valuation built with `singleton` /
`ofPair` / an opaque variable contributes `0` — matching MLIR, where the block
arguments are `%arg0…` and do not participate in the `%0, %1, …` numbering.

A tail block's valuation is `ofHVector args.reverse ++ Vamb`: its own block
arguments over the ambient context. Both halves count -- the block arguments
because MLIR numbers them (`^bb10(%33: i32)`), and `Vamb` because it is the
entry block's spine, which is what makes a tail block's `v<i>` continue the
entry block's numbering rather than restarting at `v0`. -/
private partial def valuationDepth (V : Lean.Expr) : MetaM Nat := do
  if V.isAppOf ``Ctxt.Valuation.cons then
    let args := V.getAppArgs
    if args.size ≥ 1 then return (← valuationDepth args[args.size - 1]!) + 1
  if V.isAppOf ``HAppend.hAppend then
    let args := V.getAppArgs
    if args.size ≥ 2 then
      let lhs ← whnfR args[args.size - 2]!
      let hvec ←
        if lhs.isAppOf ``Ctxt.Valuation.ofHVector then
          let a := lhs.getAppArgs
          if a.size ≥ 1 then hvectorLength a[a.size - 1]! else pure 0
        else
          valuationDepth lhs
      return hvec + (← valuationDepth args[args.size - 1]!)
  return 0

open Lean Meta in
/-- The `DenoteNumbering base depth` marker in the local context, if any. -/
private def denoteNumberingMarker : MetaM (Option (Nat × Nat)) := do
  for decl in ← getLCtx do
    let ty ← instantiateMVars decl.type
    if ty.isAppOf ``DenoteNumbering then
      let args := ty.getAppArgs
      if args.size ≥ 2 then
        if let some base := args[args.size - 2]!.nat? then
          if let some depth := args[args.size - 1]!.nat? then
            return some (base, depth)
  return none

open Lean Meta Elab Tactic in
/-- The number of instructions already consumed, i.e. the index to give the
next `v<i>`.

This is read off the *goal*, not off hypothesis names: every step wraps the
valuation in one more `Ctxt.Valuation.cons`, and that spine is part of the
denotation being rewritten, so it survives anything done to the context —
renaming, `clear`ing the `hv<i>`, or `subst`ing a `v<i>` away. The index
therefore always agrees with the `%i` of the MLIR program. -/
def nextStepIndex (goal : MVarId) : MetaM Nat :=
  goal.withContext do
    let tgt ← whnfR (← instantiateMVars (← goal.getType))
    let some (lhs, _) ← findDenoteTerm? tgt | return 0
    -- goals wrap the denotation in `StateT.run … s` and, for a CFG entry
    -- block, a `bind` as well; see `peelWrappers`.
    let (core, _, _) ← peelWrappers lhs
    unless core.isAppOf ``Com.denote || core.isAppOf ``LeanMLIR.SLLVM.BlockCom.denote do
      return 0
    let args := core.getAppArgs
    unless args.size ≥ 1 do return 0
    let depth ← valuationDepth args[args.size - 1]!
    match ← denoteNumberingMarker with
    | some (base, markDepth) => return base + (depth - markDepth)
    | none => return depth



open Lean Meta Elab Tactic in
/-- `denote_number_from 12` says that the *next* instruction the stepper peels
is MLIR's `%12`, and keeps that alignment for everything after it in this
block.

The automatic numbering is the valuation's `cons` depth, which is right within
a block and across the entry block into the first tail block it dominates. It
cannot be right for every block: under depth-1 dominance each tail block starts
from the *entry's* out-context, so `^bb2` sees the same ambient valuation as
`^bb1` and would restart at the same index, while MLIR keeps counting. One
`denote_number_from` per block after the first re-aligns them; the marker is a
hypothesis in the goal's context, so it survives whatever else the proof does
and later `denote_step_all`s in the same block pick it up. -/
elab "denote_number_from" n:num : tactic => do
  let goal ← getMainGoal
  let base := n.getNat
  let depth ← goal.withContext do
    let tgt ← whnfR (← instantiateMVars (← goal.getType))
    let some (lhs, _) ← findDenoteTerm? tgt
      | throwError "denote_number_from: no denotation in the goal"
    let (core, _, _) ← peelWrappers lhs
    let args := core.getAppArgs
    if args.size ≥ 1 then valuationDepth args[args.size - 1]! else pure 0
  -- drop any previous marker, so the tactic is idempotent per block
  let goal ← goal.withContext do
    let mut g := goal
    for decl in ← getLCtx do
      if (← instantiateMVars decl.type).isAppOf ``DenoteNumbering then
        g ← g.tryClear decl.fvarId
    return g
  let ty ← mkAppM ``DenoteNumbering #[mkNatLit base, mkNatLit depth]
  let val ← mkAppM ``denoteNumbering #[mkNatLit base, mkNatLit depth]
  let goal ← goal.assert `_denote_numbering ty val
  let (_, goal) ← goal.intro1P
  replaceMainGoal [goal]

open Lean Meta in
/-- Rewrite the goal's core denotation with the equation `lem`, whose
left-hand side must unify with it (up to default transparency, so an
auxiliary definition standing in for a quoted region is seen through).
Returns the new goal, or `none` if the equation does not apply. -/
private def rewriteCore (goal : MVarId) (lem : Name) : MetaM (Option MVarId) :=
  goal.withContext do
    let tgt ← whnfR (← instantiateMVars (← goal.getType))
    let some (lhs, rhs?) ← findDenoteTerm? tgt | return none
    let (core, rebuild, wrapped) ← peelWrappers lhs
    let lemConst ← mkConstWithFreshMVarLevels lem
    let (mvars, _, concl) ← forallMetaTelescope (← inferType lemConst)
    let some (_, lemLhs, lemRhs) := concl.eq? | return none
    unless ← isDefEq lemLhs core do return none
    let proof := mkAppN lemConst mvars
    let newCore ← instantiateMVars lemRhs
    let newLhs := if wrapped then rebuild newCore else newCore
    let proof ←
      if wrapped then
        let some (ty, _, _) := (← inferType proof).eq? | return none
        let lam ← withLocalDeclD `X ty fun X => mkLambdaFVars #[X] (rebuild X)
        mkCongrArg lam proof
      else
        pure proof
    match rhs? with
    | some rhs =>
      let newGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq newLhs rhs)
      goal.assign (← mkEqTrans proof newGoal)
      return some newGoal.mvarId!
    | none =>
      let abst ← kabstract tgt lhs
      let motive := Lean.Expr.lam `X (← inferType lhs) abst .default
      let newGoal ← mkFreshExprSyntheticOpaqueMVar (abst.instantiate1 newLhs)
      goal.assign (← mkEqMPR (← mkCongrArg motive proof) newGoal)
      return some newGoal.mvarId!

open Lean Meta Elab Tactic in
/-- `denote_reduce_get` reduces a `Blocks.get` lookup in the goal by
weak-head evaluation, so only the looked-up block is materialised -- the
skipped blocks stay folded behind the region's definition. Used directly on
a `Blocks.run_loop` step obligation, which states one block's run;
`denote_enter_block` composes it with `Blocks.run_step`, and
`denote_step_all` takes over from there. -/
elab "denote_reduce_get" : tactic => do
  let goal ← getMainGoal
  let goal ← goal.withContext do
    let tgt ← instantiateMVars (← goal.getType)
    let some getApp := tgt.find? (·.isAppOf ``LeanMLIR.SLLVM.Blocks.get)
      | throwError "denote_reduce_get: no `Blocks.get` in the goal"
    let reduced ← whnf getApp
    let tgt' := tgt.replace fun e => if e == getApp then some reduced else none
    goal.replaceTargetDefEq tgt'
  replaceMainGoal [goal]
  evalTactic (← `(tactic| dsimp only))

open Lean Meta Elab Tactic in
/-- `denote_enter_block` steps a `Blocks.run bs Vamb t` goal into the block
`t` selects: `Blocks.run_step`, then `denote_reduce_get`. -/
elab "denote_enter_block" : tactic => do
  let some g ← rewriteCore (← getMainGoal) ``LeanMLIR.SLLVM.Blocks.run_step
    | throwError "denote_enter_block: the goal is not a `Blocks.run … t`. \
        Resolve the terminator first, so the target is a concrete `SuccArgs`."
  replaceMainGoal [g]
  evalTactic (← `(tactic| denote_reduce_get))

open Lean Meta Elab Tactic in
/-- `denote_step_all v` symbolically executes a pure, single-result-per-op
`Com` denotation: as long as the goal has the shape
`(Com.var e body).denote V = rhs`, it introduces a fresh variable `v<i>` with
defining hypothesis `hv<i> : v<i> = e.denoteOp1 V` and changes the goal to
`body.denote (v<i> ::ᵥ V) = rhs` (via `Com.denote_var_pure_single`). Sharing
between use sites is preserved — every use of an intermediate value is just a
variable — and each `hv<i>` can be simplified in isolation.

This is pure term surgery (no `rw`), so each step is cheap even when the
remaining program is large.

A CFG block (`BlockCom`) steps the same way, through
`BlockCom.denote_var_pureOp_single`. Three things to know about that path:

- Open a `Cfg` goal with `simp only [Cfg.denote]` first. That splits it into
  the entry block and the dispatch on its terminator; the entry block is what
  steps, and the tactic says so rather than silently doing nothing if the goal
  is still a whole `Cfg.denote`.
- Stepping stops at the first genuinely impure instruction -- a load or a
  store has no `Expr.HasPureOp` proof, and its value is not determined by the
  valuation alone. That is the boundary where the proof has to supply, say, a
  `Fits` hypothesis, so `denote_step_all v` on its own runs the block up to
  (not through) its first memory access.
- Numbering follows the valuation's `cons` depth, counting through the
  `ofHVector args.reverse ++ Vamb` a tail block starts from. That keeps the
  `v<i>` on MLIR's `%i` within a block, and across the entry block into the
  first tail block it dominates. It cannot hold for every block: depth-1
  dominance means each tail block starts from the *entry's* out-context, so
  `^bb2` sees what `^bb1` saw and would reuse its indices while MLIR keeps
  counting. Put one `denote_number_from` at the top of each block after the
  first to re-align.

`denote_step_all v n` runs *to* instruction `%n` of the MLIR program, like a
debugger's "run to line": it stops once `v<n>` exists, leaving `v0 … v<n>` in
context and the goal positioned at `%(n+1)`. The argument is an absolute
instruction number, not a number of steps — `denote_step_all v 31` always
means "up to and including `%31`", however many steps that takes from here.

Numbering is per-program, so it composes: `denote_step_all v 3` followed by
`denote_step_all v 5` introduces `v0 … v3` and then `v4 v5`, exactly as a
single `denote_step_all v 5` would. The continuation point is `nextStepIndex`,
which reads the instruction count off the goal, so `v<i>` names the program's
`%i` no matter what happened to the context in between — the `hv<i>` may be
`clear`ed, the `v<i>` `subst`ed away or renamed. -/
elab "denote_step_all" base:ident target:(num)? : tactic => do
  let baseName := base.getId
  let start ← nextStepIndex (← getMainGoal)
  match target with
  | none =>
    let mut i := start
    for _ in [0:1000] do
      let some goal2 ← denoteStep1 (← getMainGoal) baseName i | break
      replaceMainGoal [goal2]
      i := i + 1
  | some n =>
    let target := n.getNat
    if start > target then
      throwError "denote_step_all: already positioned at %{start}, which is \
        past the requested %{target}"
    for i in [start:target + 1] do
      let some goal2 ← denoteStep1 (← getMainGoal) baseName i
        | throwError "denote_step_all: the program has no instruction %{i}, \
            so it cannot be stepped to %{target}"
      replaceMainGoal [goal2]

/-! ### Working with a range of stepped instructions

`denote_step_all` leaves one `hv<i>` per instruction, which is what keeps each
of them small, but it means referring to a stretch of the program spells out
every name. The two tactics below take an inclusive index range instead.
-/

open Lean Meta Elab Tactic in
/-- The hypotheses `h<base><lo> … h<base><hi>` that actually exist in the main
goal's context, ascending. Indices with no hypothesis are skipped rather than
being an error, so a range may freely span `v<i>`s that have been `subst`ed
away or whose `hv<i>` has been `clear`ed. -/
private def denoteHyps (base : Name) (lo hi : Nat) : TacticM (Array Ident) := do
  (← getMainGoal).withContext do
    let lctx ← getLCtx
    let mut hyps : Array Ident := #[]
    for i in [lo:hi + 1] do
      let n := Name.mkSimple ("h" ++ base.toString ++ toString i)
      if (lctx.findFromUserName? n).isSome then
        hyps := hyps.push (mkIdent n)
    if hyps.isEmpty then
      throwError "no `h{base}<i>` hypothesis with {lo} ≤ i ≤ {hi}"
    return hyps

open Lean Elab Tactic in
/-- `denote_eval v 4 27` evaluates the stepping hypotheses `hv4 … hv27` in
place, turning each `hv<i> : v<i> = (Expr.mk …).denoteOp1 V` into the dialect
value it denotes, e.g. `hv13 : v13 = LLVM.Ty.insertelement v11 v10 v12`.

Each hypothesis is evaluated *on its own*, which is the cheap direction:
inlining a chain of instructions first and evaluating the result afterwards
does not scale. -/
elab "denote_eval " base:ident lo:num hi:num : tactic => do
  let hyps ← denoteHyps base.getId lo.getNat hi.getNat
  evalTactic (← `(tactic| simp only [Expr.denoteOp1, Expr.denoteOpPure] at $hyps*))
  evalTactic (← `(tactic| simp_peephole at $hyps*))
  evalTactic (← `(tactic| simp only [HVector.head] at $hyps*))

open Lean Elab Tactic in
/-- `denote_expand v 4 27` rewrites the goal with `hv27, hv26, …, hv4` —
descending, so a chain collapses in one pass from its last instruction down to
its inputs. The range is written ascending, as for `denote_eval`; run that
first, or the goal fills up with unevaluated `denoteOp1`s. -/
elab "denote_expand " base:ident lo:num hi:num : tactic => do
  let hyps := (← denoteHyps base.getId lo.getNat hi.getNat).reverse
  evalTactic (← `(tactic| simp only [$[$hyps:ident],*]))

open Lean Elab Tactic in
/-- `denote_step v 12` runs to instruction `%12` like `denote_step_all`, but
peels back only the *last* one: `%12` gets `v12`/`hv12`, and everything before it
is inlined straight into the valuation spine. The context therefore never
accumulates `hv<i>` for instructions already dealt with, and no `subst` is needed
to retire them.

The trade is term size: an inlined instruction sits in the spine as an
unevaluated `Expr.denoteOp1`, and `hv<n>` is stated over that spine. Cheap for a
run of constants or a short chain, but see `denote_eval` -- evaluating each
instruction on its own is the direction that scales. -/
elab "denote_step " base:ident target:num : tactic => do
  let baseName := base.getId
  let start ← nextStepIndex (← getMainGoal)
  let target := target.getNat
  if start > target then
    throwError "denote_step: already positioned at %{start}, which is past the \
      requested %{target}"
  for i in [start:target] do
    let some g ← denoteStep1 (← getMainGoal) baseName i (inline := true)
      | throwError "denote_step: the program has no instruction %{i}"
    replaceMainGoal [g]
  let some g ← denoteStep1 (← getMainGoal) baseName target
    | throwError "denote_step: the program has no instruction %{target}"
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- `denote_clear v 4 27` retires `hv4 … hv27` and `v4 … v27`, for stretches of
the program that have been dealt with and are only making the context long.

Each is `clear`ed if possible. A `v<i>` usually is not: until it is `subst`ed
away it still occurs in the goal's valuation spine, which is a real dependency.
Those are **hidden** instead — marked as implementation details, which the goal
display filters out. That changes nothing about the goal, so the spine is
untouched and `denote_step_all` numbering is unaffected.

Indices with nothing in the context are skipped, as for `denote_eval`; an
entirely empty range is an error.

A hidden hypothesis is still in scope and can still be used by name
(`exact hv11` works). What it is invisible to is automation that scans the
context — `simp at *`, `assumption`, `omega`. That is harmless for a `v<i>`,
which carries no information once its `hv<i>` is gone. -/
elab "denote_clear " base:ident lo:num hi:num : tactic => do
  let baseName := base.getId
  let lo := lo.getNat
  let hi := hi.getNat
  let goal ← getMainGoal
  let fvars ← goal.withContext do
    let lctx ← getLCtx
    let mut fvars : Array FVarId := #[]
    -- `hv<i>` mentions `v<i>`, so it has to be cleared first.
    for name in [("h" ++ baseName.toString), baseName.toString] do
      for i in [lo:hi + 1] do
        if let some d := lctx.findFromUserName? (Name.mkSimple (name ++ toString i)) then
          fvars := fvars.push d.fvarId
    return fvars
  if fvars.isEmpty then
    throwError "no `{baseName}<i>` or `h{baseName}<i>` hypothesis with \
      {lo} ≤ i ≤ {hi}"
  -- NOTE: not `tryClearMany`, which iterates its argument in *reverse* and so
  -- would try each `v<i>` while its `hv<i>` still depends on it, silently
  -- leaving every value behind.
  let mut goal := goal
  for fvar in fvars do
    goal ← goal.tryClear fvar
  -- Whatever survived the clear is depended upon; hide it instead.
  let survivors ← goal.withContext do
    let lctx ← getLCtx
    return fvars.filter fun f => (lctx.find? f).isSome
  if survivors.isEmpty then
    replaceMainGoal [goal]
  else
    goal.withContext do
      let mut lctx ← getLCtx
      for f in survivors do
        lctx := lctx.setKind f .implDetail
      let newGoal ← mkFreshExprMVarAt lctx (← getLocalInstances) (← goal.getType)
                      .syntheticOpaque (← goal.getTag)
      goal.assign newGoal
      replaceMainGoal [newGoal.mvarId!]


/-! ### Stepping and reducing in one go

`denote_step_all` leaves the stepped instructions as `denoteOp1` applications;
`denote_eval` evaluates them; a `simp` usually follows. The two tactics below
run that sequence over an index range, so a stretch of the program is one line.
-/

syntax reduceArgs := " [" term,* "]"

open Lean Elab Tactic in
/-- `simp` over `hyps` with `args`, `only` deciding which of the two it is. -/
private def simpHyps (only : Bool) (args : Array Term) (hyps : Array Ident) : TacticM Unit := do
  match only, args.isEmpty with
  | true,  true  => evalTactic (← `(tactic| simp only [] at $hyps*))
  | true,  false => evalTactic (← `(tactic| simp only [$[$args:term],*] at $hyps*))
  | false, true  => evalTactic (← `(tactic| simp at $hyps*))
  | false, false => evalTactic (← `(tactic| simp [$[$args:term],*] at $hyps*))

open Lean Elab Tactic in
/-- `denote_eval base lo hi`, a `simp` over the same hypotheses, and -- with
`fold` -- one more ascending pass that rewrites each of them into the ones
after it: the shared body of `reduce_hv` and `denote_step_reduce`. -/
private def reduceHypsAt (base : Ident) (lo hi : Nat) (only : Bool) (args : Array Term)
    (fold : Bool) : TacticM Unit := do
  let loStx := Syntax.mkNumLit (toString lo)
  let hiStx := Syntax.mkNumLit (toString hi)
  evalTactic (← `(tactic| denote_eval $base $loStx:num $hiStx:num))
  let hyps ← denoteHyps base.getId lo hi
  simpHyps only args hyps
  if fold then
    -- ascending, so `hv<i>` is already folded by the time it is used: each
    -- hypothesis is rewritten by every earlier one at once, which keeps a
    -- fan-out (`%5` reading both `%3` and `%4`) as cheap as a chain.
    for j in [1 : hyps.size] do
      let prev : Array Term := (hyps.extract 0 j).map fun h => (h : Term)
      -- a hypothesis mentioning none of its predecessors makes no progress,
      -- which is `simp`'s error and not a failure of the fold
      try simpHyps only (args ++ prev) #[hyps[j]!] catch _ => pure ()

open Lean Elab in
/-- The lemma list of `reduce_hv`, read off the syntax. -/
private def reduceArgTerms (extra : Option (TSyntax ``reduceArgs)) : Array Term :=
  match extra with
  | some e => e.raw[1].getSepArgs.map fun s => ⟨s⟩
  | none => #[]

open Lean Elab Tactic in
/-- `reduce_hv v 0 5 only [foo, bar]` is `denote_eval v 0 5` followed by
`simp only [foo, bar] at hv0 … hv5`: the stepping hypotheses of an index range
are evaluated to their dialect semantics and then simplified in place, without
either half spelling the names out. Without `only` the second half is the full
`simp`, and with no bracket the lemma list is empty -- `reduce_hv v 0 5` is
`denote_eval` plus plain `simp at hv0 …`.

Indices with no hypothesis are skipped, as for `denote_eval`, so a range may
span `v<i>`s already `subst`ed away. Beyond that the semantics are `simp`'s,
failure to make progress at a location included.

`reduce_hv v 0 5 only [foo] fold` adds a second, ascending pass that rewrites
each hypothesis into *every* later one -- `hv0` into `hv1 … hv5`, then the
folded `hv1` into `hv2 … hv5`, and so on -- so the last hypothesis of the range
is stated over the values that entered it rather than over the `v<i>` before it.
A fan-out costs no more than a chain, and a hypothesis mentioning none of its
predecessors is left alone rather than being an error. -/
elab "reduce_hv " base:ident lo:num hi:num only:(&" only")? extra:(reduceArgs)?
    fold:(&" fold")? : tactic => do
  reduceHypsAt base lo.getNat hi.getNat only.isSome (reduceArgTerms extra) fold.isSome

open Lean Meta Elab Tactic in
/-- `denote_step_reduce v 5 only [foo]` runs the block to `%5` and reduces what
that introduced: `denote_step_all v 5` followed by `reduce_hv` over exactly the
new hypotheses. The range's lower end is where the walk already stood, read off
the goal by `nextStepIndex`, so a stretch of the program is one line rather than
three and the index never has to be repeated.

The `only`/bracket clauses are `reduce_hv`'s. -/
elab "denote_step_reduce " base:ident target:num only:(&" only")? extra:(reduceArgs)?
    fold:(&" fold")? : tactic => do
  let lo ← nextStepIndex (← getMainGoal)
  evalTactic (← `(tactic| denote_step_all $base $target))
  reduceHypsAt base lo target.getNat only.isSome (reduceArgTerms extra) fold.isSome
