/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect.Basic
import SSA.Projects.SLLVM.Dialect.Semantics.MemoryLemmas

/-!
# Stepping an impure `Com` in run form

A program whose memory operations sit in the *middle* -- allocas, then
arithmetic, then a call, then loads, as `fd_r43x6_ge_is_eq` is shaped --
cannot be derived at the `denote` level alone: the values its loads produce
exist only once a concrete state is threaded through. The derivation for such
a program works on `(com.denote V).run s` throughout, and this file holds the
steps of that form.

`run_denote_var_single`/`run_denote_var_zero` peel one impure instruction off
the front, given what its operation does to the state. The `denoteOp_*`
lemmas supply exactly that for the operations whose effect is an honest state
change -- `alloca`, `load`, `lifetime` -- in the same shape `denoteOp_call`
gives it for calls; `run_alloca` and the `getThe`/`modifyThe` lemmas then
evaluate the effects on a concrete state.
-/

namespace LeanMLIR.SLLVM

open LeanMLIR
open InstCombine (LLVM)

-- v4.34: `SLLVM` is semireducible, so `SLLVM.Op`/`SLLVM.m` no longer reduce when applications
-- are type-checked at `implicit` transparency.
-- TODO: belongs unscoped on the `def` in `SSA/Projects/SLLVM/Dialect/Basic.lean`.

/-! ## Effects on a concrete state -/

-- v4.34: a `do`-block now exposes `MonadState.get` where it used to expose `getThe`.
@[simp, simp_denote, simp_sllvm]
theorem run_get_state (s : GlobalState) :
    StateT.run
        (@get GlobalState EffectM
          (@instMonadStateOfMonadStateOf _ _ EffectM.instMonadStateOfGlobalState))
        s =
      .value (s, s) :=
  rfl

@[simp, simp_denote, simp_sllvm]
theorem run_getThe_state (s : GlobalState) :
    StateT.run (getThe GlobalState : EffectM GlobalState) s = .value (s, s) :=
  rfl

@[simp, simp_denote, simp_sllvm]
theorem run_getThe_alloc (s : GlobalState) :
    StateT.run (getThe AllocState : EffectM AllocState) s = .value (s.alloc, s) :=
  rfl

@[simp, simp_denote, simp_sllvm]
theorem run_modifyThe_mem (f : MemoryState → MemoryState) (s : GlobalState) :
    StateT.run (modifyThe MemoryState f : EffectM PUnit) s =
      .value (⟨⟩, { s with mem := f s.mem }) :=
  rfl

@[simp, simp_denote, simp_sllvm]
theorem run_modifyThe_alloc (f : AllocState → AllocState) (s : GlobalState) :
    StateT.run (modifyThe AllocState f : EffectM PUnit) s =
      .value (⟨⟩, { s with alloc := f s.alloc }) :=
  rfl

@[simp, simp_denote, simp_sllvm]
theorem run_modifyThe_state (f : GlobalState → GlobalState) (s : GlobalState) :
    StateT.run (modifyThe GlobalState f : EffectM PUnit) s = .value (⟨⟩, f s) :=
  rfl

/-- A function whose body runs to `(r, s')` returns `r` in `s'` with the frame
killed and the entry counter restored. -/
theorem run_runFunction {α : Type} {body : EffectM α} {s s' : GlobalState} {r : α}
    (h : StateT.run body s = .value (r, s')) :
    StateT.run (runFunction body) s = .value (r, s.popFrame s'.mem) := by
  simp only [runFunction, EffectM.run_bind, run_getThe_state, PoisonOr.value_bind, h,
    run_modifyThe_mem, run_modifyThe_alloc, run_modifyThe_state, EffectM.run_pure]
  rfl

/-- What `alloca` does to a state: the pointer to a fresh zeroed block at the
counter, the counter advanced past it. -/
theorem run_alloca (w : Nat) (s : GlobalState) :
    StateT.run (SLLVM.alloca w) s =
      .value (PoisonOr.value ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩, s.afterAlloca w) := by
  rfl

/-- What `addressof` does to a state: nothing but read the symbol table. The
hypothesis is the whole content of a global here -- an entry has to be there,
or the operation is UB. -/
theorem run_addressof {name : String} {s : GlobalState} {p : Pointer}
    (h : s.globals[name]? = some p) :
    StateT.run (SLLVM.addressof name) s = .value (PoisonOr.value p, s) := by
  simp [SLLVM.addressof, h]

/-! ## The operations, in `denoteOp` form

Stated over `Expr.mk` exactly as `denoteOp_call` is, so that they rewrite the
expressions a parsed program carries. -/

@[simp_denote]
theorem denoteOp_alloca {Γ : Ctxt SLLVM.Ty} (w : Nat) (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure) (SLLVMOp.alloca w) rfl
          (EffectKind.le_refl _) HVector.nil Regions.nil)
        V =
      (([·]ₕ) <$> SLLVM.alloca w : EffectM _) := by
  rfl

@[simp_denote]
theorem denoteOp_addressof {Γ : Ctxt SLLVM.Ty} (name : String) (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure) (SLLVMOp.addressof name) rfl
          (EffectKind.le_refl _) HVector.nil Regions.nil)
        V =
      (([·]ₕ) <$> SLLVM.addressof name : EffectM _) := by
  rfl

@[simp_denote]
theorem denoteOp_lifetime {Γ : Ctxt SLLVM.Ty} (start : Bool) (p : Ctxt.Var Γ .ptr)
    (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure) (SLLVMOp.lifetime start) rfl
          (EffectKind.le_refl _) (p::ₕ.nil) Regions.nil)
        V =
      (pure []ₕ : EffectM _) := by
  rfl

@[simp_denote]
theorem denoteOp_load {Γ : Ctxt SLLVM.Ty} (t : LLVM.Ty) (p : Ctxt.Var Γ .ptr)
    (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
        (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure) (SLLVMOp.load t) rfl (EffectKind.le_refl _)
          (p::ₕ.nil) Regions.nil)
        V =
      (([·]ₕ) <$> (liftM (SLLVM.load (V p) t)) :
        EffectM (HVector TyDenote.toType [SLLVM.Ty.arith t])) := by
  rfl

/-- v4.34: a one-element `HVector` prepended to a valuation is a `cons`. The step lemmas
below used to get this by `rfl` through `Ctxt.Valuation.ofHVector`. -/
theorem valuation_appendHVector_singleton {Γ : Ctxt SLLVM.Ty} {t : SLLVM.Ty} (x : TyDenote.toType t)
    (V : Ctxt.Valuation Γ) : ((x::ₕHVector.nil) ++ V : Ctxt.Valuation _) = x::ᵥV := by
  show Ctxt.Valuation.ofHVector (x::ₕ.nil) ++ V = x::ᵥV
  simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil]
  -- v4.34: `cons_append`'s `no_index` LHS no longer matches under `simp`.
  exact Ctxt.Valuation.cons_append.trans (congrArg _ Ctxt.Valuation.nil_append)

/-! ## Peeling one impure instruction -/

/-- Step a single-result impure instruction: given what its operation does to
the state, the program continues on the result and the new state. -/
theorem run_denote_var_single {Γ : Ctxt SLLVM.Ty} {t : SLLVM.Ty} {ts : List SLLVM.Ty}
    {e : Expr SLLVM Γ .impure [t]} {body : Com SLLVM e.outContext .impure ts} {V : Ctxt.Valuation Γ}
    {s s' : GlobalState} {x : TyDenote.toType t}
    (h : StateT.run (e.denoteOp V) s = .value ([x]ₕ, s')) :
    StateT.run ((Com.var e body).denote V) s = StateT.run (body.denote (x::ᵥV)) s' := by
  rw [Com.denote_var]
  show StateT.run (e.denote V >>= body.denote) s = _
  rw [Expr.denote_unfold]
  simp only [EffectM.run_bind, EffectM.run_map, h, PoisonOr.map_value, PoisonOr.value_bind]
  rw [valuation_appendHVector_singleton]

/-- Step a zero-result impure instruction (a store, a lifetime marker, a void
call): the state advances and the valuation is untouched. -/
theorem run_denote_var_zero {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} {e : Expr SLLVM Γ .impure []}
    {body : Com SLLVM e.outContext .impure ts} {V : Ctxt.Valuation Γ} {s s' : GlobalState}
    (h : StateT.run (e.denoteOp V) s = .value (HVector.nil, s')) :
    StateT.run ((Com.var e body).denote V) s = StateT.run (body.denote V) s' := by
  rw [Com.denote_var]
  show StateT.run (e.denote V >>= body.denote) s = _
  rw [Expr.denote_unfold]
  simp only [EffectM.run_bind, EffectM.run_map, h, PoisonOr.map_value, PoisonOr.value_bind]
  congr 2

/-! ## The steps, closed per operation

`run_denote_var_single`'s side condition mentions the result and the new
state; at a use site those are still metavariables, which `simp` will not work
under. These instances close the side condition once, with everything spelled
out, so that stepping one `alloca`, `lifetime` or `load` is a single `rw`. -/

/-- Step an `alloca`: the fresh pointer enters the valuation, the counter
advances, and a zeroed block appears. -/
theorem run_var_alloca {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} {w : Nat}
    {body : Com SLLVM (([SLLVM.Ty.ptr] : List SLLVM.Ty) ++ Γ) .impure ts} (V : Ctxt.Valuation Γ)
    (s : GlobalState) :
    StateT.run
        ((Com.var
              (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure) (SLLVMOp.alloca w) rfl
                (EffectKind.le_refl _) HVector.nil Regions.nil)
              body).denote
          V)
        s =
      StateT.run (body.denote (PoisonOr.value ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩::ᵥV))
        (s.afterAlloca w) :=
  run_denote_var_single
    (by
      simp only [denoteOp_alloca, EffectM.run_map]
      rw [run_alloca]
      rfl)

/-- Step a lifetime marker: nothing happens. -/
theorem run_var_lifetime {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} {start : Bool}
    {p : Ctxt.Var Γ .ptr} {body : Com SLLVM Γ .impure ts} (V : Ctxt.Valuation Γ) (s : GlobalState) :
    StateT.run
        ((Com.var
              (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure) (SLLVMOp.lifetime start) rfl
                (EffectKind.le_refl _) (p::ₕ.nil) Regions.nil)
              body).denote
          V)
        s =
      StateT.run (body.denote V) s :=
  run_denote_var_zero (by simp only [denoteOp_lifetime, EffectM.run_pure])

/-- Step a `load`, given what the memory at the pointer holds. A load leaves
the state alone, so the hypothesis returns into the same memory. -/
theorem run_var_load {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} {t : LLVM.Ty} {p : Ctxt.Var Γ .ptr}
    {body : Com SLLVM (([SLLVM.Ty.arith t] : List SLLVM.Ty) ++ Γ) .impure ts} {V : Ctxt.Valuation Γ}
    {s : GlobalState} {x : TyDenote.toType t}
    (h : StateT.run (SLLVM.load (V p) t) s.mem = .value (x, s.mem)) :
    StateT.run
        ((Com.var
              (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure) (SLLVMOp.load t) rfl
                (EffectKind.le_refl _) (p::ₕ.nil) Regions.nil)
              body).denote
          V)
        s =
      StateT.run (body.denote (x::ᵥV)) s := by
  refine run_denote_var_single ?_
  simp only [denoteOp_load, EffectM.run_map, SLLVM.run_liftM h, PoisonOr.map_value]

end LeanMLIR.SLLVM
