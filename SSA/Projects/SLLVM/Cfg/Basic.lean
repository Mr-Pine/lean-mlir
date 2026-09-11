/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# A CFG for SLLVM

`Com` is a straight-line let-chain; this module adds the control flow the
Firedancer ref extraction needs: a region of basic blocks. A block's body has
exactly `Com`'s cons shape, but ends in a `Terminator` (return / br /
cond_br / switch) instead of `Com.rets`. A branch names a `Target`: which
block to enter, plus the values passed to its block arguments -- MLIR's φ
nodes.

A `Target` may name *any* block -- back-edges included -- so the region is
lifted verbatim, block order and loop φs intact. The price is that the
interpreter is no longer structural in the block list. It is factored as:

- `BlockCom.eval` / `Blocks.iterate`: a **fueled**, computable interpreter.
  Fuel is spent once per block transition; `none` means "still running".
- `Blocks.run` / `BlockCom.denote` / `Cfg.denote`: the semantics proper,
  taking the limit over fuel (`Fuel.limit`, classical). A computation with
  no limit -- a genuinely non-terminating loop -- denotes UB.

**Nontermination is UB** is a deliberate semantics decision (LIMITATIONS
5.1): the artifacts' loop latches carry `mustProgress = true` (C's
forward-progress guarantee), so LLVM is already licensed to assume they
terminate. `#guard`-style testing goes through `Cfg.eval`, the fueled
top-level interpreter; the agreement theorem lives in `Cfg/Eval.lean`.

One remaining restriction: **depth-1 dominance**. A non-entry block sees the
entry block's definitions (`Γamb`) and its own arguments -- not other blocks'
definitions. The lifter (`threadLive` in `Cfg/Transform.lean`) brings a general
SSA region into this shape by passing such values as extra block arguments.

Block arguments enter contexts in reverse declaration order
(`Ctxt.ofList argTys.reverse`), the same load-bearing convention as `call`
regions (see `Dialect/Basic.lean`).

Branching on a poison condition or switch scrutinee is UB, as in LLVM.
-/

namespace LeanMLIR.SLLVM

/-- A branch target: an index into the region's block list (`all` lists every
non-entry block's argument signature), plus the argument variables the branch
passes. Shaped like `Ctxt.Var`: the target's signature `ts` comes out of the
lookup proof, so no `getElem` cast arises downstream. -/
structure Target (Γ : Ctxt SLLVM.Ty) (all : List (List SLLVM.Ty)) where
  {ts : List SLLVM.Ty}
  idx : Nat
  hidx : all[idx]? = some ts
  args : HVector Γ.Var ts

/-- `Target`'s value level: the chosen block index together with the argument
*values* passed to it. -/
structure SuccArgs (all : List (List SLLVM.Ty)) where
  {ts : List SLLVM.Ty}
  idx : Nat
  hidx : all[idx]? = some ts
  args : HVector toType ts

/-- There is nowhere to branch to in an empty block list. -/
def SuccArgs.elim {α : Sort _} (t : SuccArgs []) : α :=
  absurd t.hidx (by simp)

/-- How a block ends: return from the region, or transfer control to another
block. -/
inductive Terminator (Γ : Ctxt SLLVM.Ty) (rets : List SLLVM.Ty)
    (succs : List (List SLLVM.Ty)) : Type
  | ret (vs : HVector Γ.Var rets)
  | br (t : Target Γ succs)
  | condBr (c : Γ.Var (Ty.bitvec 1)) (tTrue tFalse : Target Γ succs)
  | switch {w : Nat} (v : Γ.Var (Ty.bitvec w)) (dflt : Target Γ succs)
      (cases : List (BitVec w × Target Γ succs))

mutual

/-- A block body: `Com`'s cons shape with `rets` generalised to a
`Terminator`. `Γout` (the context after all lets) is exposed in the type so
the entry block's definitions can become the tail blocks' ambient context.
The effect is fixed `.impure`; pure operations inside impure code are already
the norm (see `Com.denote_var_pureOp`).

`call` is the CFG layer's function call: the framework's `Regions` slot can
only carry a `Com`, so a callee that is itself a CFG travels here instead, as
an inlined entry + tail blocks over its argument context. A straight-line
callee is the one-block case (`cblocks = .nil`). `callee` is the symbol name,
for printing only. -/
inductive BlockCom : (Γ Γout : Ctxt SLLVM.Ty) → (rets : List SLLVM.Ty) →
    (succs : List (List SLLVM.Ty)) → Type
  | term (t : Terminator Γ rets succs) : BlockCom Γ Γ rets succs
  | var (e : Expr SLLVM Γ .impure tys) (body : BlockCom (tys ++ Γ) Γout rets succs) :
      BlockCom Γ Γout rets succs
  | call {Γ Γout : Ctxt SLLVM.Ty} {rets succs} {argTys retTys : List SLLVM.Ty}
      {csigs : List (List SLLVM.Ty)} {cΓout : Ctxt SLLVM.Ty}
      (callee : String)
      (centry : BlockCom (Ctxt.ofList argTys.reverse) cΓout retTys csigs)
      (cblocks : Blocks cΓout retTys csigs csigs)
      (args : HVector Γ.Var argTys)
      (body : BlockCom (retTys ++ Γ) Γout rets succs) :
      BlockCom Γ Γout rets succs

/-- The non-entry blocks, in source order. `remaining` indexes the blocks
from here on (the structural recursion); `all` is every block's signature,
fixed for the whole region (what branch targets name). Block `k` sees the
ambient context `Γamb` plus its own arguments, and its terminator may target
any block -- back-edges included. -/
inductive Blocks : (Γamb : Ctxt SLLVM.Ty) → (rets : List SLLVM.Ty) →
    (remaining all : List (List SLLVM.Ty)) → Type
  | nil : Blocks Γamb rets [] all
  | cons {Γamb : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty}
      {argTys : List SLLVM.Ty} {remaining all : List (List SLLVM.Ty)}
      {Γout : Ctxt SLLVM.Ty}
      (b : BlockCom (Ctxt.ofList argTys.reverse ++ Γamb) Γout rets all)
      (bs : Blocks Γamb rets remaining all) :
      Blocks Γamb rets (argTys :: remaining) all

end

/-- A CFG: an entry block over the region arguments `Γin`, then the remaining
blocks with the entry's out-context as their ambient context. The tail
blocks' `remaining` and `all` indices coincide: the list is the whole region. -/
structure Cfg (Γin : Ctxt SLLVM.Ty) (rets : List SLLVM.Ty) where
  {sigs : List (List SLLVM.Ty)}
  {Γout : Ctxt SLLVM.Ty}
  entry : BlockCom Γin Γout rets sigs
  blocks : Blocks Γout rets sigs sigs

/-- Look up block `i`: total, because the caller's `remaining[i]? = some ts`
guarantees the index is in range and pins the block's signature. -/
def Blocks.get {Γamb : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty}
    {all : List (List SLLVM.Ty)} :
    {remaining : List (List SLLVM.Ty)} → Blocks Γamb rets remaining all →
    (i : Nat) → {ts : List SLLVM.Ty} → remaining[i]? = some ts →
    Σ Γout, BlockCom (Ctxt.ofList ts.reverse ++ Γamb) Γout rets all
  | _, .nil, _, _, h => absurd h (by simp)
  | _, .cons (Γout := Γout) b _, 0, _, h =>
      ⟨Γout, (by simpa using h : _ = _) ▸ b⟩
  | _, .cons _ bs, i + 1, _, h => bs.get i (by simpa using h)

/-! ### Denotation -/

/-- `Target`'s value level: look the argument variables up in the valuation. -/
def Target.denote (V : Γ.Valuation) (t : Target Γ all) : SuccArgs all :=
  ⟨t.idx, t.hidx, t.args.map V⟩

/-- Either the region's results (a `ret` ran) or the target the block
branched to. Branching on poison is UB. -/
def Terminator.denote : Terminator Γ rets succs → Γ.Valuation →
    EffectM (HVector toType rets ⊕ SuccArgs succs)
  | .ret vs, V => return .inl (vs.map V)
  | .br t, V => return .inr (t.denote V)
  | .condBr c tTrue tFalse, V =>
      match V c with
      | .poison => throwUB
      | .value b => return .inr ((if b = 1 then tTrue else tFalse).denote V)
  | .switch v dflt cases, V =>
      match V v with
      | .poison => throwUB
      | .value x =>
          return .inr ((((cases.find? (·.1 == x)).map (·.2)).getD dflt).denote V)

/-! ### The fueled interpreter

Computable and total: fuel is spent once per block transition, `none` means
"still running". A body's own instructions are free -- a block is finite --
so fuel measures exactly the thing that can be unbounded. Termination of the
definition itself is lexicographic on (fuel, term): a transition strictly
decreases fuel, everything else strictly decreases the term.
-/

/-- Sequence a fueled stage into a continuation: still-running (`none`) and
UB (`some .poison`) pass through. Everything below has this shape, so the
monotonicity and limit lemmas (`Cfg/Eval.lean`) each need to be stated once. -/
def Fuel.andThen : Option (PoisonOr α) → (α → Option (PoisonOr β)) → Option (PoisonOr β)
  | none, _ => none
  | some .poison, _ => some .poison
  | some (.value a), k => k a

@[simp] theorem Fuel.andThen_none {k : α → Option (PoisonOr β)} :
    Fuel.andThen none k = none := rfl
@[simp] theorem Fuel.andThen_poison {k : α → Option (PoisonOr β)} :
    Fuel.andThen (some .poison) k = some .poison := rfl
@[simp] theorem Fuel.andThen_value {a : α} {k : α → Option (PoisonOr β)} :
    Fuel.andThen (some (.value a)) k = k a := rfl

/-- Read a completed fueled result; "still running" at every fuel is UB. -/
def Fuel.force : Option (PoisonOr α) → PoisonOr α
  | some r => r
  | none => .poison

@[simp] theorem Fuel.force_some {r : PoisonOr α} : Fuel.force (some r) = r := rfl
@[simp] theorem Fuel.force_none : Fuel.force (none : Option (PoisonOr α)) = .poison := rfl

mutual

/-- Run a block body to its terminator. `none` = a callee ran out of fuel. -/
def BlockCom.eval (fuel : Nat) :
    {Γ Γout : Ctxt SLLVM.Ty} → {rets : List SLLVM.Ty} →
    {all : List (List SLLVM.Ty)} →
    BlockCom Γ Γout rets all → Γ.Valuation → GlobalState →
    Option (PoisonOr ((Γout.Valuation × (HVector toType rets ⊕ SuccArgs all)) × GlobalState))
  | _, _, _, _, .term t, V, s =>
      some (StateT.run (do return (V, ← t.denote V)) s)
  | _, _, _, _, .var e body, V, s =>
      Fuel.andThen (some (StateT.run (e.denote V) s)) fun (V', s') =>
        body.eval fuel V' s'
  | _, _, _, _, .call _ centry cblocks args body, V, s =>
      -- `runFunction`, fueled: run the callee from `s`, then kill its frame
      -- and restore the allocation counter (`MemorySemantics.runFunction`).
      Fuel.andThen
        (Fuel.andThen
          (centry.eval fuel (Ctxt.Valuation.ofHVector (args.map V).reverse) s)
          fun p => cblocks.next fuel p.1.1 p.1.2 p.2)
        fun p => body.eval fuel (p.1 ++ V) (s.popFrame p.2.mem)
termination_by _ _ _ _ c _ _ => (fuel, sizeOf c, 0)

/-- Walk the region: enter the targeted block with its arguments bound
(reverse order, as always), run it, and continue with whatever its terminator
produced -- one unit of fuel per transition. -/
def Blocks.iterate :
    (fuel : Nat) → {Γamb : Ctxt SLLVM.Ty} → {rets : List SLLVM.Ty} →
    {all : List (List SLLVM.Ty)} →
    Blocks Γamb rets all all → Γamb.Valuation → SuccArgs all → GlobalState →
    Option (PoisonOr (HVector toType rets × GlobalState))
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, _, _, _, bs, Vamb, t, s =>
      Fuel.andThen
        ((bs.get t.idx t.hidx).2.eval fuel
          (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb) s)
        fun p => bs.next fuel Vamb p.1.2 p.2
termination_by fuel _ _ _ bs _ _ _ => (fuel, sizeOf bs, 0)

/-- Dispatch on a block's outcome: the region's results, or continue walking
from the branched-to block. A *named* continuation, so the agreement lemmas
(`Cfg/Eval.lean`) rewrite it syntactically. -/
def Blocks.next {Γamb : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty}
    {all : List (List SLLVM.Ty)}
    (bs : Blocks Γamb rets all all) (fuel : Nat) (Vamb : Γamb.Valuation) :
    (HVector toType rets ⊕ SuccArgs all) → GlobalState →
    Option (PoisonOr (HVector toType rets × GlobalState))
  | .inl rets, s => some (.value (rets, s))
  | .inr t, s => bs.iterate fuel Vamb t s
termination_by _ _ => (fuel, sizeOf bs, 1)

end

/-- The fueled interpreter for a whole region: entry block, then the walk. -/
def Cfg.eval (fuel : Nat) (cfg : Cfg Γin rets) (V : Γin.Valuation)
    (s : GlobalState) : Option (PoisonOr (HVector toType rets × GlobalState)) :=
  Fuel.andThen (cfg.entry.eval fuel V s) fun p =>
    cfg.blocks.next fuel p.1.1 p.1.2 p.2

/-! ### From fuel to the limit -/

/-- Fuel-monotone: a completed result never changes with more fuel. Both
fueled interpreters satisfy this (`Cfg/Eval.lean`). -/
def FuelMono (f : Nat → Option α) : Prop :=
  ∀ ⦃m n⦄, m ≤ n → ∀ ⦃r⦄, f m = some r → f n = some r

/-- The limit of a fueled computation: its eventual value, or `none` if it
never completes. Classical -- this is where "does it halt" is decided. -/
noncomputable def Fuel.limit (f : Nat → Option α) : Option α :=
  open Classical in
  if h : ∃ n, (f n).isSome then f (Nat.find h) else none

/-- The block walk, unfueled. **A walk with no limit -- a genuinely
non-terminating loop -- is UB**: the artifacts' loop latches carry
`mustProgress = true`, so LLVM already assumes termination (LIMITATIONS 5.1). -/
noncomputable def Blocks.run (bs : Blocks Γamb rets all all)
    (Vamb : Γamb.Valuation) (t : SuccArgs all) :
    EffectM (HVector toType rets) := fun s =>
  Fuel.force (Fuel.limit (fun fuel => bs.iterate fuel Vamb t s))

/-- A block body's semantics. Structural: only a `call`'s tail-block walk
goes through `Blocks.run`; a `call` runs its callee as a function
(`runFunction`: the callee's frame dies on return), argument values entering
the callee's context in reverse declaration order exactly as `SLLVMOp.call`
does. -/
noncomputable def BlockCom.denote :
    {Γ Γout : Ctxt SLLVM.Ty} → {rets : List SLLVM.Ty} →
    {all : List (List SLLVM.Ty)} → BlockCom Γ Γout rets all → Γ.Valuation →
    EffectM (Γout.Valuation × (HVector toType rets ⊕ SuccArgs all))
  | _, _, _, _, .term t, V => do return (V, ← t.denote V)
  | _, _, _, _, .var e body, V => e.denote V >>= body.denote
  | _, _, _, _, .call _ centry cblocks args body, V => do
      let rs ← runFunction do
        let (Vc, r) ← centry.denote (Ctxt.Valuation.ofHVector (args.map V).reverse)
        match r with
        | .inl rs => pure rs
        | .inr next => cblocks.run Vc next
      body.denote (rs ++ V)

noncomputable def Cfg.denote (cfg : Cfg Γin rets) (V : Γin.Valuation) :
    EffectM (HVector toType rets) :=
  cfg.entry.denote V >>= fun (Vout, r) =>
    match r with
    | .inl rets => pure rets
    | .inr next => cfg.blocks.run Vout next

/-! ### Unfolding lemmas

One equation per constructor and, for `condBr`/`switch`, one per outcome of
the scrutinee -- so a proof that knows which branch is taken rewrites the
goal to that branch's continuation in one step.
-/

section Lemmas
variable {Γ : Ctxt SLLVM.Ty} {V : Γ.Valuation}

@[simp, simp_denote] theorem Target.denote_mk {ts : List SLLVM.Ty} {idx : Nat}
    {h : all[idx]? = some ts} {args : HVector Γ.Var ts} :
    Target.denote V ⟨idx, h, args⟩ = ⟨idx, h, args.map V⟩ := rfl

@[simp, simp_denote] theorem Terminator.denote_ret {vs : HVector Γ.Var rets} :
    Terminator.denote (succs := succs) (.ret vs) V = return .inl (vs.map V) := rfl
@[simp, simp_denote] theorem Terminator.denote_br {t : Target Γ succs} :
    Terminator.denote (rets := rets) (.br t) V = return .inr (t.denote V) := rfl

theorem Terminator.denote_condBr {c : Γ.Var (Ty.bitvec 1)} {tT tF : Target Γ succs} :
    Terminator.denote (rets := rets) (.condBr c tT tF) V =
      match V c with
      | .poison => throwUB
      | .value b => return .inr ((if b = 1 then tT else tF).denote V) := rfl

@[simp, simp_denote] theorem Terminator.denote_condBr_value
    {c : Γ.Var (Ty.bitvec 1)} {tT tF : Target Γ succs} (h : V c = .value b) :
    Terminator.denote (rets := rets) (.condBr c tT tF) V =
      return .inr ((if b = 1 then tT else tF).denote V) := by
  simp [denote_condBr, h]

@[simp, simp_denote] theorem Terminator.denote_condBr_poison
    {c : Γ.Var (Ty.bitvec 1)} {tT tF : Target Γ succs} (h : V c = .poison) :
    Terminator.denote (rets := rets) (.condBr c tT tF) V = throwUB := by
  simp [denote_condBr, h]

theorem Terminator.denote_switch {v : Γ.Var (Ty.bitvec w)} {dflt : Target Γ succs} :
    Terminator.denote (rets := rets) (.switch v dflt cases) V =
      match V v with
      | .poison => throwUB
      | .value x =>
          return .inr ((((cases.find? (·.1 == x)).map (·.2)).getD dflt).denote V) := rfl

@[simp, simp_denote] theorem Terminator.denote_switch_value
    {v : Γ.Var (Ty.bitvec w)} {dflt : Target Γ succs} (h : V v = .value x) :
    Terminator.denote (rets := rets) (.switch v dflt cases) V =
      return .inr ((((cases.find? (·.1 == x)).map (·.2)).getD dflt).denote V) := by
  simp [denote_switch, h]

@[simp, simp_denote] theorem Terminator.denote_switch_poison
    {v : Γ.Var (Ty.bitvec w)} {dflt : Target Γ succs} (h : V v = .poison) :
    Terminator.denote (rets := rets) (.switch v dflt cases) V = throwUB := by
  simp [denote_switch, h]

@[simp, simp_denote] theorem BlockCom.denote_term {t : Terminator Γ rets succs} :
    BlockCom.denote (.term t) V = do return (V, ← t.denote V) := rfl
@[simp, simp_denote] theorem BlockCom.denote_var {e : Expr SLLVM Γ .impure tys}
    {body : BlockCom (tys ++ Γ) Γout rets succs} :
    BlockCom.denote (.var e body) V = e.denote V >>= body.denote := rfl

@[simp, simp_denote] theorem BlockCom.denote_call {Γout cΓout : Ctxt SLLVM.Ty}
    {argTys retTys : List SLLVM.Ty} {csigs : List (List SLLVM.Ty)} {callee : String}
    {centry : BlockCom (Ctxt.ofList argTys.reverse) cΓout retTys csigs}
    {cblocks : Blocks cΓout retTys csigs csigs} {args : HVector Γ.Var argTys}
    {body : BlockCom (retTys ++ Γ) Γout rets succs} :
    BlockCom.denote (.call callee centry cblocks args body) V = (do
      let rs ← runFunction do
        let (Vc, r) ← centry.denote (Ctxt.Valuation.ofHVector (args.map V).reverse)
        match r with
        | .inl rs => pure rs
        | .inr next => cblocks.run Vc next
      body.denote (rs ++ V)) := rfl

attribute [simp, simp_denote] Cfg.denote

end Lemmas

end LeanMLIR.SLLVM
