/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# A forward CFG for SLLVM

`Com` is a straight-line let-chain; this module adds the *minimal* control
flow the Firedancer ref extraction needs: a region of basic blocks whose
branches only go **forward**. A block's body has exactly `Com`'s cons shape,
but ends in a `Terminator` (return / br / cond_br / switch) instead of
`Com.rets`. A branch names a `Target`: which *later* block to enter, plus the
values passed to its block arguments -- MLIR's φ nodes.

Two deliberate restrictions, both matching the artifacts:
- **Forward-only.** A `Target` points into the list of blocks *after* the
  current one, so a back-edge is unrepresentable and `denote` is structural --
  total, fuel-free. Loops later mean re-indexing `Target` over the full block
  list and a fuel- or wf-based interpreter; nothing else here encodes
  forwardness.
- **Depth-1 dominance.** A non-entry block sees the entry block's definitions
  (`Γamb`) and its own arguments -- not other blocks' definitions.

Block arguments enter contexts in reverse declaration order
(`Ctxt.ofList argTys.reverse`), the same load-bearing convention as `call`
regions (see `Dialect/Basic.lean`).

Branching on a poison condition or switch scrutinee is UB, as in LLVM.
-/

namespace LeanMLIR.SLLVM

/-- A branch target among the blocks *after* the current one: `succs` lists
their block-argument signatures. Carries the argument variables the branch
passes. Sum-shaped rather than index-based, so case lemmas are plain
equations and no `getElem` casts arise. -/
inductive Target (Γ : Ctxt SLLVM.Ty) : List (List SLLVM.Ty) → Type
  | here (args : HVector Γ.Var ts) : Target Γ (ts :: tss)
  | there (t : Target Γ tss) : Target Γ (ts :: tss)

/-- `Target`'s value level: the chosen block together with the argument
*values* passed to it. -/
inductive SuccArgs : List (List SLLVM.Ty) → Type
  | here (args : HVector toType ts) : SuccArgs (ts :: tss)
  | there (t : SuccArgs tss) : SuccArgs (ts :: tss)

/-- How a block ends: return from the region, or transfer control to a later
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
      (cblocks : Blocks cΓout retTys csigs)
      (args : HVector Γ.Var argTys)
      (body : BlockCom (retTys ++ Γ) Γout rets succs) :
      BlockCom Γ Γout rets succs

/-- The non-entry blocks, in source order; the index lists each block's
argument signature. Block `k` sees the ambient context `Γamb` plus its own
arguments, and its terminator may only target blocks after `k`. -/
inductive Blocks : (Γamb : Ctxt SLLVM.Ty) → (rets : List SLLVM.Ty) →
    List (List SLLVM.Ty) → Type
  | nil : Blocks Γamb rets []
  | cons {Γamb : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty} {argTys sigs}
      {Γout : Ctxt SLLVM.Ty}
      (b : BlockCom (Ctxt.ofList argTys.reverse ++ Γamb) Γout rets sigs)
      (bs : Blocks Γamb rets sigs) : Blocks Γamb rets (argTys :: sigs)

end

/-- A forward CFG: an entry block over the region arguments `Γin`, then the
remaining blocks with the entry's out-context as their ambient context. -/
structure Cfg (Γin : Ctxt SLLVM.Ty) (rets : List SLLVM.Ty) where
  {sigs : List (List SLLVM.Ty)}
  {Γout : Ctxt SLLVM.Ty}
  entry : BlockCom Γin Γout rets sigs
  blocks : Blocks Γout rets sigs

/-! ### Denotation -/

def Target.denote (V : Γ.Valuation) : Target Γ succs → SuccArgs succs
  | .here args => .here (args.map V)
  | .there t => .there (t.denote V)

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

mutual

/-- A `call` runs its callee as a function (`runFunction`: the callee's frame
dies on return), argument values entering the callee's context in reverse
declaration order exactly as `SLLVMOp.call` does. -/
def BlockCom.denote : {Γ Γout : Ctxt SLLVM.Ty} → {rets : List SLLVM.Ty} →
    {succs : List (List SLLVM.Ty)} → BlockCom Γ Γout rets succs → Γ.Valuation →
    EffectM (Γout.Valuation × (HVector toType rets ⊕ SuccArgs succs))
  | _, _, _, _, .term t, V => do return (V, ← t.denote V)
  | _, _, _, _, .var e body, V => e.denote V >>= body.denote
  | _, _, _, _, .call _ centry cblocks args body, V => do
      let rs ← runFunction do
        let (Vc, r) ← centry.denote (Ctxt.Valuation.ofHVector (args.map V).reverse)
        match r with
        | .inl rs => pure rs
        | .inr next => cblocks.denote Vc next
      body.denote (rs ++ V)

/-- Walk the block list: enter the targeted block with its arguments bound
(reverse order, as always), run it, and continue with whatever its
terminator produced. Structural on the block list -- forwardness makes the
interpreter total with no fuel. -/
def Blocks.denote : {Γamb : Ctxt SLLVM.Ty} → {rets : List SLLVM.Ty} →
    {sigs : List (List SLLVM.Ty)} → Blocks Γamb rets sigs → Γamb.Valuation →
    SuccArgs sigs → EffectM (HVector toType rets)
  | _, _, _, .nil, _, t => nomatch t
  | _, _, _, .cons b bs, Vamb, .here args => do
      let (_, r) ← b.denote (Ctxt.Valuation.ofHVector args.reverse ++ Vamb)
      match r with
      | .inl rets => return rets
      | .inr next => bs.denote Vamb next
  | _, _, _, .cons _ bs, Vamb, .there t => bs.denote Vamb t

end

def Cfg.denote (cfg : Cfg Γin rets) (V : Γin.Valuation) :
    EffectM (HVector toType rets) :=
  cfg.entry.denote V >>= fun (Vout, r) =>
    match r with
    | .inl rets => pure rets
    | .inr next => cfg.blocks.denote Vout next

/-! ### Unfolding lemmas

One equation per constructor and, for `condBr`/`switch`, one per outcome of
the scrutinee -- so a proof that knows which branch is taken rewrites the
goal to that branch's continuation in one step.
-/

section Lemmas
variable {Γ : Ctxt SLLVM.Ty} {V : Γ.Valuation}

@[simp, simp_denote] theorem Target.denote_here :
    Target.denote V (.here (tss := tss) args) = .here (args.map V) := rfl
@[simp, simp_denote] theorem Target.denote_there {t : Target Γ tss} :
    Target.denote V (.there (ts := ts) t) = .there (t.denote V) := rfl

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
    {cblocks : Blocks cΓout retTys csigs} {args : HVector Γ.Var argTys}
    {body : BlockCom (retTys ++ Γ) Γout rets succs} :
    BlockCom.denote (.call callee centry cblocks args body) V = (do
      let rs ← runFunction do
        let (Vc, r) ← centry.denote (Ctxt.Valuation.ofHVector (args.map V).reverse)
        match r with
        | .inl rs => pure rs
        | .inr next => cblocks.denote Vc next
      body.denote (rs ++ V)) := rfl

@[simp, simp_denote] theorem Blocks.denote_cons_here {Γamb Γout : Ctxt SLLVM.Ty}
    {Vamb : Γamb.Valuation} {args : HVector toType argTys}
    {b : BlockCom (Ctxt.ofList argTys.reverse ++ Γamb) Γout rets sigs}
    {bs : Blocks Γamb rets sigs} :
    Blocks.denote (.cons b bs) Vamb (.here args) = (do
      let (_, r) ← b.denote (Ctxt.Valuation.ofHVector args.reverse ++ Vamb)
      match r with
      | .inl rets => return rets
      | .inr next => bs.denote Vamb next) := rfl

@[simp, simp_denote] theorem Blocks.denote_cons_there {Γamb Γout : Ctxt SLLVM.Ty}
    {argTys : List SLLVM.Ty} {Vamb : Γamb.Valuation} {t : SuccArgs sigs}
    {b : BlockCom (Ctxt.ofList argTys.reverse ++ Γamb) Γout rets sigs}
    {bs : Blocks Γamb rets sigs} :
    Blocks.denote (.cons b bs) Vamb (.there t) = bs.denote Vamb t := rfl

attribute [simp, simp_denote] Cfg.denote

end Lemmas

end LeanMLIR.SLLVM
