module

public import SSA.Projects.RIR.SimpSets
public import SSA.Projects.RIR.Context
public meta import Lean.Elab.Term
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.PrettyPrinter.Delaborator.Basic

namespace LeanMLIR.RIR

@[expose] public section

structure Env (Γ : Ctx) where
  args : (i : Fin Γ.args.length) → ⟦Γ.args[i]⟧
  vals : (i : Fin Γ.n) → ⟦Γ.ty i⟧

/-- `⟪Γ⟫` is the `Env` of `Γ`, functions mapping the args
  and vals to a value of the correct type --/
notation "⟪" Γ "⟫" => LeanMLIR.RIR.Env Γ

namespace Env

def init {Γ : Ctx} (args : (i : Fin Γ.args.length) → ⟦Γ.args[i]⟧) : ⟪Γ⟫ :=
  { args := args, vals := fun i => (Γ.ty i).poisoned }

def read (env : ⟪Γ⟫) (reg : Reg Γ t) : ⟦t⟧ :=
  match reg with
  | .arg i h => h.symm ▸ env.args i
  | .val i h => h.symm ▸ env.vals i

def set (env : ⟪Γ⟫) (i : Fin Γ.n) (v : ⟦Γ.ty i⟧) : ⟪Γ⟫ :=
  { env with vals := fun j => if h : j = i then h ▸ v else env.vals j }

def write (env : ⟪Γ⟫) (dst : Dst Γ t) (v : ⟦t⟧) : ⟪Γ⟫ :=
  set env dst.i (dst.h.symm ▸ v)

section Lemmas

@[simp, mlir_env]
theorem read_set_self (env : ⟪Γ⟫) : (env.set i v).read (.val (t := t) i ht) = ht ▸ v := by
  simp [set, read]

@[simp, mlir_env]
theorem read_set_ne (env : ⟪Γ⟫) (h : i ≠ j) :
    (env.set i v).read (.val j ht) = env.read (.val j ht) := by simp [set, read, h.symm]

@[simp, mlir_env]
theorem set_set (env : ⟪Γ⟫) : (env.set i v).set i w = env.set i w := by
  simp [set]
  ext j
  split <;> rfl

theorem set_comm (env : ⟪Γ⟫) (h : i ≠ j) : (env.set i v).set j w = (env.set j w).set i v := by
  simp [set]
  ext k
  split <;> try rfl
  rename_i hkj
  simp [h.symm, hkj]

/-- A register read right after its write is the written value: the casts in and out cancel, even
for a `dst` whose type proof is not `rfl`. -/
@[simp, mlir_env]
theorem read_write_dst (env : ⟪Γ⟫) (dst : Dst Γ t) (v : ⟦t⟧) :
    (env.write dst v).read (.val dst.i dst.h) = v := by
  obtain ⟨i, h⟩ := dst
  subst h
  simp [write, read, set]

/-- Writing the value a register already holds changes nothing. -/
theorem write_of_read (env : ⟪Γ⟫) (dst : Dst Γ t) (h : env.read (.val dst.i dst.h) = v) :
    env.write dst v = env := by
  obtain ⟨i, hi⟩ := dst
  subst hi h
  cases env
  simp only [write, set, read, Env.mk.injEq, true_and]
  funext j
  split <;> rename_i h <;> (try subst h) <;> rfl

theorem write_comm (env : ⟪Γ⟫) (h : dst.i ≠ dst'.i) :
    (env.write dst v).write dst' w = (env.write dst' w).write dst v := by
  unfold write
  apply set_comm
  exact h

@[mlir_env]
theorem read_write_self (env : ⟪Γ⟫) (dst : Dst Γ t) :
    (env.write dst v).read (.val dst.i dst.h) = dst.h ▸ v := by
  unfold Env.write
  apply read_set_self

@[mlir_env]
theorem read_write_self' (env : ⟪Γ⟫) : (env.write ⟨i, h⟩ v).read (.val i h) = h ▸ v := by
  apply read_write_self

@[mlir_env]
theorem read_write_ne (env : ⟪Γ⟫) (dst : Dst Γ t) (h : i ≠ dst.i := by decide) :
    (env.write dst v).read (.val (t := t') i ht') = env.read (.val i ht') := by
  unfold Env.write
  apply read_set_ne env h.symm

@[mlir_env]
theorem read_write_ne' (env : ⟪Γ⟫) (hij : i ≠ j := by decide) :
    (env.write ⟨i, h⟩ v).read (.val (t := t') j ht') = env.read (.val j ht') := by
  apply read_write_ne
  apply hij.symm

@[simp, mlir_env]
theorem write_args (env : ⟪Γ⟫) (dst : Dst Γ t) : (env.write dst v).args = env.args := by rfl

@[mlir_env]
theorem read_write_arg (env : ⟪Γ⟫) (dst : Dst Γ t) :
    (env.write dst v).read (.arg i h) = env.read (.arg i h) := by simp [read]

@[mlir_env]
theorem read_arg (env : ⟪Γ⟫) : env.read (.arg i h) = h ▸ env.args i := by rfl

@[mlir_env]
theorem read_init_arg (args : _) : (Env.init args).read (.arg i h) = args i := by rfl

/-- Writing the value a register holds already changes nothing. -/
theorem write_eq_of {E₀ E : ⟪Γ⟫} (h₀ : E₀ = E) (hr : E.read (.val i h) = v) :
    E₀.write ⟨i, h⟩ v = E := by
  subst h₀ h hr
  cases E₀
  simp only [write, set, read, mk.injEq, true_and]
  funext j
  split
  · subst_vars; rfl
  · rfl

end Lemmas

meta section Syntax

open Lean Elab Term Meta

/-- `E[d := v, …]` writes `v` to `d` in `E`, left to right. -/
syntax :max (name := envWrite) term noWs "[" withoutPosition(term " := " term),+ "]" : term

@[app_unexpander Env.write] def unexpandWrite : PrettyPrinter.Unexpander
  | `($_ $E[$[$ds := $vs],*] $d $v) => `($E[$[$ds := $vs],*, $d := $v])
  | `($_ $E $d $v) => `($E[$d := $v])
  | _ => throw ()

/-- `%k` is value register `k`: a `Dst` or a `Reg`, by the expected type. -/
syntax :lead (name := valReg) "%" noWs num : term

/-- `%argk` is argument register `k`. -/
syntax :lead (name := argReg) "%arg" noWs num : term

def expectedHead (ty? : Option Expr) (what : String) : TermElabM Expr := do
  tryPostponeIfNoneOrMVar ty?
  let some ty := ty? | throwError "{what} needs an expected type"
  let ty ← instantiateMVars ty
  if ty.getAppFn.isMVar then
    throwError "`{what}` needs an expected type, got{indentExpr ty}"
  return ty

/-- `Γ.argBase` or `Γ.valBase` (`base`) as a literal; `0` if `Γ` is no literal. -/
def regBase (base : Name) (Γ : Expr) : MetaM Nat := do
  return (← evalNat (← whnfD (mkApp (mkConst base) Γ))).getD 0

/-- The register of `%k` or `%argk` in `Γ`: `k` less `base`. -/
def regSlot (base : Name) (Γ : Expr) (k : TSyntax `num) : TermElabM (TSyntax `num) := do
  let b ← regBase base Γ
  unless b ≤ k.getNat do
    throwErrorAt k "the registers of this context start at {b}"
  return Syntax.mkNumLit (toString (k.getNat - b))

@[term_elab valReg]
def elabValReg : TermElab := fun stx ty? => do
  let ty ← whnfR (← expectedHead ty? "%k")
  let k ← regSlot ``Ctx.valBase ty.appFn!.appArg! ⟨stx.getArg 1⟩
  if ty.isAppOf ``Dst then
    elabTerm (← `(⟨$k, rfl⟩)) ty
  else
    elabTerm (← `(Reg.val $k rfl)) ty

@[term_elab argReg]
def elabArgReg : TermElab := fun stx ty? => do
  let ty ← whnfR (← expectedHead ty? "%k")
  let k ← regSlot ``Ctx.argBase ty.appFn!.appArg! ⟨stx.getArg 1⟩
  elabTerm (← `(Reg.arg $k rfl)) ty

/-- The type of value `%k` of `Γ`, if `Γ.vals` unfolds to a list. -/
def valTy? (Γ : Expr) (k : Nat) : MetaM (Option Expr) := do
  let b ← regBase ``Ctx.valBase Γ
  if k < b then
    return none
  let k := k - b
  let rec go (l : Expr) : Nat → MetaM (Option Expr)
    | k => do
      let l ← whnfD l
      let_expr List.cons _ x xs := l | return none
      if k = 0 then
        return some (← whnfR x)
      else
        go xs (k - 1)
  go (mkApp (mkConst ``Ctx.vals) Γ) k

/-- Elaborates `v` as a `⟦t⟧`, or else a raw value wrapped: `.value v` or `Ty.wrap v`. -/
def elabValue (v : Term) (t : Expr) : TermElabM Expr := do
  let expected := mkApp (mkConst ``Ty.denote) t
  let s ← saveState
  try
    withoutErrToSorry do
        let e ← elabTermEnsuringType v expected
        synthesizeSyntheticMVarsNoPostponing
        return e
  catch ex =>
    s.restore
    let wrapped ←
      match (← whnfR t).getAppFn.constName? with
      | some ``Ty.vec =>
        `(Ty.wrap (t := $(← exprToSyntax t)) $v)
      | some ``Ty.bv | some ``Ty.ptr =>
        `(PoisonOr.value $v)
      | _ =>
        throw ex
    elabTermEnsuringType wrapped expected

/-- Elaborates `E` first, so its `Γ` types each `%k` and, through it, each value. -/
@[term_elab envWrite]
def elabEnvWrite : TermElab := fun stx ty? => do
  let E ← elabTerm stx[0] none
  let envTy ← whnfR (← instantiateMVars (← inferType E))
  let_expr Env Γ := envTy |
    do
      tryPostponeIfMVar envTy
      throwError "`E[d := v]` needs `E` to be an `Env`, got{indentExpr envTy}"
  let mut env := E
  for w in stx[2].getSepArgs do
    let d := w[0]
    let t ←
      if d.getKind == ``valReg then
        do
          pure ((← valTy? Γ (d[1].isNatLit?.getD 0)).getD (← mkFreshExprMVar (mkConst ``Ty)))
      else
        mkFreshExprMVar (mkConst ``Ty)
    let dst ← elabTermEnsuringType d (mkApp2 (mkConst ``Dst) Γ t)
    synthesizeSyntheticMVarsNoPostponing
    let t ← instantiateMVars t
    let v ← elabValue ⟨w[2]⟩ t
    env := mkAppN (mkConst ``Env.write) #[Γ, t, env, dst, v]
  ensureHasType ty? env

/-- `E ⊨ [r := v, …]`: `E` reads `v` at `r`, for each pair, as a conjunction. A register is `%k`,
`%argk`, a `Reg`, or a `Dst` (its value register); a value is typed and wrapped as in
`E[d := v]`. -/
syntax :50 (name := envReads) term:51 " ⊨ " "[" withoutPosition(term " := " term),+ "]" : term

/-- The register `d` of `Γ`: elaborated as a `Reg`, else a `Dst`'s value register. -/
def elabReadReg (Γ : Expr) (d : Syntax) : TermElabM (Expr × Expr) := do
  let t ←
    if d.getKind == ``valReg then
      pure ((← valTy? Γ (d[1].isNatLit?.getD 0)).getD (← mkFreshExprMVar (mkConst ``Ty)))
    else
      mkFreshExprMVar (mkConst ``Ty)
  let s ← saveState
  try
    let r ←
      withoutErrToSorry do
          let r ← elabTermEnsuringType d (mkApp2 (mkConst ``Reg) Γ t)
          synthesizeSyntheticMVarsNoPostponing
          pure r
    -- an argument's type as a `Ty` constructor (`G.args[0]` is `.bv 8`), for wrapping its value
    return (r, ← whnfD (← instantiateMVars t))
  catch _ =>
    s.restore
    let x ← elabTerm d none
    synthesizeSyntheticMVarsNoPostponing
    let_expr Dst Γ' t :=
      ←
        whnfR
            (←
              inferType
                  x) | throwError "`E ⊨ [r := v]` needs `r` to be a register, got{indentExpr x}"
    let i := mkApp3 (mkConst ``Dst.i) Γ' t x
    let h := mkApp3 (mkConst ``Dst.h) Γ' t x
    return (mkApp4 (mkConst ``Reg.val) Γ' t i h, t)

@[term_elab envReads]
def elabEnvReads : TermElab := fun stx ty? => do
  let E ← elabTerm stx[0] none
  let envTy ← whnfR (← instantiateMVars (← inferType E))
  let_expr Env Γ := envTy |
    do
      tryPostponeIfMVar envTy
      throwError "`E ⊨ [r := v]` needs `E` to be an `Env`, got{indentExpr envTy}"
  let mut reads := #[]
  for w in stx[3].getSepArgs do
    let (r, t) ← elabReadReg Γ w[0]
    let v ← elabValue ⟨w[2]⟩ t
    reads := reads.push (← mkEq (mkAppN (mkConst ``Env.read) #[Γ, t, E, r]) v)
  let some last := reads.back? | throwError "`E ⊨ []`: no reads"
  ensureHasType ty? (reads.pop.foldr mkAnd last)

open PrettyPrinter.Delaborator SubExpr in
/-- A register `c Γ t i h` with a literal `i` as `%(b + i)`, or `%arg(b + i)`, `b` being `Γ`'s
`base`. -/
def delabReg (arg : Bool) (base : Name) : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let_expr OfNat.ofNat _ i _ := e.getArg! 2 | failure
  let some i := i.rawNatLit? | failure
  let k := Syntax.mkNumLit (toString ((← regBase base (e.getArg! 0)) + i))
  return if arg then ⟨mkNode ``argReg #[mkAtom "%arg", k]⟩ else ⟨mkNode ``valReg #[mkAtom "%", k]⟩

@[delab app.LeanMLIR.RIR.Dst.mk]
def delabDst : PrettyPrinter.Delaborator.Delab :=
  delabReg false ``Ctx.valBase

@[delab app.LeanMLIR.RIR.Reg.val]
def delabRegVal : PrettyPrinter.Delaborator.Delab :=
  delabReg false ``Ctx.valBase

@[delab app.LeanMLIR.RIR.Reg.arg]
def delabRegArg : PrettyPrinter.Delaborator.Delab :=
  delabReg true ``Ctx.argBase

end Syntax

end Env

end

end LeanMLIR.RIR
