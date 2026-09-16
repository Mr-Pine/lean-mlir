/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg.Basic

/-!
# A straight-line `Com` as a one-block `Cfg`

`Com` and `BlockCom` describe the same straight-line programs: `Com.rets` is a
`ret` terminator, `Com.var` is `BlockCom.var`. A callee lifted with
`[sllvm_of| …]` is a `Com`, while a `BlockCom.call` node holds a `Cfg`, so a
caller lifted with `[sllvm_cfg_of| …]` needs the translation -- and
`denote_ofCom` to reuse the callee's conformance theorem across it.

`Cfg` hides its output context and block signatures as fields, so the
recursion is stated on `Cfg` rather than on `BlockCom`: an `ofCom` indexed by
`Com.outContext` does not reduce under `Com.rec'`, whose `var` case spells the
body's context `Expr.outContext e` where the constructor spells it `tys ++ Γ`.
-/

namespace LeanMLIR.SLLVM

/-- A straight-line `Com` as a one-block CFG. -/
def Cfg.ofCom {ts : List SLLVM.Ty} : {Γ : Ctxt SLLVM.Ty} → Com SLLVM Γ .impure ts → Cfg Γ ts
  | _, .rets vs => ⟨.term (.ret vs), .nil⟩
  | _, .var e body => ⟨.var e (Cfg.ofCom body).entry, (Cfg.ofCom body).blocks⟩

@[simp]
theorem Cfg.ofCom_rets {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} (vs : HVector Γ.Var ts) :
    Cfg.ofCom (Com.rets (eff := .impure) vs) = ⟨.term (.ret vs), .nil⟩ := by rw [Cfg.ofCom]

@[simp]
theorem Cfg.ofCom_var {Γ : Ctxt SLLVM.Ty} {ts tys : List SLLVM.Ty} {e : Expr SLLVM Γ .impure tys}
    {body : Com SLLVM _ .impure ts} :
    Cfg.ofCom (Com.var e body) = ⟨.var e (Cfg.ofCom body).entry, (Cfg.ofCom body).blocks⟩ := by
  rw [Cfg.ofCom]

@[simp, simp_denote]
theorem Cfg.denote_ofCom {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} (c : Com SLLVM Γ .impure ts)
    (V : Γ.Valuation) : (Cfg.ofCom c).denote V = c.denote V := by
  induction c using Com.rec' with
  | rets vs =>
    rw [Cfg.ofCom_rets]; simp [Cfg.denote]
  | var e body ih =>
    rw [Cfg.ofCom_var]
    simp only [Cfg.denote, BlockCom.denote_var, bind_assoc, Com.denote_var]
    refine bind_congr fun a => Eq.trans ?_ (ih a)
    -- The two unfoldings of `Cfg.denote` produce distinct match auxiliaries;
    -- destructing the scrutinee iota-reduces both to the same branches.
    simp only [Cfg.denote]
    refine bind_congr fun x => ?_
    rcases x with ⟨Vout, r | n⟩ <;> rfl

/-- `denote_ofCom` in the shape a by-reference call site carries: the callee
rebuilt from its own projections (`Cfg.mk` of a value's projections is the
value, by structure eta). -/
@[simp, simp_denote]
theorem Cfg.denote_mk_ofCom {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} (c : Com SLLVM Γ .impure ts)
    (V : Γ.Valuation) : Cfg.denote ⟨(Cfg.ofCom c).entry, (Cfg.ofCom c).blocks⟩ V = c.denote V :=
  Cfg.denote_ofCom c V

/-- As `denote_mk_ofCom`, for a callee that is a `Cfg` constant already. -/
@[simp, simp_denote]
theorem Cfg.denote_mk_self {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} (c : Cfg Γ ts)
    (V : Γ.Valuation) : Cfg.denote ⟨c.entry, c.blocks⟩ V = c.denote V :=
  rfl

end LeanMLIR.SLLVM
