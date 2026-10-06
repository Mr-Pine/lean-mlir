/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PrefixTransport
import SSA.Projects.Firedancer.MLIR.DenoteStep

namespace AgaveLatticeHash.MLIR.BlockPrefix
open LeanMLIR SLLVM

inductive Pure : BlockPrefix Γ Δ → Prop
  | nil : Pure .nil
  | var {e : Expr SLLVM Γ .impure ts} {p : BlockPrefix (ts ++ Γ) Δ}
      (he : e.HasPureOp) (hp : Pure p) : Pure (.var e p)

theorem Pure.denote_exists {p : BlockPrefix Γ Δ} (h : Pure p) (V : Γ.Valuation) :
    ∃ W : Δ.Valuation, p.denote V = pure W ∧ W.comap p.contextHom = V := by
  induction h with
  | nil => exact ⟨V, rfl, rfl⟩
  | @var Γ ts Δ e p he hp ih =>
    obtain ⟨W, hr, hc⟩ := ih ((e.toPure he).denoteOpPure V ++ V)
    refine ⟨W, ?_, ?_⟩
    · simp only [denote, Expr.denote_unfold]
      rw [← Expr.pure_denoteOp_toPure e he]
      simp only [map_pure, pure_bind]
      exact hr
    · change (W.comap p.contextHom).comap e.contextHom = V
      rw [hc]
      exact Expr.comap_append_contextHom e _ V

end AgaveLatticeHash.MLIR.BlockPrefix

namespace AgaveLatticeHash.MLIR.PortableXof
open LeanMLIR SLLVM
open InstCombine (LLVM)

inductive Stored : {Γ Ω : Ctxt SLLVM.Ty} → Γ.Var (SLLVM.Ty.bitvec 32) →
    BlockCom Γ Ω rs ss → Prop
  | head {Γ Ω : Ctxt SLLVM.Ty} (p : Γ.Var .ptr) (x : Γ.Var (SLLVM.Ty.bitvec 32))
      (b : BlockCom Γ Ω rs ss) :
      Stored x (.var (Expr.mk (SLLVMOp.store (.bitvec 32)) rfl (EffectKind.le_refl _)
        (p ::ₕ x ::ₕ .nil) Regions.nil) b)
  | var {Γ Ω : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} (e : Expr SLLVM Γ .impure ts)
      (x : Γ.Var (SLLVM.Ty.bitvec 32)) (b : BlockCom (ts ++ Γ) Ω rs ss)
      (h : Stored (e.contextHom x) b) : Stored x (.var e b)

private theorem run_store_poison (p : SLLVM.Ptr) (s : MemoryState) :
    StateT.run (store p (.bitvec 32) .poison) s = .poison := by
  cases p using PoisonOr.casesOn' <;> simp [store, PoisonOr.getOrUB, LLVM.Ty.flatten, LLVM.Ty.Defined]

private theorem run_liftM_poison {α : Type} {x : MemorySSAM α} {s : GlobalState}
    (h : x.run s.mem = .poison) :
    (liftM x : EffectM α).run s = .poison := by
  cases s
  simp only [liftM, monadLift, MonadLift.monadLift, StateT.run] at *
  rw [h]

theorem Stored.defined {Γ Ω : Ctxt SLLVM.Ty} {rs ss}
    {x : Γ.Var (SLLVM.Ty.bitvec 32)} {b : BlockCom Γ Ω rs ss}
    (h : Stored x b) (V : Γ.Valuation) (s : GlobalState)
    {α : Type} (K : (Ω.Valuation × (HVector toType rs ⊕ SuccArgs ss)) → EffectM α)
    (y : α × GlobalState)
    (hrun : StateT.run (b.denote V >>= K) s = .value y) : V x ≠ .poison := by
  induction h generalizing s with
  | head p x b =>
    intro hx
    simp only [BlockCom.denote_var, bind_assoc, Expr.denote_unfold,
      EffectM.run_bind, EffectM.run_map] at hrun
    have hs : StateT.run
        ((Expr.mk (d := SLLVM) (Γ := _) (eff := .impure)
          (SLLVMOp.store (.bitvec 32)) rfl (EffectKind.le_refl _)
          (p ::ₕ x ::ₕ .nil) Regions.nil).denoteOp V) s = .poison := by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm, hx]
      rw [run_liftM_poison (run_store_poison (V p) s.mem)]
      rfl
    rw [hs] at hrun
    exact PoisonOr.poison_ne_value y hrun
  | @var Γ Ω ts e x b h ih =>
    rw [BlockCom.denote_var, bind_assoc, Expr.denote_unfold,
      EffectM.run_bind, EffectM.run_map] at hrun
    cases he : StateT.run (e.denoteOp V) s with
    | poison =>
      rw [he] at hrun
      exact False.elim (PoisonOr.poison_ne_value y hrun)
    | value z =>
      rcases z with ⟨vs, s'⟩
      rw [he] at hrun
      have hd := ih (vs ++ V) s' K hrun
      have hc := congrArg (fun U => U x) (Expr.comap_append_contextHom e vs V)
      exact hc ▸ hd

end AgaveLatticeHash.MLIR.PortableXof
