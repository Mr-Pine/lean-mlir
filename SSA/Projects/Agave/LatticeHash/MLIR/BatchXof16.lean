/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXof
import SSA.Projects.Firedancer.Proof.Tactics
namespace AgaveLatticeHash.MLIR.BatchXof16
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Input9 := blockInput agave_batch_16.cfgBlock_9

def next9 (V : Input9.Valuation) (counter : Nat) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨10, rfl,
    V ⟨114, rfl⟩ ::ₕ
    V ⟨2, rfl⟩ ::ₕ
    V ⟨3, rfl⟩ ::ₕ
    V ⟨4, rfl⟩ ::ₕ
    V ⟨5, rfl⟩ ::ₕ
    V ⟨6, rfl⟩ ::ₕ
    V ⟨7, rfl⟩ ::ₕ
    V ⟨8, rfl⟩ ::ₕ
    V ⟨9, rfl⟩ ::ₕ
    V ⟨105, rfl⟩ ::ₕ
    V ⟨106, rfl⟩ ::ₕ
    V ⟨107, rfl⟩ ::ₕ
    V ⟨108, rfl⟩ ::ₕ
    Vector.replicate 16 (PoisonOr.value (BitVec.ofNat 32 counter)) ::ₕ
    V ⟨95, rfl⟩ ::ₕ
    V ⟨1, rfl⟩ ::ₕ
    V ⟨0, rfl⟩ ::ₕ
    V ⟨9, rfl⟩ ::ₕ
    V ⟨8, rfl⟩ ::ₕ
    V ⟨7, rfl⟩ ::ₕ
    V ⟨6, rfl⟩ ::ₕ
    V ⟨5, rfl⟩ ::ₕ
    V ⟨4, rfl⟩ ::ₕ
    V ⟨3, rfl⟩ ::ₕ
    V ⟨2, rfl⟩ ::ₕ
    V ⟨1, rfl⟩ ::ₕ
    V ⟨0, rfl⟩ ::ₕ
    V ⟨10, rfl⟩ ::ₕ .nil⟩
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Actual root counter truncation and sixteen-lane broadcast for all 32 blocks. -/
theorem block9_continue {α : Type} (V : Input9.Valuation) (s : GlobalState)
    (counter : Nat) (hc : counter < 32)
    (hcounter : V ⟨10, rfl⟩ = PoisonOr.value (BitVec.ofNat 64 counter))
    (hzero : V ⟨114, rfl⟩ = PoisonOr.value 0#64)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_16.cfgBlock_9.denote V >>= fun r => k r.2) s =
      StateT.run (k (.inr (next9 V counter))) s := by
  denote_step_all v
  denote_eval v 0 2
  have e0 : v0 = PoisonOr.value (BitVec.ofNat 32 counter) := by
    rw [hv0, hcounter]
    exact BatchXof.counter_trunc counter hc
  have e2 : v2 = Vector.replicate 16 (PoisonOr.value (BitVec.ofNat 32 counter)) := by
    rw [hv2, hv1, e0, hzero]
    apply Vector.ext
    intro i hi
    change i < 16 at hi
    interval_cases i <;> simp [LLVM.Ty.shufflevector, LLVM.Ty.insertelement]
  rw [e2]
  simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote]
  rfl

noncomputable def input9 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[9]'(by decide))) : Input9.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

/-- Dispatcher transport of the exact lifted-block continuation theorem. -/
theorem run9 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[9]'(by decide)))
    (s : GlobalState)
    (counter : Nat) (hc : counter < 32)
    (hcounter : (input9 A args) ⟨10, rfl⟩ = PoisonOr.value (BitVec.ofNat 64 counter))
    (hzero : (input9 A args) ⟨114, rfl⟩ = PoisonOr.value 0#64)
    : StateT.run (agave_batch_16.blocks.run A ⟨9, rfl, args⟩) s =
      StateT.run (agave_batch_16.blocks.run A (next9 (input9 A args) counter)) s := by
  denote_enter_block
  exact block9_continue (input9 A args) s counter hc hcounter hzero
    (fun r => match r with | .inl rets => pure rets | .inr next => agave_batch_16.blocks.run A next)
end AgaveLatticeHash.MLIR.BatchXof16
