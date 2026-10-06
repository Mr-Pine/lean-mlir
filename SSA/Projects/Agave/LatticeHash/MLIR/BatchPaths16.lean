/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXof
import SSA.Projects.Firedancer.Proof.Tactics
namespace AgaveLatticeHash.MLIR.BatchPaths16
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Input6 := blockInput agave_batch_16.cfgBlock_6

def words16 (v : Vector (LLVM.IntW 64) 8) : Vector (LLVM.IntW 32) 16 :=
  bitcast (.vector 8 (.bitvec 64)) (.vector 16 (.bitvec 32)) v

def next6 (V : Input6.Valuation) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨7, rfl,
    V ⟨132, rfl⟩ ::ₕ
    V ⟨3, rfl⟩ ::ₕ
    V ⟨4, rfl⟩ ::ₕ
    V ⟨5, rfl⟩ ::ₕ
    V ⟨6, rfl⟩ ::ₕ
    V ⟨7, rfl⟩ ::ₕ
    V ⟨8, rfl⟩ ::ₕ
    V ⟨9, rfl⟩ ::ₕ
    V ⟨10, rfl⟩ ::ₕ
    V ⟨123, rfl⟩ ::ₕ
    V ⟨124, rfl⟩ ::ₕ
    V ⟨125, rfl⟩ ::ₕ
    V ⟨126, rfl⟩ ::ₕ
    V ⟨113, rfl⟩ ::ₕ
    V ⟨113, rfl⟩ ::ₕ
    words16 (V ⟨1, rfl⟩) ::ₕ
    words16 (V ⟨2, rfl⟩) ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
    V ⟨15, rfl⟩ ::ₕ
    V ⟨14, rfl⟩ ::ₕ
    V ⟨13, rfl⟩ ::ₕ
    V ⟨12, rfl⟩ ::ₕ
    V ⟨11, rfl⟩ ::ₕ
    V ⟨10, rfl⟩ ::ₕ
    V ⟨9, rfl⟩ ::ₕ
    V ⟨8, rfl⟩ ::ₕ
    V ⟨7, rfl⟩ ::ₕ
    V ⟨6, rfl⟩ ::ₕ
    V ⟨5, rfl⟩ ::ₕ
    V ⟨4, rfl⟩ ::ₕ
    V ⟨3, rfl⟩ ::ₕ
    V ⟨0, rfl⟩ ::ₕ .nil⟩
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Actual nonroot compression initialization, with exact live successor arguments. -/
theorem block6_continue {α : Type} (V : Input6.Valuation) (s : GlobalState)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_16.cfgBlock_6.denote V >>= fun r => k r.2) s =
      StateT.run (k (.inr (next6 V))) s := by
  denote_step_all v
  denote_eval v 0 1
  rw [hv0, hv1]
  simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote]
  rfl

noncomputable def input6 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[6]'(by decide))) : Input6.Valuation :=
  Ctxt.Valuation.ofHVector args.reverse ++ A

/-- Dispatcher transport of the exact lifted-block continuation theorem. -/
theorem run6 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[6]'(by decide)))
    (s : GlobalState)
    : StateT.run (agave_batch_16.blocks.run A ⟨6, rfl, args⟩) s =
      StateT.run (agave_batch_16.blocks.run A (next6 (input6 A args))) s := by
  denote_enter_block
  exact block6_continue (input6 A args) s
    (fun r => match r with | .inl rets => pure rets | .inr next => agave_batch_16.blocks.run A next)
end AgaveLatticeHash.MLIR.BatchPaths16
