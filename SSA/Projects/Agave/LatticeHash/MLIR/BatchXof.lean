/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootCopy
namespace AgaveLatticeHash.MLIR.BatchXof
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Input22 := blockInput agave_batch_8.cfgBlock_22

/-- Both overflow promises on the compiler's XOF-counter truncation hold
for every one of the thirty-two output blocks. -/
theorem counter_trunc (counter : Nat) (hc : counter < 32) :
    LLVM.trunc 32 (PoisonOr.value (BitVec.ofNat 64 counter)) ⟨true, true⟩ =
      PoisonOr.value (BitVec.ofNat 32 counter) := by
  interval_cases counter <;> decide +kernel

/-- Flagged byte-stride arithmetic is defined for every root-output block. -/
theorem counter_shift6 (counter : Nat) (hc : counter < 32) :
    LLVM.shl (PoisonOr.value (BitVec.ofNat 64 counter)) (PoisonOr.value 6#64)
      ⟨true, true⟩ = PoisonOr.value (BitVec.ofNat 64 (64 * counter)) := by
  interval_cases counter <;> decide +kernel

/-- The actual flagged XOF-counter increment cannot overflow. -/
theorem counter_succ (counter : Nat) (hc : counter < 32) :
    LLVM.add (PoisonOr.value (BitVec.ofNat 64 counter)) (PoisonOr.value 1#64)
      ⟨true, true⟩ = PoisonOr.value (BitVec.ofNat 64 (counter + 1)) := by
  interval_cases counter <;> decide +kernel

/-- The actual exit comparison is true precisely on the final output block. -/
theorem counter_exit (counter : Nat) (hc : counter < 32) :
    LLVM.icmp .eq (PoisonOr.value (BitVec.ofNat 64 (counter + 1)))
      (PoisonOr.value 32#64) =
      PoisonOr.value (BitVec.ofBool (decide (counter = 31))) := by
  interval_cases counter <;> decide +kernel

/-- Every taken backedge re-establishes the truncation/shift/increment bound. -/
theorem counter_backedge_bound (counter : Nat) (hc : counter < 32)
    (hmore : counter ≠ 31) : counter + 1 < 32 := by omega

/-- Exact initialization payload of the actual root-output compression loop. -/
def next22 (V : Input22.Valuation) (counter : Nat) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨23, rfl, V ⟨85, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
    V ⟨15, rfl⟩ ::ₕ
    V ⟨14, rfl⟩ ::ₕ
    V ⟨13, rfl⟩ ::ₕ
    V ⟨12, rfl⟩ ::ₕ
    V ⟨11, rfl⟩ ::ₕ
    V ⟨10, rfl⟩ ::ₕ
    V ⟨9, rfl⟩ ::ₕ
    V ⟨68, rfl⟩ ::ₕ
    V ⟨67, rfl⟩ ::ₕ
    V ⟨66, rfl⟩ ::ₕ
    V ⟨65, rfl⟩ ::ₕ
    Vector.replicate 8 (PoisonOr.value (BitVec.ofNat 32 counter)) ::ₕ
    V ⟨81, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
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
    V ⟨2, rfl⟩ ::ₕ
    V ⟨1, rfl⟩ ::ₕ
    V ⟨0, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ .nil⟩
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Execute the actual counter truncation, insertion and SIMD broadcast,
retaining the saved CV, root length/flags, output pointer, and counter. -/
theorem block22_continue {α : Type} (V : Input22.Valuation) (s : GlobalState)
    (counter : Nat) (hc : counter < 32)
    (hcounter : V ⟨19, rfl⟩ = PoisonOr.value (BitVec.ofNat 64 counter))
    (hzero : V ⟨85, rfl⟩ = PoisonOr.value 0#64)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_22.denote V >>= fun r => k r.2) s =
      StateT.run (k (.inr (next22 V counter))) s := by
  denote_step_all v
  denote_eval v 0 2
  have e0 : v0 = PoisonOr.value (BitVec.ofNat 32 counter) := by
    rw [hv0, hcounter]
    exact counter_trunc counter hc
  have e2 : v2 = Vector.replicate 8 (PoisonOr.value (BitVec.ofNat 32 counter)) := by
    rw [hv2, hv1, e0, hzero]
    apply Vector.ext
    intro i hi
    change i < 8 at hi
    interval_cases i <;> simp [LLVM.Ty.shufflevector, LLVM.Ty.insertelement]
  rw [e2]
  simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote]
  rfl
end AgaveLatticeHash.MLIR.BatchXof
