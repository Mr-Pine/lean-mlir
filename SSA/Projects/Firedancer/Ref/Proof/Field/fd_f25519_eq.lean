import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_eq
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sub
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_is_zero

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 3200000 in
theorem fd_f25519_eq_conforms (p q: Pointer) (s: GlobalState)
  (hs : s.WF)
  (hp : IsFieldElemPtr s.mem p)
  (hq : IsFieldElemPtr s.mem q)
  (hpbounds : LimbBounds hp)
  (hqbounds : BiasBounds hq) :
  fd_f25519_eq_spec p q s hp hq := by
    simp only [fd_f25519_eq_spec, Cfg.denote]

    -- `fd_f25519_t r[1]`
    obtain ⟨r, sAlloc, hrdef, hsAlloc, hsAllocWF, hrfits, hrid, hroff, -, -⟩ :=
      GlobalState.exists_afterAlloca_facts s hs (5 * 64)
    have fb : FrameBelow s.alloc.nextFreeBlock s sAlloc :=
      hsAlloc ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    have hr₁ : IsFieldElemPtr sAlloc.mem r := ⟨hrfits, by simp [hroff]⟩
    have hlive : ∀ t : Pointer, IsFieldElemPtr s.mem t →
        sAlloc.mem.live? t.id = s.mem.live? t.id :=
      fun t ht => fb t.id (lt_nextFreeBlock_of_fits hs ht.left)
    have hp₁ : IsFieldElemPtr sAlloc.mem p := isFieldElemPtr_of_live?_eq (hlive p hp) hp
    have hq₁ : IsFieldElemPtr sAlloc.mem q := isFieldElemPtr_of_live?_eq (hlive q hq) hq

    have hpbounds₁ : ∀ (i : Fin 5) (l : ℕ), readLimb? p i sAlloc.mem = some l → l ≤ 0x8000000000000 :=
      fun i l hl => limbBounds_readLimb? hp hpbounds i l (by simpa [readLimb?, hlive p hp] using hl)
    have hqbounds₁ : BiasBounds? q sAlloc.mem :=
      fun i l hl => biasBounds_readLimb? hq hqbounds i l (by simpa [readLimb?, hlive q hq] using hl)

    obtain ⟨subres, hsubval, hsubbnd, substate, hsubstate, hsubstate_eq⟩ :=
      fd_f25519_sub_conforms r p q sAlloc hsAllocWF hpbounds₁ hqbounds₁ hr₁ hp₁ hq₁

    have hrbounds? : ∀ (i : Fin 5) (l : ℕ), readLimb? r i substate.mem = some l → l ≤ 2 ^ 51 :=
      fun i l hl => limbBounds_readLimb? _ hsubbnd i l
        ((readLimb?_of_equiv hsubstate_eq r i).trans hl)
    have hr₂ : IsFieldElemPtr substate.mem r := by
      refine ⟨?_, hr₁.2⟩
      apply fits_equiv hsubstate_eq
      simpa using fits_splice hr₁.1

    have hsubstateWF : substate.WF := GlobalState.WF.of_equiv hsAllocWF.splice hsubstate_eq

    -- `fd_f25519_is_zero( r )`, which takes its bound in the total form
    have hrbounds : LimbBounds hr₂ := limbBounds_of_readLimb? hr₂ hrbounds?

    obtain ⟨iszerostate, hiszerostate, hiszerostate_eq⟩ :=
      fd_f25519_is_zero_conforms r substate hsubstateWF hr₂ hrbounds

    -- the frame holds only `r`, so popping it restores `s`
    have fbZero : FrameBelow s.alloc.nextFreeBlock s iszerostate :=
      FrameBelow.of_equiv hiszerostate_eq
        (FrameBelow.of_equiv hsubstate_eq (FrameBelow.splice (by omega) fb))

    refine ⟨s.popFrame iszerostate.mem, run_runFunction (s' := iszerostate) ?_,
      GlobalState.Equiv.symm (FrameBelow.popFrame_equiv hs fbZero)⟩

    denote_step_all v 0
    denote_eval v 0 0
    simp only [LLVM.const?] at hv0
    subst hv0

    refine (BlockCom.run_bind_denote_var_of_value
        (x := PoisonOr.value r) (s' := sAlloc) ?_).trans ?_
    · rw [hrdef, hsAlloc]
      simp only [denoteOp_alloca, EffectM.run_map]
      rw [run_alloca]
      rfl

    skip_lifetime

    refine (BlockCom.run_bind_denote_call_of_value
        (x := PoisonOr.value r) (s' := substate) ?_).trans ?_
    · exact hsubstate

    refine (BlockCom.run_bind_denote_call_of_value
        (x := PoisonOr.value (if readFieldElem? r substate.mem = some 0 then 1#32 else 0#32)) (s' := iszerostate) ?_).trans ?_
    · exact hiszerostate

    skip_lifetime

    simp_return

    -- the operands read the same either side of the `alloca`
    have hpv : readFieldElem hp₁ = readFieldElem hp :=
      readFieldElem_eq_of ((readFieldElem?_of_live?_eq (hlive p hp)).trans
        (Option.some_get _).symm)
    have hqv : readFieldElem hq₁ = readFieldElem hq :=
      readFieldElem_eq_of ((readFieldElem?_of_live?_eq (hlive q hq)).trans
        (Option.some_get _).symm)
    have hrval : readFieldElem? r substate.mem
        = some (readFieldElem hp - readFieldElem hq) := by
      rw [← readFieldElem?_of_equiv hsubstate_eq r, ← hpv, ← hqv, ← hsubval]
      exact (Option.some_get _).symm
    -- `fd_f25519_is_zero` tests the difference, which vanishes exactly when the
    -- two elements agree
    have hiff : (readFieldElem? r substate.mem = some 0)
        ↔ (readFieldElem hp = readFieldElem hq) := by
      rw [hrval, Option.some.injEq, sub_eq_zero]
    simp only [hiff]

end Firedancer.Ref
