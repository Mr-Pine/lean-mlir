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
  (hqbounds : LimbBounds hq) :
  fd_f25519_eq_spec p q s := by
    simp only [fd_f25519_eq_spec, Cfg.denote]

    obtain ⟨r, sAlloc, hrdef, hsAlloc⟩ := GlobalState.exists_afterAlloca s (5 * 64)
    -- the fresh block is 40 zero bytes at offset 0: exactly one field element.
    have hr₁ : IsFieldElemPtr sAlloc.mem r := by
      subst hrdef hsAlloc; exact isFieldElemPtr_afterAlloca_self s
    -- a pointer live in `s` predates the frame, so the fresh block's id is not
    -- its own and the insert leaves it alone: `p` and `q` read as they did.
    have hlive : ∀ t : Pointer, IsFieldElemPtr s.mem t →
        sAlloc.mem.live? t.id = s.mem.live? t.id := by
      subst hsAlloc; exact fun t ht => live?_afterAlloca_of_fits hs _ ht.left
    have hframe : ∀ t : Pointer, IsFieldElemPtr s.mem t → IsFieldElemPtr sAlloc.mem t :=
      fun t ht => isFieldElemPtr_of_live?_eq (hlive t ht) ht
    have hp₁ : IsFieldElemPtr sAlloc.mem p := hframe p hp
    have hq₁ : IsFieldElemPtr sAlloc.mem q := hframe q hq
    have hsAllocWF : sAlloc.WF := by subst hsAlloc; exact hs.afterAlloca _

    have hpbounds₁ : ∀ (i : Fin 5) (l : ℕ), readLimb? p i sAlloc.mem = some l → l ≤ 0x8000000000000 :=
      fun i l hl => limbBounds_readLimb? hp hpbounds i l (by simpa [readLimb?, hlive p hp] using hl)
    have hqbounds₁ : ∀ (i : Fin 5) (l : ℕ), readLimb? q i sAlloc.mem = some l → l ≤ 0x8000000000000 :=
      fun i l hl => limbBounds_readLimb? hq hqbounds i l (by simpa [readLimb?, hlive q hq] using hl)

    obtain ⟨subres, ⟨substate, hsubstate, hsubstate_eq⟩, hsubres⟩ := fd_f25519_sub_conforms r p q sAlloc hsAllocWF hpbounds₁ hqbounds₁ hr₁ hp₁ hq₁

    have hrbounds? : ∀ (i : Fin 5) (l : ℕ), readLimb? r i substate.mem = some l → l ≤ 2 ^ 51 := by
      simp at hsubres
      simp [← readLimb?_of_equiv hsubstate_eq]
      intro i
      intro l
      exact hsubres.right i l
    have hr₂ : IsFieldElemPtr substate.mem r := by
      refine ⟨?_, hr₁.2⟩
      apply fits_equiv hsubstate_eq
      simpa using fits_splice hr₁.1

    -- the sub only spliced at `r`, which is *below* `sAlloc`'s counter, so
    -- nothing at or above it became live.
    have hsubstateWF : substate.WF := by
      have halloc : sAlloc.alloc = substate.alloc := hsubstate_eq.1
      intro t ht
      rw [← halloc] at ht
      rw [← hsubstate_eq.2 t]
      grind [live?_splice_ne, GlobalState.afterAlloca, hsAllocWF t ht]

    -- and `fd_f25519_is_zero` in the total form
    have hrbounds : LimbBounds hr₂ := limbBounds_of_readLimb? hr₂ hrbounds?

    obtain ⟨iszerostate, hiszerostate, hiszerostate_eq⟩ :=
      fd_f25519_is_zero_conforms r substate hsubstateWF hr₂ hrbounds

    refine ⟨s.popFrame iszerostate.mem, run_runFunction (s' := iszerostate) ?_, ?_⟩
    case refine_2 =>
      refine GlobalState.Equiv.symm ((GlobalState.killFrom_equiv iszerostate.mem hs) ?_)
      intro t ht
      have hne : r.id ≠ t := by
        grind only
      rw [← hiszerostate_eq.2 t, ← hsubstate_eq.2 t]
      grind only [GlobalState.afterAlloca, MemoryState.live?, MemoryState.getElem?_eq,
        Std.HashMap.getElem?_insert, live?_splice_ne]

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

    simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]
    have hpval : readFieldElem? p sAlloc.mem = readFieldElem? p s.mem := by
      simp only [readFieldElem?, readLimb?, hlive p hp]
    have hqval : readFieldElem? q sAlloc.mem = readFieldElem? q s.mem := by
      simp only [readFieldElem?, readLimb?, hlive q hq]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (readFieldElem?_isSome hp)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (readFieldElem?_isSome hq)
    have hrval : readFieldElem? r substate.mem = some (x - y) := by
      rw [← readFieldElem?_of_equiv hsubstate_eq r, hsubres.1, hpval, hqval, hx, hy]
      rfl
    grind only [readFieldElem?, readFieldElem?_of_equiv]

end Firedancer.Ref
