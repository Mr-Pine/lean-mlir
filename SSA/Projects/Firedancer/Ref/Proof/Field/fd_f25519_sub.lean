import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_sub
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sub
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_sub
import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_carry

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 3200000 in
theorem fd_f25519_sub_conforms (o p q: Pointer) (s: GlobalState)
  (hs : s.WF)
  (hpbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x8000000000000)
  (hqbounds : BiasBounds? q s.mem)
  (ho : IsFieldElemPtr s.mem o)
  (hp : IsFieldElemPtr s.mem p)
  (hq : IsFieldElemPtr s.mem q) :
  fd_f25519_sub_spec o p q s ho hp hq := by
    simp only [fd_f25519_sub_spec, Cfg.denote]

    obtain ⟨subres, hsubval, hsubbnd, substate, hsubstate, hsubstate_eq⟩ :=
      fiat_25519_sub_conforms o p q s hs hpbounds hqbounds ho hp hq
    -- the callee states its result as a readback; the walk below runs on the
    -- proof-free forms, so take them once here
    have hsubval? : readFieldElem? o substate.mem = some (readFieldElem hp - readFieldElem hq) := by
      rw [← readFieldElem?_of_equiv hsubstate_eq o, ← hsubval]
      exact (Option.some_get _).symm
    have hsubbnd? : ∀ (i : Fin 5) (l : ℕ),
        readLimb? o i substate.mem = some l → l ≤ 0x18000000000000 :=
      fun i l hl => limbBounds_readLimb? _ hsubbnd i l
        ((readLimb?_of_equiv hsubstate_eq o i).trans hl)
    have ho_subst : Fits substate.mem o (5 * 64) := by
      apply fits_equiv hsubstate_eq
      simp
      exact fits_splice ho.left

    have hoframe : o.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ho.left

    have hsubWF : substate.WF := GlobalState.WF.of_equiv hs.splice hsubstate_eq
    have halloc : substate.alloc = s.alloc := hsubstate_eq.1.symm

    obtain ⟨carryres, ⟨carrystate, hcarrystate, hcarrystate_eq⟩, hcarryres⟩ :=
      fiat_25519_carry_conforms o o substate hsubWF hsubbnd? ⟨ho_subst, ho.right⟩
        ⟨ho_subst, ho.right⟩

    have hcarryWF : carrystate.WF :=
      GlobalState.WF.of_equiv hsubWF.splice hcarrystate_eq
    have hcalloc : carrystate.alloc = s.alloc := hcarrystate_eq.1.symm.trans halloc
    have hcglobals : s.globals = carrystate.globals :=
      hsubstate_eq.globals.trans hcarrystate_eq.globals

    have hpop : (s.popFrame carrystate.mem : GlobalState) ≈ carrystate :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none (fun t ht => hcarryWF t (by rw [hcalloc]; omega)))
        ⟨hcalloc.symm, hcglobals, fun _ => rfl⟩

    -- a read at `o` sees only the spliced bits, so splicing the carry's result
    -- into `s` and into `substate` agree
    have hlimbs : ∀ i : Fin 5, readLimb? o i (s.mem.splice o carryres)
        = readLimb? o i (substate.mem.splice o carryres) := fun i => by
      rw [limbSpliceReadback _ _ _ ho.left i, limbSpliceReadback _ _ _ ho_subst i]
    have hfield : readFieldElem? o (s.mem.splice o carryres)
        = readFieldElem? o (substate.mem.splice o carryres) := by
      simp only [readFieldElem?, hlimbs]

    have hkill : (substate : GlobalState)
        ≈ { alloc := s.alloc, mem := s.mem.splice o subres, globals := s.globals } :=
      GlobalState.Equiv.symm hsubstate_eq

    refine ⟨carryres, ?value, ?bounds, s.popFrame carrystate.mem,
      run_runFunction (s' := carrystate) ?run, ?equiv⟩

    case equiv =>
      refine GlobalState.Equiv.trans ?_ (GlobalState.Equiv.symm hpop)
      refine GlobalState.Equiv.trans ?_ hcarrystate_eq
      refine GlobalState.Equiv.trans (GlobalState.Equiv.symm
        (splice_splice_equiv (s := s) (p := o) subres carryres)) ?_
      exact GlobalState.Equiv.symm (splice_equiv (p := o) (x := carryres) hkill)
    case value =>
      exact readFieldElem_eq_of (hfield.trans (hcarryres.1.trans hsubval?))
    case bounds =>
      exact limbBounds_of_readLimb? _ fun i l hl => hcarryres.2 i l ((hlimbs i).symm.trans hl)
    case run =>
      refine (BlockCom.run_bind_denote_call_of_nil (s' := substate) ?_).trans ?_
      · exact hsubstate
      refine (BlockCom.run_bind_denote_call_of_nil (s' := carrystate) ?_).trans ?_
      · exact hcarrystate
      rfl

end Firedancer.Ref
