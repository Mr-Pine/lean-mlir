import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_add
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_add
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_add
import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_carry

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 3200000 in
theorem fd_f25519_add_conforms (o p q: Pointer) (s: GlobalState)
  (hs : s.WF)
  (hpbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x8000000000000)
  (hqbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ 0x8000000000000)
  (ho : IsFieldElemPtr s.mem o)
  (hp : IsFieldElemPtr s.mem p)
  (hq : IsFieldElemPtr s.mem q) :
  fd_f25519_add_spec o p q s ho hp hq := by
    simp only [fd_f25519_add_spec, Cfg.denote]

    obtain ⟨addres, haddval, haddbounds, ⟨addstate, haddstate, haddstate_eq⟩⟩ :=
      fiat_25519_add_conforms o p q s hs hpbounds hqbounds ho hp hq

    -- the add's result in the `readLimb?`/`readFieldElem?` form
    -- `fiat_25519_carry_conforms` takes
    have haddval? : readFieldElem? o (s.mem.splice o (packLimbs addres))
        = some (readFieldElem hp + readFieldElem hq) := by
      rw [← haddval]; exact (Option.some_get _).symm
    have haddbounds? : ∀ (i : Fin 5) (l : ℕ),
        readLimb? o i (s.mem.splice o (packLimbs addres)) = some l → l ≤ 0x18000000000000 :=
      limbBounds_readLimb? (isFieldElemPtr_splice ho) haddbounds

    have haddWF : addstate.WF := GlobalState.WF.of_equiv hs.splice haddstate_eq

    have ho_addst : Fits addstate.mem o (5 * 64) := by
      apply fits_equiv haddstate_eq
      simp
      exact fits_splice ho.left

    have hoframe : o.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ho.left

    have hfield₂ : readFieldElem? o addstate.mem
        = readFieldElem? o (s.mem.splice o (packLimbs addres)) :=
      (readFieldElem?_of_equiv haddstate_eq o).symm
    have hread₂ : ∀ (i : Fin 5), readLimb? o i addstate.mem
        = readLimb? o i (s.mem.splice o (packLimbs addres)) :=
      fun i => (readLimb?_of_equiv haddstate_eq o i).symm
    have ho₁ : Fits addstate.mem o (5 * 64) := ho_addst

    obtain ⟨carryres, ⟨carrystate, hcarrystate, hcarrystate_eq⟩, hcarryres⟩ :=
      fiat_25519_carry_conforms o o addstate haddWF
        (fun i l h => haddbounds? i l ((hread₂ i).symm.trans h))
        ⟨ho₁, ho.right⟩ ⟨ho₁, ho.right⟩

    -- `addstate.alloc` is `s.alloc`, just not syntactically: both callees pop
    -- their own frame, so the counter comes back through `haddstate_eq`
    have halloc : addstate.alloc = s.alloc := haddstate_eq.1.symm

    have hcarryWF : carrystate.WF :=
      GlobalState.WF.of_equiv haddWF.splice hcarrystate_eq
    have hcalloc : carrystate.alloc = s.alloc := hcarrystate_eq.1.symm.trans halloc

    -- a read at `o` sees only the spliced bits, so splicing the carry's result
    -- into `s` and into `addstate` agree
    have hlimbs : ∀ i : Fin 5, readLimb? o i (s.mem.splice o carryres)
        = readLimb? o i (addstate.mem.splice o carryres) := fun i => by
      rw [limbSpliceReadback _ _ _ ho.left i, limbSpliceReadback _ _ _ ho₁ i]
    have hfield : readFieldElem? o (s.mem.splice o carryres)
        = readFieldElem? o (addstate.mem.splice o carryres) := by
      simp only [readFieldElem?, hlimbs]

    -- the carry hands back one 320-bit word; the spec asks for its five limbs
    have hpack : packLimbs (fun i : Fin 5 => carryres.extractLsb' (64 * i.toNat) 64) = carryres :=
      packLimbs_extractLsb' carryres

    have hpop : (s.popFrame carrystate.mem : GlobalState) ≈ carrystate :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none (fun t ht => hcarryWF t (by rw [hcalloc]; omega)))
        ⟨hcalloc.symm, haddstate_eq.globals.trans hcarrystate_eq.globals, fun _ => rfl⟩

    have hkill : (addstate : GlobalState)
        ≈ { alloc := s.alloc, mem := s.mem.splice o (packLimbs addres), globals := s.globals } :=
      GlobalState.Equiv.symm haddstate_eq

    refine ⟨fun i => carryres.extractLsb' (64 * i.toNat) 64, ?value, ?bounds,
      ⟨s.popFrame carrystate.mem, run_runFunction (s' := carrystate) ?run, ?equiv⟩⟩

    case value =>
      refine readFieldElem_eq_of ?_
      rw [hpack]
      exact hfield.trans (hcarryres.1.trans (hfield₂.trans haddval?))
    case bounds =>
      refine limbBounds_of_readLimb? _ ?_
      rw [hpack]
      exact fun i l hl => hcarryres.2.1 i l ((hlimbs i).symm.trans hl)
    case equiv =>
      rw [hpack]
      refine GlobalState.Equiv.trans ?_ (GlobalState.Equiv.symm hpop)
      refine GlobalState.Equiv.trans ?_ hcarrystate_eq
      refine GlobalState.Equiv.trans (GlobalState.Equiv.symm
        (splice_splice_equiv (s := s) (p := o) (packLimbs addres) carryres)) ?_
      exact GlobalState.Equiv.symm (splice_equiv (p := o) (x := carryres) hkill)
    case run =>
      refine (BlockCom.run_bind_denote_call_of_nil (s' := addstate) ?_).trans ?_
      · exact haddstate
      refine (BlockCom.run_bind_denote_call_of_nil (s' := carrystate) ?_).trans ?_
      · exact hcarrystate
      rfl

end Firedancer.Ref
