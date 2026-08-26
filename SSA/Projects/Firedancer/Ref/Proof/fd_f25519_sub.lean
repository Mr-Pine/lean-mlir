import SSA.Projects.Firedancer.Ref.Spec.fd_f25519_sub
import SSA.Projects.Firedancer.Ref.Mlir.fd_f25519_sub
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.fiat_25519_sub
import SSA.Projects.Firedancer.Ref.Proof.fiat_25519_carry

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 3200000 in
theorem fd_f25519_sub_conforms (o p q: Pointer) (s: GlobalState)
  (hs : s.WF)
  (hpbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x8000000000000)
  (hqbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ 0x8000000000000)
  (ho : Fits s.mem o (5 * 64))
  (ho' : o.offset.toNat + 40 ≤ 2 ^ 64)
  (hp : Fits s.mem p (5 * 64))
  (hp' : p.offset.toNat + 40 ≤ 2 ^ 64)
  (hq : Fits s.mem q (5 * 64))
  (hq' : q.offset.toNat + 40 ≤ 2 ^ 64) :
  fd_f25519_sub_spec o p q s := by
    simp only [fd_f25519_sub_spec, Cfg.denote]

    obtain ⟨subres, ⟨substate, hsubstate, hsubstate_eq⟩, hsubres⟩ :=
      fiat_25519_sub_conforms o p q s hpbounds hqbounds ho ho' hp hp' hq hq'
    replace hsubres : readFieldElem? o substate.mem
          = Sub.sub <$> readFieldElem? p s.mem <*> readFieldElem? q s.mem
        ∧ ∀ (i : Fin 5) (l : ℕ), readLimb? o i substate.mem = some l → l ≤ 0x18000000000000 :=
      ⟨(readFieldElem?_of_equiv hsubstate_eq o).symm.trans hsubres.1,
       fun i l hl => hsubres.2 i l ((readLimb?_of_equiv hsubstate_eq o i).trans hl)⟩
    have ho_subst : Fits substate.mem o (5 * 64) := by
      apply fits_equiv hsubstate_eq
      simp
      exact fits_splice ho

    -- `o` addresses a live block, so by well-formedness it predates the frame:
    -- neither call's frame kill can touch it.
    have hoframe : o.id.id < s.alloc.nextFreeBlock := by
      obtain ⟨blk, hblk, -⟩ := id ho
      by_contra hcon
      have hnone := hs o.id (by omega)
      simp [MemoryState.live?, hblk] at hnone

    -- the state the `fiat_25519_sub` call returns to, its frame popped: this,
    -- not `substate`, is where `fiat_25519_carry` actually runs. Popping the
    -- frame is invisible -- below the counter `killFrom` is the identity, above
    -- it well-formedness says nothing was live -- so the two are equivalent and
    -- everything known about `substate` transfers.
    set substate' : GlobalState :=
      { alloc := s.alloc, mem := substate.mem.killFrom s.alloc.nextFreeBlock } with hsubstate'def
    have hsubstate'_eq : (substate' : GlobalState) ≈ substate := by
      refine ⟨hsubstate_eq.1, fun r => ?_⟩
      by_cases hr : r.id < s.alloc.nextFreeBlock
      · exact live?_killFrom_of_lt hr
      · rw [live?_killFrom_of_le (by omega), ← hsubstate_eq.2 r,
          live?_splice_ne (show o.id ≠ r by rintro rfl; omega), hs r (by omega)]
    have hread₁ : ∀ (i : Fin 5), readLimb? o i substate'.mem = readLimb? o i substate.mem :=
      readLimb?_of_equiv hsubstate'_eq o
    have hfield₁ : readFieldElem? o substate'.mem = readFieldElem? o substate.mem :=
      readFieldElem?_of_equiv hsubstate'_eq o
    have ho₁ : Fits substate'.mem o (5 * 64) :=
      fits_equiv (GlobalState.Equiv.symm hsubstate'_eq) ho_subst

    obtain ⟨carryres, ⟨carrystate, hcarrystate, hcarrystate_eq⟩, hcarryres⟩ :=
      fiat_25519_carry_conforms o o substate'
        (fun i l h => hsubres.2 i l ((hread₁ i).symm.trans h)) ho₁ ho₁ ho' ho'

    -- and the state the `fiat_25519_carry` call returns to, which is what the
    -- region as a whole ends in
    set carrystate' : GlobalState :=
      { alloc := s.alloc, mem := carrystate.mem.killFrom s.alloc.nextFreeBlock }
      with hcarrystate'def

    refine ⟨carryres, ⟨carrystate', ?_⟩, ?_⟩
    pick_goal 2

    -- the spec splices `carryres` into `s`, the carry into `substate'`; a read at `o`
    -- sees only the spliced bits, so the two agree.
    have hlimbs : ∀ i : Fin 5, readLimb? o i (s.mem.splice o carryres)
        = readLimb? o i (substate'.mem.splice o carryres) := fun i => by
      rw [limbSpliceReadback _ _ _ ho i, limbSpliceReadback _ _ _ ho₁ i]
    have hfield : readFieldElem? o (s.mem.splice o carryres)
        = readFieldElem? o (substate'.mem.splice o carryres) := by
      simp only [readFieldElem?, hlimbs]
    exact ⟨hfield.trans (hcarryres.1.trans (hfield₁.trans hsubres.1)),
      fun i l hl => hcarryres.2 i l ((hlimbs i).symm.trans hl)⟩

    constructor
    case refine_1.right =>
      have hkill : (substate' : GlobalState)
          ≈ { alloc := s.alloc, mem := s.mem.splice o subres } :=
        GlobalState.Equiv.trans hsubstate'_eq (GlobalState.Equiv.symm hsubstate_eq)
      -- popping the carry's frame is invisible for the same reason
      have hkill₂ : (carrystate' : GlobalState) ≈ carrystate := by
        refine ⟨hcarrystate_eq.1, fun r => ?_⟩
        by_cases hr : r.id < s.alloc.nextFreeBlock
        · exact live?_killFrom_of_lt hr
        · rw [live?_killFrom_of_le (by omega), ← hcarrystate_eq.2 r,
            live?_splice_ne (show o.id ≠ r by rintro rfl; omega),
            live?_killFrom_of_le (by omega)]
      -- the sub's splice at `o` is overwritten by the carry's
      exact GlobalState.Equiv.trans
        (GlobalState.Equiv.trans
          (GlobalState.Equiv.trans
            (GlobalState.Equiv.symm (splice_splice_equiv (s := s) (p := o) subres carryres))
            (GlobalState.Equiv.symm (splice_equiv (p := o) (x := carryres) hkill)))
          hcarrystate_eq)
        (GlobalState.Equiv.symm hkill₂)

    refine (BlockCom.run_bind_denote_call_of_nil (s' := substate') ?_).trans ?_
    · exact run_runFunction hsubstate

    refine (BlockCom.run_bind_denote_call_of_nil (s' := carrystate') ?_).trans ?_
    · exact run_runFunction hcarrystate

    rfl

end Firedancer.Ref
