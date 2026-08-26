import SSA.Projects.Firedancer.Ref.Spec.fd_f25519_is_zero
import SSA.Projects.Firedancer.Ref.Mlir.fd_f25519_is_zero
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations


namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Base-`2^51` digits that sum to a multiple of `p` are one of exactly two
patterns: all zero, or the limbs of `p` itself. The sum is below `2p`, so it is
`0` or `p` on the nose, and digits below `2^51` then pin every limb. -/
private lemma limbs_of_dvd {l0 l1 l2 l3 l4 : ℕ}
    (h0 : l0 < 2^51) (h1 : l1 < 2^51) (h2 : l2 < 2^51) (h3 : l3 < 2^51) (h4 : l4 < 2^51)
    (h : p ∣ (l0 + l1 * 2^51 + l2 * 2^102 + l3 * 2^153 + l4 * 2^204)) :
    (l0 = 0 ∧ l1 = 0 ∧ l2 = 0 ∧ l3 = 0 ∧ l4 = 0)
  ∨ (l0 = 0x7ffffffffffed ∧ l1 = 0x7ffffffffffff ∧ l2 = 0x7ffffffffffff
      ∧ l3 = 0x7ffffffffffff ∧ l4 = 0x7ffffffffffff) := by
  obtain ⟨k, hk⟩ := h
  norm_num [p] at h0 h1 h2 h3 h4 hk ⊢
  -- `k = 0` gives the all-zero limbs, `k = 1` the `p` pattern; `k ≥ 2` exceeds
  -- the largest sum five digits below `2^51` can reach.
  rcases k with _ | _ | k <;> omega

/-- The field element a pointer addresses is `0` exactly when its limbs are one
of the two representations of zero: all zero, or the limbs of `p` itself. The
limb bound is needed only left-to-right -- any limbs at all that *are* one of
the two patterns decode to `0`. -/
private lemma readFieldElem_eq_zero_iff (p : Pointer) (m : MemoryState)
    (hp : Fits m p (5 * 64))
    (hlimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i m = some l → l < 2 ^ 51) :
    readFieldElem? p m = .some 0
      ↔ (∀ i : Fin 5, readLimb? p i m = .some 0)
      ∨ (∀ i : Fin 5, readLimb? p i m = .some (match i with
          | 0 => 0x7ffffffffffed
          | _ => 0x7ffffffffffff)) := by
  obtain ⟨blk, hblk, hlen⟩ := hp
  -- One opaque handle for all five limbs. `e` is an existential witness, so no
  -- later `simp` can unfold it back into `extractLsb'`.
  obtain ⟨e, he⟩ : ∃ e : Fin 5 → ℕ, ∀ i, readLimb? p i m = some (e i) :=
    ⟨fun i => (blk.bytes.extractLsb' (p.offsetInBits + 64 * i.toNat) 64).toNat,
      fun i => by simp [readLimb?, MemoryState.live?, hblk]⟩
  simp only [readFieldElem?, he 0, he 1, he 2, he 3, he 4, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq]
  constructor
  · -- `= 0` in `ZMod p` is divisibility by `p` on the underlying natural.
    intro hzero
    have hdvd : _root_.p ∣ (e 0 + e 1 * 2^51 + e 2 * 2^102 + e 3 * 2^153 + e 4 * 2^204) :=
      (ZMod.natCast_eq_zero_iff _ _).mp (by simpa [decodeFieldElem] using hzero)
    rcases limbs_of_dvd (hlimb 0 _ (he 0)) (hlimb 1 _ (he 1)) (hlimb 2 _ (he 2))
        (hlimb 3 _ (he 3)) (hlimb 4 _ (he 4)) hdvd with
      ⟨r0, r1, r2, r3, r4⟩ | ⟨r0, r1, r2, r3, r4⟩
    · exact Or.inl fun i => by fin_cases i <;> simp_all
    · exact Or.inr fun i => by fin_cases i <;> simp_all
  · rintro (h | h) <;>
      have r := fun i => Option.some.inj ((he i).symm.trans (h i))
    · simp [decodeFieldElem, r]
    · -- these limbs sum to `p` on the nose
      have hp0 : ((0x7ffffffffffed + 0x7ffffffffffff * 2^51 + 0x7ffffffffffff * 2^102
          + 0x7ffffffffffff * 2^153 + 0x7ffffffffffff * 2^204 : ℕ) : ZMod _root_.p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (by norm_num [_root_.p])
      simpa [decodeFieldElem, r] using hp0

open Lean Elab Tactic
elab "read_limb " i:num ", " p:term ", " hp:term ", " st:term : tactic => do
  let num := i.getNat
  -- `peel_gep` counts bytes; `offsetInBits` counts bits
  let offBits := Syntax.mkNumLit (toString (num * 64))
  let n ← nextStepIndex (← getMainGoal)
  let nIcmpLit := Syntax.mkNumLit (toString (n + 2))

  let vBase := mkIdent (Name.mkSimple "v")
  let hv' := mkIdent (Name.mkSimple ("hv" ++ (toString (n + 2))))

  let s := subscript i.getNat
  let ptr := mkIdent (Name.mkSimple ("p" ++ s))
  let hptr := mkIdent (Name.mkSimple ("hp" ++ s))

  let limb := mkIdent (Name.mkSimple ("limb" ++ s))
  let hlimb := mkIdent (Name.mkSimple ("hlimb" ++ s))

  let hread := mkIdent (Name.mkSimple ("hread" ++ s))
  let baseHread := mkIdent (Name.mkSimple "hread")

  evalTactic (← `(tactic| peel_gep $i, $p, $hp, $st, p))
  let baseblk := mkIdent (Name.mkSimple "blk")
  let basehblk := mkIdent (Name.mkSimple "hblk")
  evalTactic (← `(tactic| peel_limb $i, $ptr, $hptr, $baseblk, $basehblk))
  evalTactic (← `(tactic| have hoff : ($ptr).offsetInBits = ($p).offsetInBits + ($offBits) := by
        have hlt : ($p).offset.toNat < 2 ^ 64 := ($p).offset.isLt
        simp [$ptr:ident, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add]
        omega))
  evalTactic (← `(tactic| have $hread:ident : readLimb? $p $i ($st).mem = some ($limb).toNat := by
        rw [$hlimb:ident, hoff]
        simpa using $baseHread $i))
  evalTactic (← `(tactic| denote_step_all $vBase $nIcmpLit))
  evalTactic (← `(tactic| denote_eval $vBase $nIcmpLit $nIcmpLit))
  evalTactic (← `(tactic| simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', simp_sllvm] at $hv':ident))
  evalTactic (← `(tactic| subst $hv'))
  evalTactic (← `(tactic| clear hoff))

open Lean Elab Tactic
elab "discharge_bad_case " i:num ", " target:num ", " caseH:ident ", " hlz:ident ", " hreadz:ident ", " st:term ", " limb0:term ", " p:term ", " hp:term ", " hlimb:term : tactic => do
  let s := subscript i.getNat

  let limb := mkIdent (Name.mkSimple ("limb" ++ s))
  let hl := mkIdent (Name.mkSimple ("hl" ++ s))
  let hread := mkIdent (Name.mkSimple ("hread" ++ s))

  let nonTargetZ := Syntax.mkNumLit (toString (if (target.getNat = 0) then 0x7ffffffffffed else 0))

  evalTactic (← `(tactic| have e : ($limb == BitVec.ofNat 64 $target) = false := by simp [$caseH:ident]))
  evalTactic (← `(tactic| simp [e, $caseH:ident, BlockCom.denote_term,
          Terminator.denote_condBr_value, Ctxt.Valuation.cons_last, simp_denote, simp_sllvm]))
  evalTactic (← `(tactic| clear e))
  evalTactic (← `(tactic| (
    denote_enter_block
    simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
    denote_enter_block
    simp only [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]
    simp [Ctxt.Valuation.singleton, simp_sllvm]
  )))
  evalTactic (← `(tactic| intro hzero))
  if target.getNat = 0 then
    evalTactic (← `(tactic| (
      rcases (readFieldElem_eq_zero_iff $p ($st).mem ($hp) ($hlimb)).mp hzero with h | h
      · have h' := h $i
        rw [($hread:ident), Option.some_inj] at h'
        rw [← BitVec.toNat_inj] at $hl:ident
        simp at $hl:ident
        exact $hl h'
      · have h0 : ($limb0) = BitVec.ofNat 64 $nonTargetZ := by
          simpa [← BitVec.toNat_inj] using Option.some.inj (($hreadz:ident).symm.trans (h 0))
        simp [$hlz:ident] at h0)))
  else
    evalTactic (← `(tactic| (
      rcases (readFieldElem_eq_zero_iff $p ($st).mem ($hp) ($hlimb)).mp hzero with h | h
      · have h0 : ($limb0) = BitVec.ofNat 64 $nonTargetZ := by
          simpa [← BitVec.toNat_inj] using Option.some.inj (($hreadz:ident).symm.trans (h 0))
        simp [$hlz:ident] at h0
      · have h' := h $i
        rw [($hread:ident), Option.some_inj] at h'
        rw [← BitVec.toNat_inj] at $hl:ident
        simp at $hl:ident
        exact $hl h')))

open Lean Elab Tactic
elab "discharge_bad " i:num "@" target:num " with " p:term ", " hp:ident ", " st:term ", " hlimb:ident " and " limbz:ident ", " hlz:ident ", " hreadz:ident : tactic => do
  evalTactic (← `(tactic| read_limb $i, $p, $hp, $st))

  let s := subscript i.getNat
  let hl := mkIdent (Name.mkSimple ("hl" ++ s))
  let hread := mkIdent (Name.mkSimple ("hread" ++ s))
  let limb := mkIdent (Name.mkSimple ("limb" ++ s))

  evalTactic (← `(tactic| by_cases $hl:ident : $limb = BitVec.ofNat 64 $target))
  evalTactic (← `(tactic| (case neg =>
        discharge_bad_case $i, $target, $hl, $hlz, $hreadz, $st, $limbz, $p, $hp, $hlimb)))
  evalTactic (← `(tactic| have e : ($limb == (BitVec.ofNat 64 $target)) = true := by simp [$hl:ident]))
  evalTactic (← `(tactic| rw [e]))
  evalTactic (← `(tactic| clear e))
  evalTactic (← `(tactic| simp [BlockCom.denote_term, Terminator.denote_condBr_value,
        Ctxt.Valuation.cons_last, simp_denote, simp_sllvm]))
  evalTactic (← `(tactic| rw [$hl:ident] at $hread:ident))


set_option maxHeartbeats 400000 in
theorem fd_f25519_is_zero_conforms (p: Pointer) (s: GlobalState)
  (hp : Fits s.mem p (5 * 64))
  (hlimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l < 2 ^ 51)
  -- The five limbs do not straddle the end of the address space, so the region's
  -- geps do not wrap. `Fits` cannot give this: it bounds `p.offset` only against
  -- `blk.length`, which is an unbounded `ℕ`.
  (hnw : p.offset.toNat + 40 ≤ 2 ^ 64) :
  fd_f25519_is_zero_spec p s := by
    -- Split the region into the entry block and the dispatch on its terminator.
    simp only [fd_f25519_is_zero_spec, Cfg.denote]
    -- No store runs, so the final state is `s` itself; `≈` is reflexive.
    refine ⟨s, ?_, GlobalState.Equiv.refl s⟩
    -- `^bb0`, up to the load at `%8`: the eight compare constants.
    denote_step_all v 7
    denote_eval v 0 7
    simp only [LLVM.const?] at hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7
    subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7

    obtain ⟨blk, hblk, hlen⟩ := id hp   -- `id` so `hp` survives for the lemma

    peel_limb 0, p, hp, blk, hblk

    -- Bridge from the block bytes the region loads to the `readLimb?` the spec
    -- reads; all three arms need it to build `badLimbMakesNonzero`'s witness.
    have hread : ∀ j : Fin 5,
        readLimb? p j s.mem
          = some ((blk.bytes.extractLsb' (p.offsetInBits + 64 * j.toNat) 64).toNat) :=
      fun j => by simp [readLimb?, MemoryState.live?, hblk]
    have hread₀ : readLimb? p 0 s.mem = some limb₀.toNat := by
      rw [hlimb₀]
      simpa using hread 0

    simp only [BlockCom.denote_term, Terminator.denote_switch_value,
      Ctxt.Valuation.cons_last, simp_denote, simp_sllvm]

    by_cases hl₀ : limb₀ = 0#64
    case pos =>
      have e0 : (0#64 == limb₀) = true := by simp [hl₀]
      simp [e0]

      denote_enter_block
      discharge_bad 1@0 with p, hp, s, hlimb and limb₀, hl₀, hread₀

      denote_enter_block
      discharge_bad 2@0 with p, hp, s, hlimb and limb₀, hl₀, hread₀

      denote_enter_block
      discharge_bad 3@0 with p, hp, s, hlimb and limb₀, hl₀, hread₀

      denote_enter_block
      discharge_bad 4@0 with p, hp, s, hlimb and limb₀, hl₀, hread₀

      denote_enter_block
      simp only [BlockCom.denote_term, Terminator.denote_ret,
        Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      simp [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append,
        Ctxt.Valuation.cons_last, simp_denote, simp_sllvm]

      rw [hl₀] at hread₀
      rw [readFieldElem_eq_zero_iff p s.mem hp hlimb]
      left
      intro i
      fin_cases i <;> simp [hread₀, hread₁, hread₂, hread₃, hread₄]
    case neg =>
      by_cases hl₀' : limb₀ = 0x7ffffffffffed#64
      case pos =>
        -- `find?` walks the list head-first, so it needs the *0* comparison too.
        have e0 : (0#64 == limb₀) = false := by simp [Ne.symm hl₀]
        have e1 : (0x7ffffffffffed#64 == limb₀) = true := by simp [hl₀']
        simp [e0, e1]

        denote_enter_block
        discharge_bad 1@0x7ffffffffffff with p, hp, s, hlimb and limb₀, hl₀, hread₀

        denote_enter_block
        discharge_bad 2@0x7ffffffffffff with p, hp, s, hlimb and limb₀, hl₀, hread₀

        denote_enter_block
        discharge_bad 3@0x7ffffffffffff with p, hp, s, hlimb and limb₀, hl₀, hread₀

        denote_enter_block
        discharge_bad 4@0x7ffffffffffff with p, hp, s, hlimb and limb₀, hl₀, hread₀

        denote_enter_block
        simp only [BlockCom.denote_term, Terminator.denote_ret,
          Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        simp [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append,
          Ctxt.Valuation.cons_last, simp_denote, simp_sllvm]

        rw [hl₀'] at hread₀
        rw [readFieldElem_eq_zero_iff p s.mem hp hlimb]
        right
        intro i
        fin_cases i <;> simp [hread₀, hread₁, hread₂, hread₃, hread₄]
      case neg =>
        simp [Ne.symm hl₀, Ne.symm hl₀']
        denote_enter_block
        simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
        denote_enter_block
        simp only [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]
        simp [Ctxt.Valuation.singleton, simp_sllvm]
        -- Either pattern would force limb 0 to a value the switch already ruled
        -- out; `hread0` carries the comparison over to `readLimb?`.
        intro hzero
        rcases (readFieldElem_eq_zero_iff p s.mem hp hlimb).mp hzero with h | h
        · exact hl₀ (by simpa [← BitVec.toNat_inj] using Option.some.inj (hread₀.symm.trans (h 0)))
        · exact hl₀' (by simpa [← BitVec.toNat_inj] using Option.some.inj (hread₀.symm.trans (h 0)))

end Firedancer.Ref
