module

public import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_subborrowx_u51
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_subborrowx_u51
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fiat_25519_subborrowx_u51_conforms (o₁ o₂ : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) (hs : s.WF) (h₁ : Fits s.mem o₁ 64) (h₂ : Fits s.mem o₂ 8) :
    fiat_25519_subborrowx_u51_spec o₁ o₂ c a b s := by
  simp only [fiat_25519_subborrowx_u51_spec, Cfg.denote]
  intro ha hcb hcb'
  obtain ⟨lowv, hlow⟩ :
    ∃ v : BitVec 64, v = a - (BitVec.zeroExtend 64 c + b) &&& 2251799813685247#64 := ⟨_, rfl⟩
  obtain ⟨borrowv, hborrow⟩ :
    ∃ v : BitVec 8,
      v = 0#8 - BitVec.truncate 8 ((a - (BitVec.zeroExtend 64 c + b)) >>> (51 : Nat)) :=
    ⟨_, rfl⟩
  obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState, m = (s.mem.splice o₁ lowv).splice o₂ borrowv :=
    ⟨_, rfl⟩
  refine ⟨lowv, borrowv, ?low, ?sum, ?_⟩
  case
    low =>
    rw [hlow, BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  case sum =>
    -- the 64-bit difference, in ℕ: `c + b` does not wrap, so only the
    -- subtraction can, and then by exactly `2 ^ 64`
    have hcb64 : (BitVec.zeroExtend 64 c + b).toNat = c.toNat + b.toNat := by
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
      omega
    have hd :
      (a - (BitVec.zeroExtend 64 c + b)).toNat =
        (2 ^ 64 - (c.toNat + b.toNat) + a.toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, hcb64]
    have hlo : lowv.toNat = (a - (BitVec.zeroExtend 64 c + b)).toNat % 2 ^ 51 := by
      rw [hlow, BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod]
    have hbo :
      borrowv.toNat =
        (2 ^ 8 - (a - (BitVec.zeroExtend 64 c + b)).toNat / 2 ^ 51 % 2 ^ 8) % 2 ^ 8 := by
      rw [hborrow, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]
      simp
    rcases Nat.lt_or_ge a.toNat (c.toNat + b.toNat) with hlt | hge
    · -- the subtraction wrapped: one borrow, and the limb comes back up by `2 ^ 51`
      have hD :
        (a - (BitVec.zeroExtend 64 c + b)).toNat = 2 ^ 64 - (c.toNat + b.toNat) + a.toNat := by
        rw [hd]; exact Nat.mod_eq_of_lt (by omega)
      rw [hlo, hbo, hD]
      omega
    · -- no wrap: the difference is already a limb
      have hD : (a - (BitVec.zeroExtend 64 c + b)).toNat = a.toNat - (c.toNat + b.toNat) := by
        rw [hd,
          show 2 ^ 64 - (c.toNat + b.toNat) + a.toNat = a.toNat - (c.toNat + b.toNat) + 2 ^ 64 * 1
            by omega,
          Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hlo, hbo, hD]
      omega
  rw [← houtMem]
  refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
  case
    equiv =>
    have hnone : ∀ (q : BlockId), s.alloc.nextFreeBlock ≤ q.id → outMem.live? q = none := by
      rw [houtMem]
      exact fun q hq => live?_splice_eq_none (live?_splice_eq_none (hs q hq))
    exact
      GlobalState.Equiv.symm
        (GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨rfl, rfl, fun _ => rfl⟩)
  denote_step_all v 6
  denote_eval v 0 6
  simp only [LLVM.const?] at hv0 hv1 hv2
  subst hv0 hv1 hv2
  eval_llvm 3
  eval_llvm 4
  eval_llvm 5
  eval_llvm 6
  have e6 : v6 = .value lowv := by rw [hv6, hlow]
  rw [e6]
  peel_store lowv, o₁, h₁, s
  denote_step_all v 9
  denote_eval v 7 9
  eval_llvm 7
  eval_llvm 8
  eval_llvm 9
  have e9 : v9 = .value borrowv := by
    rw [hv9, hborrow]
    exact congrArg PoisonOr.value (by bv_decide)
  rw [e9]
  peel_store borrowv, o₂, (fits_splice h₂), ({ s with mem := s.mem.splice o₁ lowv })
  simp only [BlockCom.denote_term, Terminator.denote_ret, houtMem, simp_denote, simp_sllvm]

end Firedancer.Ref
