module

public import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_addcarryx_u51
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_addcarryx_u51
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fiat_25519_addcarryx_u51_conforms (o₁ o₂ : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) (hs : s.WF)
    (h₁ : Fits s.mem o₁ 64) (h₂ : Fits s.mem o₂ 8) :
    fiat_25519_addcarryx_u51_spec o₁ o₂ c a b s := by
  simp only [fiat_25519_addcarryx_u51_spec, Cfg.denote]
  intro hc ha hb
  obtain ⟨lowv, hlow⟩ : ∃ v : BitVec 64,
      v = BitVec.zeroExtend 64 c + a + b &&& 2251799813685247#64 := ⟨_, rfl⟩
  obtain ⟨carryv, hcarry⟩ : ∃ v : BitVec 8,
      v = BitVec.truncate 8 ((BitVec.zeroExtend 64 c + a + b) >>> (51 : Nat)) := ⟨_, rfl⟩
  obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState,
      m = (s.mem.splice o₁ lowv).splice o₂ carryv := ⟨_, rfl⟩
  refine ⟨lowv, carryv, ?low, ?sum, ?_⟩
  case low =>
    rw [hlow, BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  case sum =>
    -- at the contract the 64-bit sum does not wrap, so it *is* `c + a + b`
    have hsum : (BitVec.zeroExtend 64 c + a + b).toNat = c.toNat + a.toNat + b.toNat := by
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
      omega
    have hlo : lowv.toNat = (c.toNat + a.toNat + b.toNat) % 2 ^ 51 := by
      rw [hlow, BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod, hsum]
    -- the carry is one bit wide here, so it survives the truncation to eight
    have hco : carryv.toNat = (c.toNat + a.toNat + b.toNat) / 2 ^ 51 := by
      rw [hcarry, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        hsum]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hlo, hco]
    omega
  rw [← houtMem]
  refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
  case equiv =>
    have hnone : ∀ (q : BlockId), s.alloc.nextFreeBlock ≤ q.id → outMem.live? q = none := by
      rw [houtMem]
      exact fun q hq => live?_splice_eq_none (live?_splice_eq_none (hs q hq))
    exact GlobalState.Equiv.symm
      (GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨rfl, rfl, fun _ => rfl⟩)

  denote_step_all v 7
  denote_eval v 0 7
  simp only [LLVM.const?] at hv0 hv1
  subst hv0 hv1
  eval_llvm 2
  eval_llvm 3
  eval_llvm 4
  eval_llvm 5
  eval_llvm 6
  eval_llvm 7
  have e5 : v5 = .value lowv := by
    rw [hv5, hlow]
  have e7 : v7 = .value carryv := by
    rw [hv7, hcarry]
    exact congrArg PoisonOr.value (by bv_decide)
  rw [e5, e7]
  peel_store lowv, o₁, h₁, s
  peel_store carryv, o₂, (fits_splice h₂), ({ s with mem := s.mem.splice o₁ lowv })
  simp only [BlockCom.denote_term, Terminator.denote_ret, houtMem, simp_denote, simp_sllvm]

end Firedancer.Ref
