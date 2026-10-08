import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreValues
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreLater
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreFirstArithmetic

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.FiredancerSHAExecution.Core (Ring ringWord)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Both overflow flags hold throughout the finite scalar schedule loop. -/
private theorem index_add (r k : Nat) (hr : r < 80) (hk : k ≤ 14) :
    LLVM.add (.value (BitVec.ofNat 64 r)) (.value (BitVec.ofNat 64 k))
      {nsw := true, nuw := true} = .value (BitVec.ofNat 64 (r+k)) := by
  have h := Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ring_index_add r k hr hk
  by_cases hs : (BitVec.ofNat 64 r).saddOverflow (BitVec.ofNat 64 k) = true
  · simp [LeanMLIR.RIR.Operation.add, hs] at h
    cases h
  by_cases hu : (BitVec.ofNat 64 r).uaddOverflow (BitVec.ofNat 64 k) = true
  · simp [LeanMLIR.RIR.Operation.add, hs, hu] at h
    cases h
  simp [LLVM.add, LLVM.add?, hs, hu, ← BitVec.ofNat_add]

private theorem later_fshl63 (x : Word) : fshlBV x x 63#64 = x.rotateRight 1 := rotateRight1_fshl x
private theorem later_fshl56 (x : Word) : fshlBV x x 56#64 = x.rotateRight 8 := rotateRight8_fshl x
private theorem later_fshl45 (x : Word) : fshlBV x x 45#64 = x.rotateRight 19 := rotateRight19_fshl x
private theorem later_fshl3 (x : Word) : fshlBV x x 3#64 = x.rotateRight 61 := rotateRight61_fshl x

def laterMemory (m : MemoryState) (stack : Pointer) (q : Ring) (i : Nat) : MemoryState :=
  m.splice (stack.withOffset (BitVec.ofNat 64 (8 * (i % 16)))) (ringWord q i)

def laterNext (initial work : State) (data : Pointer) (count : Word)
    (q : Ring) (i : Nat) (constant : Word) : SuccArgs core.cfgSigs :=
  let next := laterRound work (ringWord q i) constant
  if i + 1 = 80 then feedforwardTarget initial next data count
  else laterTarget initial next data count (i+1)

/-- Execute the imported bb3, including all four ring loads, the ring write,
constant-table load, SHA round, and its actual conditional successor. -/
theorem later_body {α : Type} (kp chain stack originalData data : Pointer)
    (originalCount count : Word) (original initial work : State)
    (q : Ring) (i : Nat) (constant : Word) (before : GlobalState)
    (hi : i < 80) (hs : SmallRange before.mem stack 128)
    (hk : SmallRange before.mem kp 640) (hne : stack.id ≠ kp.id)
    (hread : ∀ j, j < 16 → readBits before.mem
      (stack.withOffset (BitVec.ofNat 64 (8*j))) 64 = q j)
    (hkread : readBits before.mem (kp.withOffset (BitVec.ofNat 64 (8*i))) 64 = constant)
    (k : HVector TyDenote.toType [] ⊕ SuccArgs core.cfgSigs → SLLVM.m α) :
    StateT.run (core.cfgBlock_2.denote
      (blockInput (laterTarget initial work data count i)
        (ambient kp chain stack originalData originalCount original)) >>= fun (_, jump) => k jump)
      before =
    StateT.run (k (.inr (laterNext initial work data count q i constant)))
      {before with mem := laterMemory before.mem stack q i} := by
  unfold blockInput laterTarget ambient
  denote_expose
  denote_number_from 106
  denote_step_all v 108
  denote_eval v 106 108
  rw [index_add i 1 hi (by decide)] at hv106
  subst v106
  have hm1 := Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ring_index_mask (i+1) (by omega)
  simp [LLVM.and, LLVM.and?, hm1] at hv107
  subst v107
  have hgep : v108 = .value (stack.withOffset (BitVec.ofNat 64 (8*((i+1)%16)))) := by
    simp [hv108, gep, ptradd, LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?,
      LLVM.const?, Pointer.withOffset, ← BitVec.ofNat_mul, BitVec.mul_comm, Nat.mul_comm]
  clear hv108
  subst v108
  have hf1 : Fits before.mem (stack.withOffset (BitVec.ofNat 64 (8*((i+1)%16)))) 64 :=
    (hs.add (k := 8*((i+1)%16)) (n := 8) (by omega)).fits
  rw [BlockCom.run_bind_denote_var_of_value (x := (PoisonOr.value (q ((i+1)%16)) : LLVM.IntW 64)) (s' := before)
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      rw [run_liftM (run_load_readBits hf1), hread ((i+1)%16) (by omega)]
      rfl)]
  denote_step_all v 112
  denote_eval v 110 112
  rw [index_add i 14 hi (by decide)] at hv110
  subst v110
  have hm14 := Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ring_index_mask (i+14) (by omega)
  simp [LLVM.and, LLVM.and?, hm14] at hv111
  subst v111
  have hgep : v112 = .value (stack.withOffset (BitVec.ofNat 64 (8*((i+14)%16)))) := by
    simp [hv112, gep, ptradd, LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?,
      LLVM.const?, Pointer.withOffset, ← BitVec.ofNat_mul, BitVec.mul_comm, Nat.mul_comm]
  clear hv112
  subst v112
  have hf14 : Fits before.mem (stack.withOffset (BitVec.ofNat 64 (8*((i+14)%16)))) 64 :=
    (hs.add (k := 8*((i+14)%16)) (n := 8) (by omega)).fits
  rw [BlockCom.run_bind_denote_var_of_value (x := (PoisonOr.value (q ((i+14)%16)) : LLVM.IntW 64)) (s' := before)
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      rw [run_liftM (run_load_readBits hf14), hread ((i+14)%16) (by omega)]
      rfl)]
  denote_step_all v 126
  denote_eval v 114 126
  try eval_llvm 114
  try eval_llvm 115
  try eval_llvm 116
  try eval_llvm 117
  try eval_llvm 118
  try eval_llvm 119
  try eval_llvm 120
  try eval_llvm 121
  try eval_llvm 122
  try eval_llvm 123
  rw [index_add i 9 hi (by decide)] at hv124
  subst v124
  have hm9 := Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ring_index_mask (i+9) (by omega)
  simp [LLVM.and, LLVM.and?, hm9] at hv125
  subst v125
  have hgep : v126 = .value (stack.withOffset (BitVec.ofNat 64 (8*((i+9)%16)))) := by
    simp [hv126, gep, ptradd, LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?,
      LLVM.const?, Pointer.withOffset, ← BitVec.ofNat_mul, BitVec.mul_comm, Nat.mul_comm]
  clear hv126
  subst v126
  have hf9 : Fits before.mem (stack.withOffset (BitVec.ofNat 64 (8*((i+9)%16)))) 64 :=
    (hs.add (k := 8*((i+9)%16)) (n := 8) (by omega)).fits
  rw [BlockCom.run_bind_denote_var_of_value (x := (PoisonOr.value (q ((i+9)%16)) : LLVM.IntW 64)) (s' := before)
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      rw [run_liftM (run_load_readBits hf9), hread ((i+9)%16) (by omega)]
      rfl)]
  denote_step_all v 129
  denote_eval v 128 129
  have hm0 := Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.ring_index_mask i (by omega)
  simp [LLVM.and, LLVM.and?, hm0] at hv128
  subst v128
  have hgep : v129 = .value (stack.withOffset (BitVec.ofNat 64 (8*(i%16)))) := by
    simp [hv129, gep, ptradd, LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?,
      LLVM.const?, Pointer.withOffset, ← BitVec.ofNat_mul, BitVec.mul_comm, Nat.mul_comm]
  clear hv129
  subst v129
  have hf0 : Fits before.mem (stack.withOffset (BitVec.ofNat 64 (8*(i%16)))) 64 :=
    (hs.add (k := 8*(i%16)) (n := 8) (by omega)).fits
  rw [BlockCom.run_bind_denote_var_of_value (x := (PoisonOr.value (q (i%16)) : LLVM.IntW 64)) (s' := before)
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      rw [run_liftM (run_load_readBits hf0), hread (i%16) (by omega)]
      rfl)]
  denote_step_all v 133
  denote_eval v 131 133
  try eval_llvm 131
  try eval_llvm 132
  try eval_llvm 133
  have hw : v133 = .value (ringWord q i) := by
    simpa [fshl, later_fshl63, later_fshl56, later_fshl45, later_fshl3,
      ringWord, scheduleWord, smallSigma0, smallSigma1] using hv133
  clear hv133
  subst v133
  peel_store (ringWord q i), (stack.withOffset (BitVec.ofNat 64 (8*(i%16)))), hf0, before
  let after : GlobalState := {before with mem := laterMemory before.mem stack q i}
  change StateT.run _ after = _
  denote_step_all v 143
  denote_eval v 134 143
  have hgep : v143 = .value (kp.withOffset (BitVec.ofNat 64 (8*i))) := by
    simp [hv143, gep, ptradd, LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?,
      LLVM.const?, Pointer.withOffset, ← BitVec.ofNat_mul, BitVec.mul_comm, Nat.mul_comm]
  clear hv143
  subst v143
  have hk' : SmallRange after.mem kp 640 := hk.splice _ _
  have hkf : Fits after.mem (kp.withOffset (BitVec.ofNat 64 (8*i))) 64 :=
    (hk'.add (k := 8*i) (n := 8) (by omega)).fits
  have hkread' : readBits after.mem (kp.withOffset (BitVec.ofNat 64 (8*i))) 64 = constant := by
    rw [readBits_of_live_eq (m := before.mem)]
    · exact hkread
    · exact live?_splice_ne hne
  rw [BlockCom.run_bind_denote_var_of_value (x := (PoisonOr.value constant : LLVM.IntW 64)) (s' := after)
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      rw [run_liftM (run_load_readBits hkf), hkread']
      rfl)]
  denote_step_all v 161
  denote_eval v 145 161
  have ha : v160 = .value (laterRound work (ringWord q i) constant).a := by
    simp [hv160, hv158, hv153, hv151, hv149, hv150, hv152, hv157, hv155, hv154, hv156,
      hv148, hv147, hv146, hv145, hv142, hv139, hv141, hv140, hv138, hv136, hv134, hv135, hv137,
      simp_llvm, simp_llvm_option, fshl, first_fshl50, first_fshl46, first_fshl23,
      first_fshl36, first_fshl30, first_fshl25, laterRound, bigSigma0, bigSigma1]
  have he : v159 = .value (laterRound work (ringWord q i) constant).e := by
    simp [hv159, hv148, hv147, hv146, hv145, hv142, hv139, hv141, hv140, hv138,
      hv136, hv134, hv135, hv137, simp_llvm, simp_llvm_option,
      fshl, first_fshl50, first_fshl46, first_fshl23, laterRound, bigSigma1]
  clear hv159 hv160
  subst v159 v160
  have hc : v161 = .value (BitVec.ofBool (decide (i+1=80))) := by
    simp [hv161, simp_llvm, simp_llvm_option,
      Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_exit_test i hi]
  clear hv161
  subst v161
  by_cases hex : i+1=80
  · simp only [BlockCom.denote_term, Terminator.denote, hex, laterNext, feedforwardTarget,
      laterRound, after, simp_denote, simp_sllvm, decide_true, decide_false, BitVec.ofBool_true, BitVec.ofBool_false]

  · simp only [BlockCom.denote_term, Terminator.denote, hex, laterNext, laterTarget,
      laterRound, after, simp_denote, simp_sllvm, decide_true, decide_false, BitVec.ofBool_true, BitVec.ofBool_false]
    simp only [show (0 : BitVec 1) ≠ 1 by decide, ite_false, simp_denote]


/-- The exact successor carries the FIPS round state; round 79 enters addback. -/
theorem laterNext_spec (initial work : State) (data : Pointer) (count : Word)
    (q : Ring) (i : Nat) (constant : Word) :
    laterNext initial work data count q i constant =
      if i+1=80 then feedforwardTarget initial (Spec.round work (ringWord q i) constant) data count
      else laterTarget initial (Spec.round work (ringWord q i) constant) data count (i+1) := by
  simp only [laterNext, laterRound_eq]

theorem laterNext_last (initial work : State) (data : Pointer) (count : Word)
    (q : Ring) (constant : Word) :
    laterNext initial work data count q 79 constant =
      feedforwardTarget initial (Spec.round work (ringWord q 79) constant) data count := by
  simp only [laterNext_spec, Nat.reduceAdd, ite_true]


end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
