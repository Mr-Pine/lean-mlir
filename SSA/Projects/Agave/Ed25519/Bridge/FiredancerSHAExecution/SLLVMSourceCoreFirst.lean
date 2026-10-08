import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreValues
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreFirstArithmetic

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def firstMemory (m : MemoryState) (stack : Pointer) (i : Nat) (native : Word) : MemoryState :=
  m.splice (stack.withOffset (BitVec.ofNat 64 (8*i))) (bswapBV native)

def firstNext (initial work : State) (data : Pointer) (count : Word)
    (i : Nat) (native constant : Word) : SuccArgs core.cfgSigs :=
  let next := firstRound work (bswapBV native) constant
  if i + 1 = 16 then laterTarget initial next data count 16
  else firstTarget initial next data count (i+1)

/-- Execute the actual imported source block, retaining precisely its observable
memory update and branch arguments. The continuation discards dead local SSA values. -/
theorem first_body
    (kp chain stack originalData data : Pointer) (originalCount count : Word)
    (original initial work : State) (i : Nat) (native constant : Word)
    (s : GlobalState) (hi : i < 16)
    (hd : SmallRange s.mem data 128) (hs : SmallRange s.mem stack 128)
    (hk : SmallRange s.mem kp 640) (hne : stack.id ≠ kp.id)
    (hnative : readBits s.mem (data.withOffset (BitVec.ofNat 64 (8*i))) 64 = native)
    (hconstant : readBits s.mem (kp.withOffset (BitVec.ofNat 64 (8*i))) 64 = constant)
    (k : HVector TyDenote.toType [] ⊕ SuccArgs core.cfgSigs → SLLVM.m α) :
    StateT.run (core.cfgBlock_1.denote
      (blockInput (firstTarget initial work data count i)
        (ambient kp chain stack originalData originalCount original)) >>= fun (_, jump) => k jump) s =
    StateT.run (k (.inr (firstNext initial work data count i native constant)))
      {s with mem := firstMemory s.mem stack i native} := by
  denote_expose
  denote_step_all v 1
  denote_eval v 0 1
  simp only [blockInput, firstTarget, ambient, HVector.reverse, HVector.reverseAux, simp_denote] at hv0 hv1
  rw [first_shl i hi] at hv0
  subst v0
  have hv1' : v1 = .value (data.withOffset (BitVec.ofNat 64 (8*i))) := by
    simpa [gep, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
      Pointer.withOffset, simp_sllvm] using hv1
  subst hv1'
  clear hv1
  have hdf : Fits s.mem (data.withOffset (BitVec.ofNat 64 (8*i))) 64 := by
    exact (hd.add (k := 8*i) (n := 8) (by omega)).fits
  rw [BlockCom.run_bind_denote_var_of_value (x := PoisonOr.value native) (s' := s)
    (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load_readBits hdf), hnative]
        rfl)]
  denote_step_all v 4
  denote_eval v 3 4
  simp only [blockInput, firstTarget, ambient, HVector.reverse, HVector.reverseAux,
    simp_denote, simp_sllvm] at hv3 hv4
  subst v3
  have hv4' : v4 = .value (stack.withOffset (BitVec.ofNat 64 (8*i))) := by
    simpa [gep, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
      Pointer.withOffset, simp_sllvm, ← BitVec.ofNat_mul, Nat.mul_comm] using hv4
  subst hv4'
  clear hv4
  have hsf : Fits s.mem (stack.withOffset (BitVec.ofNat 64 (8*i))) 64 := by
    exact (hs.add (k := 8*i) (n := 8) (by omega)).fits
  peel_store (bswapBV native), (stack.withOffset (BitVec.ofNat 64 (8*i))), hsf, s
  denote_step_all v 14
  denote_eval v 5 14
  simp only [blockInput, firstTarget, ambient, HVector.reverse, HVector.reverseAux,
    simp_denote, simp_sllvm] at hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
  have hv14' : v14 = .value (kp.withOffset (BitVec.ofNat 64 (8*i))) := by
    simpa [gep, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
      Pointer.withOffset, simp_sllvm, ← BitVec.ofNat_mul, Nat.mul_comm] using hv14
  subst hv14'
  clear hv14
  let t : GlobalState := {s with mem := firstMemory s.mem stack i native}
  have hkf : Fits t.mem (kp.withOffset (BitVec.ofNat 64 (8*i))) 64 := by
    exact ((hk.splice (stack.withOffset (BitVec.ofNat 64 (8*i))) (bswapBV native)).add
      (k := 8*i) (n := 8) (by omega)).fits
  have hkread : readBits t.mem (kp.withOffset (BitVec.ofNat 64 (8*i))) 64 = constant := by
    rw [readBits_of_live_eq (m := s.mem) (by exact live?_splice_ne hne)]
    exact hconstant
  dsimp only [t, firstMemory] at hkf hkread
  rw [BlockCom.run_bind_denote_var_of_value (x := PoisonOr.value constant) (s' := t)
    (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load_readBits hkf), hkread]
        rfl)]
  denote_step_all v 33
  denote_eval v 16 33
  simp only [blockInput, firstTarget, ambient, HVector.reverse, HVector.reverseAux,
    simp_denote, simp_sllvm] at hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28 hv29 hv30 hv31 hv32 hv33
  rw [first_add i hi] at hv32
  subst v5 v6 v7 v8 v9 v10 v11 v12 v13 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33
  simp only [BlockCom.denote_term, Terminator.denote_condBr, blockInput, firstTarget,
    ambient, HVector.reverse, HVector.reverseAux, simp_denote, simp_sllvm,
    LLVM.add, LLVM.add?, LLVM.xor, LLVM.xor?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.icmp, LLVM.icmp?, LLVM.icmp',
    first_fshl50, first_fshl46, first_fshl23, first_fshl36, first_fshl30, first_fshl25]
  have heq : (BitVec.ofNat 64 (i+1) == 16#64) = decide (i+1=16) := by
    interval_cases i <;> decide
  simp only [heq]
  by_cases hi16 : i+1=16
  · simp only [hi16, decide_true, BitVec.ofBool_true, ite_eq_left rfl, simp_denote, simp_sllvm]
    simp only [Target.denote, simp_denote, simp_sllvm, firstNext, ite_eq_left hi16,
      laterTarget, firstRound, bigSigma0, bigSigma1, t, firstMemory]
    rfl
  · simp only [hi16, decide_false, BitVec.ofBool_false, ite_eq_right (by decide : (0#1) ≠ 1),
      simp_denote, simp_sllvm]
    simp only [Target.denote, simp_denote, simp_sllvm, firstNext, ite_eq_right hi16,
      firstTarget, firstRound, bigSigma0, bigSigma1, t, firstMemory]
    rfl

theorem firstNext_continue (initial work : State) (data : Pointer) (count : Word)
    (i : Nat) (native constant : Word) (hi : i + 1 ≠ 16) :
    firstNext initial work data count i native constant =
      firstTarget initial (round work (bswapBV native) constant) data count (i+1) := by
  simp only [firstNext, ite_eq_right hi, firstRound_eq]

theorem firstNext_exit (initial work : State) (data : Pointer) (count : Word)
    (native constant : Word) :
    firstNext initial work data count 15 native constant =
      laterTarget initial (round work (bswapBV native) constant) data count 16 := by
  simp [firstNext, firstRound_eq]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
