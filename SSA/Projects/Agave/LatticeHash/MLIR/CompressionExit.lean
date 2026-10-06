/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.agave_compress_pre_8
import SSA.Projects.Agave.LatticeHash.MLIR.agave_compress_pre_16
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionMemory

/-!
Execution of the compiler-emitted compression exit blocks. The incoming sixteen
state vectors are arbitrary; the loop proof must establish round correctness separately.
Opaque intermediate states keep symbolic stores shared, and `outputState_step`
relates their final memory to the generic output layout without unfolding the
whole sixteen-store memory expression during unification.
-/

namespace AgaveLatticeHash.MLIR.CompressionExit
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression

private theorem outputState_step {n : Nat} (out : Pointer) (v : State (Vector Word n))
    (s : GlobalState) (k : Nat) (prev next : GlobalState)
    (hprev : prev = {s with mem := outputMem out v k s.mem})
    (hnext : next = {prev with mem := prev.mem.splice (out.withOffset
      (BitVec.ofNat 64 (4*n*k))) (packBits (v (Fin.ofNat 16 k)))}) :
    next = {s with mem := outputMem out v (k+1) s.mem} := by
  rw [hnext, hprev]
  rfl

abbrev V8 := SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 32)))

/-- Live values threaded into compiler block `bb2`, in SSA definition order. -/
abbrev exitArgs8 (v : State (Vector Word 8)) : SuccArgs agave_compress_pre_8.sigs :=
  ⟨1, rfl, ([(v 0).map PoisonOr.value,
    (v 15).map PoisonOr.value,
    (v 10).map PoisonOr.value,
    (v 5).map PoisonOr.value,
    (v 1).map PoisonOr.value,
    (v 12).map PoisonOr.value,
    (v 11).map PoisonOr.value,
    (v 6).map PoisonOr.value,
    (v 2).map PoisonOr.value,
    (v 13).map PoisonOr.value,
    (v 8).map PoisonOr.value,
    (v 7).map PoisonOr.value,
    (v 3).map PoisonOr.value,
    (v 14).map PoisonOr.value,
    (v 9).map PoisonOr.value,
    (v 4).map PoisonOr.value]ₕ : HVector TyDenote.toType [V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8])⟩

/-- Only the output pointer and byte-offset constants are read from the ambient entry values. -/
structure ExitEnv8 (V : agave_compress_pre_8.cfgCtx.Valuation) (out : Pointer) : Prop where
  outPtr : V ⟨68, rfl⟩ = PoisonOr.value out
  off1 : V ⟨60, rfl⟩ = PoisonOr.value (32 : BitVec 64)
  off2 : V ⟨59, rfl⟩ = PoisonOr.value (64 : BitVec 64)
  off3 : V ⟨58, rfl⟩ = PoisonOr.value (96 : BitVec 64)
  off4 : V ⟨57, rfl⟩ = PoisonOr.value (128 : BitVec 64)
  off5 : V ⟨56, rfl⟩ = PoisonOr.value (160 : BitVec 64)
  off6 : V ⟨55, rfl⟩ = PoisonOr.value (192 : BitVec 64)
  off7 : V ⟨54, rfl⟩ = PoisonOr.value (224 : BitVec 64)
  off8 : V ⟨33, rfl⟩ = PoisonOr.value (256 : BitVec 64)
  off9 : V ⟨32, rfl⟩ = PoisonOr.value (288 : BitVec 64)
  off10 : V ⟨31, rfl⟩ = PoisonOr.value (320 : BitVec 64)
  off11 : V ⟨30, rfl⟩ = PoisonOr.value (352 : BitVec 64)
  off12 : V ⟨29, rfl⟩ = PoisonOr.value (384 : BitVec 64)
  off13 : V ⟨28, rfl⟩ = PoisonOr.value (416 : BitVec 64)
  off14 : V ⟨27, rfl⟩ = PoisonOr.value (448 : BitVec 64)
  off15 : V ⟨26, rfl⟩ = PoisonOr.value (480 : BitVec 64)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- The actual compiled exit block stores every result vector and returns normally. -/
theorem exit8_run (V : agave_compress_pre_8.cfgCtx.Valuation) (out : Pointer)
    (v : State (Vector Word 8)) (hV : ExitEnv8 V out) (s : GlobalState)
    (hfit : ∀ k < 16, Fits s.mem (out.withOffset (BitVec.ofNat 64 (32*k))) 256) :
    StateT.run (agave_compress_pre_8.blocks.run V (exitArgs8 v)) s =
      .value ([]ₕ, {s with mem := outputMem out v 16 s.mem}) := by
  denote_enter_block
  denote_number_from 0
  obtain ⟨s1, hs1⟩ : ∃ t : GlobalState,
      t = { s with mem := s.mem.splice out (packBits (v 0)) } := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s1)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine, hV.outPtr]
      rw [run_liftM (s := s)
        (run_store (p := out) (flatten_packBits (v 0))
          (show Fits s.mem out 256 from by simpa [Pointer.withOffset] using hfit 0 (by omega)))]
      rw [hs1]
      rfl)]
  have fit1 : ∀ j < 16, Fits s1.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs1]
    exact fits_splice (hfit j hj)
  denote_step_all w 0
  denote_eval w 0 0
  simp only [simp_spine] at hw0
  rw [hV.outPtr, hV.off1] at hw0
  change w0 = PoisonOr.value (out.withOffset 32) at hw0
  subst hw0
  obtain ⟨s2, hs2⟩ : ∃ t : GlobalState,
      t = { s1 with mem := s1.mem.splice (out.withOffset 32) (packBits (v 1)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s2)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s1)
        (run_store (p := (out.withOffset 32)) (flatten_packBits (v 1))
          (fit1 1 (by omega)))]
      rw [hs2]
      rfl)]
  have fit2 : ∀ j < 16, Fits s2.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs2]
    exact fits_splice (fit1 j hj)
  denote_step_all w 1
  denote_eval w 1 1
  simp only [simp_spine] at hw1
  rw [hV.outPtr, hV.off2] at hw1
  change w1 = PoisonOr.value (out.withOffset 64) at hw1
  subst hw1
  obtain ⟨s3, hs3⟩ : ∃ t : GlobalState,
      t = { s2 with mem := s2.mem.splice (out.withOffset 64) (packBits (v 2)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s3)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s2)
        (run_store (p := (out.withOffset 64)) (flatten_packBits (v 2))
          (fit2 2 (by omega)))]
      rw [hs3]
      rfl)]
  have fit3 : ∀ j < 16, Fits s3.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs3]
    exact fits_splice (fit2 j hj)
  denote_step_all w 2
  denote_eval w 2 2
  simp only [simp_spine] at hw2
  rw [hV.outPtr, hV.off3] at hw2
  change w2 = PoisonOr.value (out.withOffset 96) at hw2
  subst hw2
  obtain ⟨s4, hs4⟩ : ∃ t : GlobalState,
      t = { s3 with mem := s3.mem.splice (out.withOffset 96) (packBits (v 3)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s4)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s3)
        (run_store (p := (out.withOffset 96)) (flatten_packBits (v 3))
          (fit3 3 (by omega)))]
      rw [hs4]
      rfl)]
  have fit4 : ∀ j < 16, Fits s4.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs4]
    exact fits_splice (fit3 j hj)
  denote_step_all w 3
  denote_eval w 3 3
  simp only [simp_spine] at hw3
  rw [hV.outPtr, hV.off4] at hw3
  change w3 = PoisonOr.value (out.withOffset 128) at hw3
  subst hw3
  obtain ⟨s5, hs5⟩ : ∃ t : GlobalState,
      t = { s4 with mem := s4.mem.splice (out.withOffset 128) (packBits (v 4)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s5)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s4)
        (run_store (p := (out.withOffset 128)) (flatten_packBits (v 4))
          (fit4 4 (by omega)))]
      rw [hs5]
      rfl)]
  have fit5 : ∀ j < 16, Fits s5.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs5]
    exact fits_splice (fit4 j hj)
  denote_step_all w 4
  denote_eval w 4 4
  simp only [simp_spine] at hw4
  rw [hV.outPtr, hV.off5] at hw4
  change w4 = PoisonOr.value (out.withOffset 160) at hw4
  subst hw4
  obtain ⟨s6, hs6⟩ : ∃ t : GlobalState,
      t = { s5 with mem := s5.mem.splice (out.withOffset 160) (packBits (v 5)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s6)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s5)
        (run_store (p := (out.withOffset 160)) (flatten_packBits (v 5))
          (fit5 5 (by omega)))]
      rw [hs6]
      rfl)]
  have fit6 : ∀ j < 16, Fits s6.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs6]
    exact fits_splice (fit5 j hj)
  denote_step_all w 5
  denote_eval w 5 5
  simp only [simp_spine] at hw5
  rw [hV.outPtr, hV.off6] at hw5
  change w5 = PoisonOr.value (out.withOffset 192) at hw5
  subst hw5
  obtain ⟨s7, hs7⟩ : ∃ t : GlobalState,
      t = { s6 with mem := s6.mem.splice (out.withOffset 192) (packBits (v 6)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s7)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s6)
        (run_store (p := (out.withOffset 192)) (flatten_packBits (v 6))
          (fit6 6 (by omega)))]
      rw [hs7]
      rfl)]
  have fit7 : ∀ j < 16, Fits s7.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs7]
    exact fits_splice (fit6 j hj)
  denote_step_all w 6
  denote_eval w 6 6
  simp only [simp_spine] at hw6
  rw [hV.outPtr, hV.off7] at hw6
  change w6 = PoisonOr.value (out.withOffset 224) at hw6
  subst hw6
  obtain ⟨s8, hs8⟩ : ∃ t : GlobalState,
      t = { s7 with mem := s7.mem.splice (out.withOffset 224) (packBits (v 7)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s8)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s7)
        (run_store (p := (out.withOffset 224)) (flatten_packBits (v 7))
          (fit7 7 (by omega)))]
      rw [hs8]
      rfl)]
  have fit8 : ∀ j < 16, Fits s8.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs8]
    exact fits_splice (fit7 j hj)
  denote_step_all w 7
  denote_eval w 7 7
  simp only [simp_spine] at hw7
  rw [hV.outPtr, hV.off8] at hw7
  change w7 = PoisonOr.value (out.withOffset 256) at hw7
  subst hw7
  obtain ⟨s9, hs9⟩ : ∃ t : GlobalState,
      t = { s8 with mem := s8.mem.splice (out.withOffset 256) (packBits (v 8)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s9)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s8)
        (run_store (p := (out.withOffset 256)) (flatten_packBits (v 8))
          (fit8 8 (by omega)))]
      rw [hs9]
      rfl)]
  have fit9 : ∀ j < 16, Fits s9.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs9]
    exact fits_splice (fit8 j hj)
  denote_step_all w 8
  denote_eval w 8 8
  simp only [simp_spine] at hw8
  rw [hV.outPtr, hV.off9] at hw8
  change w8 = PoisonOr.value (out.withOffset 288) at hw8
  subst hw8
  obtain ⟨s10, hs10⟩ : ∃ t : GlobalState,
      t = { s9 with mem := s9.mem.splice (out.withOffset 288) (packBits (v 9)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s10)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s9)
        (run_store (p := (out.withOffset 288)) (flatten_packBits (v 9))
          (fit9 9 (by omega)))]
      rw [hs10]
      rfl)]
  have fit10 : ∀ j < 16, Fits s10.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs10]
    exact fits_splice (fit9 j hj)
  denote_step_all w 9
  denote_eval w 9 9
  simp only [simp_spine] at hw9
  rw [hV.outPtr, hV.off10] at hw9
  change w9 = PoisonOr.value (out.withOffset 320) at hw9
  subst hw9
  obtain ⟨s11, hs11⟩ : ∃ t : GlobalState,
      t = { s10 with mem := s10.mem.splice (out.withOffset 320) (packBits (v 10)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s11)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s10)
        (run_store (p := (out.withOffset 320)) (flatten_packBits (v 10))
          (fit10 10 (by omega)))]
      rw [hs11]
      rfl)]
  have fit11 : ∀ j < 16, Fits s11.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs11]
    exact fits_splice (fit10 j hj)
  denote_step_all w 10
  denote_eval w 10 10
  simp only [simp_spine] at hw10
  rw [hV.outPtr, hV.off11] at hw10
  change w10 = PoisonOr.value (out.withOffset 352) at hw10
  subst hw10
  obtain ⟨s12, hs12⟩ : ∃ t : GlobalState,
      t = { s11 with mem := s11.mem.splice (out.withOffset 352) (packBits (v 11)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s12)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s11)
        (run_store (p := (out.withOffset 352)) (flatten_packBits (v 11))
          (fit11 11 (by omega)))]
      rw [hs12]
      rfl)]
  have fit12 : ∀ j < 16, Fits s12.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs12]
    exact fits_splice (fit11 j hj)
  denote_step_all w 11
  denote_eval w 11 11
  simp only [simp_spine] at hw11
  rw [hV.outPtr, hV.off12] at hw11
  change w11 = PoisonOr.value (out.withOffset 384) at hw11
  subst hw11
  obtain ⟨s13, hs13⟩ : ∃ t : GlobalState,
      t = { s12 with mem := s12.mem.splice (out.withOffset 384) (packBits (v 12)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s13)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s12)
        (run_store (p := (out.withOffset 384)) (flatten_packBits (v 12))
          (fit12 12 (by omega)))]
      rw [hs13]
      rfl)]
  have fit13 : ∀ j < 16, Fits s13.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs13]
    exact fits_splice (fit12 j hj)
  denote_step_all w 12
  denote_eval w 12 12
  simp only [simp_spine] at hw12
  rw [hV.outPtr, hV.off13] at hw12
  change w12 = PoisonOr.value (out.withOffset 416) at hw12
  subst hw12
  obtain ⟨s14, hs14⟩ : ∃ t : GlobalState,
      t = { s13 with mem := s13.mem.splice (out.withOffset 416) (packBits (v 13)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s14)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s13)
        (run_store (p := (out.withOffset 416)) (flatten_packBits (v 13))
          (fit13 13 (by omega)))]
      rw [hs14]
      rfl)]
  have fit14 : ∀ j < 16, Fits s14.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs14]
    exact fits_splice (fit13 j hj)
  denote_step_all w 13
  denote_eval w 13 13
  simp only [simp_spine] at hw13
  rw [hV.outPtr, hV.off14] at hw13
  change w13 = PoisonOr.value (out.withOffset 448) at hw13
  subst hw13
  obtain ⟨s15, hs15⟩ : ∃ t : GlobalState,
      t = { s14 with mem := s14.mem.splice (out.withOffset 448) (packBits (v 14)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s15)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s14)
        (run_store (p := (out.withOffset 448)) (flatten_packBits (v 14))
          (fit14 14 (by omega)))]
      rw [hs15]
      rfl)]
  have fit15 : ∀ j < 16, Fits s15.mem
      (out.withOffset (BitVec.ofNat 64 (32*j))) 256 := by
    intro j hj
    rw [hs15]
    exact fits_splice (fit14 j hj)
  denote_step_all w 14
  denote_eval w 14 14
  simp only [simp_spine] at hw14
  rw [hV.outPtr, hV.off15] at hw14
  change w14 = PoisonOr.value (out.withOffset 480) at hw14
  subst hw14
  obtain ⟨s16, hs16⟩ : ∃ t : GlobalState,
      t = { s15 with mem := s15.mem.splice (out.withOffset 480) (packBits (v 15)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s16)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s15)
        (run_store (p := (out.withOffset 480)) (flatten_packBits (v 15))
          (fit15 15 (by omega)))]
      rw [hs16]
      rfl)]
  simp -failIfUnchanged only [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]
  have state1 : s1 = {s with mem := outputMem out v 1 s.mem} :=
    outputState_step out v s 0 s s1 rfl (by simpa [Pointer.withOffset] using hs1)
  have state2 : s2 = {s with mem := outputMem out v 2 s.mem} :=
    outputState_step out v s 1 s1 s2 state1 hs2
  have state3 : s3 = {s with mem := outputMem out v 3 s.mem} :=
    outputState_step out v s 2 s2 s3 state2 hs3
  have state4 : s4 = {s with mem := outputMem out v 4 s.mem} :=
    outputState_step out v s 3 s3 s4 state3 hs4
  have state5 : s5 = {s with mem := outputMem out v 5 s.mem} :=
    outputState_step out v s 4 s4 s5 state4 hs5
  have state6 : s6 = {s with mem := outputMem out v 6 s.mem} :=
    outputState_step out v s 5 s5 s6 state5 hs6
  have state7 : s7 = {s with mem := outputMem out v 7 s.mem} :=
    outputState_step out v s 6 s6 s7 state6 hs7
  have state8 : s8 = {s with mem := outputMem out v 8 s.mem} :=
    outputState_step out v s 7 s7 s8 state7 hs8
  have state9 : s9 = {s with mem := outputMem out v 9 s.mem} :=
    outputState_step out v s 8 s8 s9 state8 hs9
  have state10 : s10 = {s with mem := outputMem out v 10 s.mem} :=
    outputState_step out v s 9 s9 s10 state9 hs10
  have state11 : s11 = {s with mem := outputMem out v 11 s.mem} :=
    outputState_step out v s 10 s10 s11 state10 hs11
  have state12 : s12 = {s with mem := outputMem out v 12 s.mem} :=
    outputState_step out v s 11 s11 s12 state11 hs12
  have state13 : s13 = {s with mem := outputMem out v 13 s.mem} :=
    outputState_step out v s 12 s12 s13 state12 hs13
  have state14 : s14 = {s with mem := outputMem out v 14 s.mem} :=
    outputState_step out v s 13 s13 s14 state13 hs14
  have state15 : s15 = {s with mem := outputMem out v 15 s.mem} :=
    outputState_step out v s 14 s14 s15 state14 hs15
  have state16 : s16 = {s with mem := outputMem out v 16 s.mem} :=
    outputState_step out v s 15 s15 s16 state15 hs16
  rw [state16]

abbrev V16 := SLLVM.Ty.arith (.vector 16 (.bitvec (.concrete 32)))

/-- Live values threaded into compiler block `bb2`, in SSA definition order. -/
abbrev exitArgs16 (v : State (Vector Word 16)) : SuccArgs agave_compress_pre_16.sigs :=
  ⟨1, rfl, ([(v 0).map PoisonOr.value,
    (v 15).map PoisonOr.value,
    (v 10).map PoisonOr.value,
    (v 5).map PoisonOr.value,
    (v 1).map PoisonOr.value,
    (v 12).map PoisonOr.value,
    (v 11).map PoisonOr.value,
    (v 6).map PoisonOr.value,
    (v 2).map PoisonOr.value,
    (v 13).map PoisonOr.value,
    (v 8).map PoisonOr.value,
    (v 7).map PoisonOr.value,
    (v 3).map PoisonOr.value,
    (v 14).map PoisonOr.value,
    (v 9).map PoisonOr.value,
    (v 4).map PoisonOr.value]ₕ : HVector TyDenote.toType [V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16])⟩

/-- Only the output pointer and byte-offset constants are read from the ambient entry values. -/
structure ExitEnv16 (V : agave_compress_pre_16.cfgCtx.Valuation) (out : Pointer) : Prop where
  outPtr : V ⟨70, rfl⟩ = PoisonOr.value out
  off1 : V ⟨62, rfl⟩ = PoisonOr.value (64 : BitVec 64)
  off2 : V ⟨61, rfl⟩ = PoisonOr.value (128 : BitVec 64)
  off3 : V ⟨60, rfl⟩ = PoisonOr.value (192 : BitVec 64)
  off4 : V ⟨59, rfl⟩ = PoisonOr.value (256 : BitVec 64)
  off5 : V ⟨58, rfl⟩ = PoisonOr.value (320 : BitVec 64)
  off6 : V ⟨57, rfl⟩ = PoisonOr.value (384 : BitVec 64)
  off7 : V ⟨56, rfl⟩ = PoisonOr.value (448 : BitVec 64)
  off8 : V ⟨33, rfl⟩ = PoisonOr.value (512 : BitVec 64)
  off9 : V ⟨32, rfl⟩ = PoisonOr.value (576 : BitVec 64)
  off10 : V ⟨31, rfl⟩ = PoisonOr.value (640 : BitVec 64)
  off11 : V ⟨30, rfl⟩ = PoisonOr.value (704 : BitVec 64)
  off12 : V ⟨29, rfl⟩ = PoisonOr.value (768 : BitVec 64)
  off13 : V ⟨28, rfl⟩ = PoisonOr.value (832 : BitVec 64)
  off14 : V ⟨27, rfl⟩ = PoisonOr.value (896 : BitVec 64)
  off15 : V ⟨26, rfl⟩ = PoisonOr.value (960 : BitVec 64)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- The actual compiled exit block stores every result vector and returns normally. -/
theorem exit16_run (V : agave_compress_pre_16.cfgCtx.Valuation) (out : Pointer)
    (v : State (Vector Word 16)) (hV : ExitEnv16 V out) (s : GlobalState)
    (hfit : ∀ k < 16, Fits s.mem (out.withOffset (BitVec.ofNat 64 (64*k))) 512) :
    StateT.run (agave_compress_pre_16.blocks.run V (exitArgs16 v)) s =
      .value ([]ₕ, {s with mem := outputMem out v 16 s.mem}) := by
  denote_enter_block
  denote_number_from 0
  obtain ⟨s1, hs1⟩ : ∃ t : GlobalState,
      t = { s with mem := s.mem.splice out (packBits (v 0)) } := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s1)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine, hV.outPtr]
      rw [run_liftM (s := s)
        (run_store (p := out) (flatten_packBits (v 0))
          (show Fits s.mem out 512 from by simpa [Pointer.withOffset] using hfit 0 (by omega)))]
      rw [hs1]
      rfl)]
  have fit1 : ∀ j < 16, Fits s1.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs1]
    exact fits_splice (hfit j hj)
  denote_step_all w 0
  denote_eval w 0 0
  simp only [simp_spine] at hw0
  rw [hV.outPtr, hV.off1] at hw0
  change w0 = PoisonOr.value (out.withOffset 64) at hw0
  subst hw0
  obtain ⟨s2, hs2⟩ : ∃ t : GlobalState,
      t = { s1 with mem := s1.mem.splice (out.withOffset 64) (packBits (v 1)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s2)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s1)
        (run_store (p := (out.withOffset 64)) (flatten_packBits (v 1))
          (fit1 1 (by omega)))]
      rw [hs2]
      rfl)]
  have fit2 : ∀ j < 16, Fits s2.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs2]
    exact fits_splice (fit1 j hj)
  denote_step_all w 1
  denote_eval w 1 1
  simp only [simp_spine] at hw1
  rw [hV.outPtr, hV.off2] at hw1
  change w1 = PoisonOr.value (out.withOffset 128) at hw1
  subst hw1
  obtain ⟨s3, hs3⟩ : ∃ t : GlobalState,
      t = { s2 with mem := s2.mem.splice (out.withOffset 128) (packBits (v 2)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s3)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s2)
        (run_store (p := (out.withOffset 128)) (flatten_packBits (v 2))
          (fit2 2 (by omega)))]
      rw [hs3]
      rfl)]
  have fit3 : ∀ j < 16, Fits s3.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs3]
    exact fits_splice (fit2 j hj)
  denote_step_all w 2
  denote_eval w 2 2
  simp only [simp_spine] at hw2
  rw [hV.outPtr, hV.off3] at hw2
  change w2 = PoisonOr.value (out.withOffset 192) at hw2
  subst hw2
  obtain ⟨s4, hs4⟩ : ∃ t : GlobalState,
      t = { s3 with mem := s3.mem.splice (out.withOffset 192) (packBits (v 3)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s4)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s3)
        (run_store (p := (out.withOffset 192)) (flatten_packBits (v 3))
          (fit3 3 (by omega)))]
      rw [hs4]
      rfl)]
  have fit4 : ∀ j < 16, Fits s4.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs4]
    exact fits_splice (fit3 j hj)
  denote_step_all w 3
  denote_eval w 3 3
  simp only [simp_spine] at hw3
  rw [hV.outPtr, hV.off4] at hw3
  change w3 = PoisonOr.value (out.withOffset 256) at hw3
  subst hw3
  obtain ⟨s5, hs5⟩ : ∃ t : GlobalState,
      t = { s4 with mem := s4.mem.splice (out.withOffset 256) (packBits (v 4)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s5)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s4)
        (run_store (p := (out.withOffset 256)) (flatten_packBits (v 4))
          (fit4 4 (by omega)))]
      rw [hs5]
      rfl)]
  have fit5 : ∀ j < 16, Fits s5.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs5]
    exact fits_splice (fit4 j hj)
  denote_step_all w 4
  denote_eval w 4 4
  simp only [simp_spine] at hw4
  rw [hV.outPtr, hV.off5] at hw4
  change w4 = PoisonOr.value (out.withOffset 320) at hw4
  subst hw4
  obtain ⟨s6, hs6⟩ : ∃ t : GlobalState,
      t = { s5 with mem := s5.mem.splice (out.withOffset 320) (packBits (v 5)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s6)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s5)
        (run_store (p := (out.withOffset 320)) (flatten_packBits (v 5))
          (fit5 5 (by omega)))]
      rw [hs6]
      rfl)]
  have fit6 : ∀ j < 16, Fits s6.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs6]
    exact fits_splice (fit5 j hj)
  denote_step_all w 5
  denote_eval w 5 5
  simp only [simp_spine] at hw5
  rw [hV.outPtr, hV.off6] at hw5
  change w5 = PoisonOr.value (out.withOffset 384) at hw5
  subst hw5
  obtain ⟨s7, hs7⟩ : ∃ t : GlobalState,
      t = { s6 with mem := s6.mem.splice (out.withOffset 384) (packBits (v 6)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s7)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s6)
        (run_store (p := (out.withOffset 384)) (flatten_packBits (v 6))
          (fit6 6 (by omega)))]
      rw [hs7]
      rfl)]
  have fit7 : ∀ j < 16, Fits s7.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs7]
    exact fits_splice (fit6 j hj)
  denote_step_all w 6
  denote_eval w 6 6
  simp only [simp_spine] at hw6
  rw [hV.outPtr, hV.off7] at hw6
  change w6 = PoisonOr.value (out.withOffset 448) at hw6
  subst hw6
  obtain ⟨s8, hs8⟩ : ∃ t : GlobalState,
      t = { s7 with mem := s7.mem.splice (out.withOffset 448) (packBits (v 7)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s8)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s7)
        (run_store (p := (out.withOffset 448)) (flatten_packBits (v 7))
          (fit7 7 (by omega)))]
      rw [hs8]
      rfl)]
  have fit8 : ∀ j < 16, Fits s8.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs8]
    exact fits_splice (fit7 j hj)
  denote_step_all w 7
  denote_eval w 7 7
  simp only [simp_spine] at hw7
  rw [hV.outPtr, hV.off8] at hw7
  change w7 = PoisonOr.value (out.withOffset 512) at hw7
  subst hw7
  obtain ⟨s9, hs9⟩ : ∃ t : GlobalState,
      t = { s8 with mem := s8.mem.splice (out.withOffset 512) (packBits (v 8)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s9)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s8)
        (run_store (p := (out.withOffset 512)) (flatten_packBits (v 8))
          (fit8 8 (by omega)))]
      rw [hs9]
      rfl)]
  have fit9 : ∀ j < 16, Fits s9.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs9]
    exact fits_splice (fit8 j hj)
  denote_step_all w 8
  denote_eval w 8 8
  simp only [simp_spine] at hw8
  rw [hV.outPtr, hV.off9] at hw8
  change w8 = PoisonOr.value (out.withOffset 576) at hw8
  subst hw8
  obtain ⟨s10, hs10⟩ : ∃ t : GlobalState,
      t = { s9 with mem := s9.mem.splice (out.withOffset 576) (packBits (v 9)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s10)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s9)
        (run_store (p := (out.withOffset 576)) (flatten_packBits (v 9))
          (fit9 9 (by omega)))]
      rw [hs10]
      rfl)]
  have fit10 : ∀ j < 16, Fits s10.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs10]
    exact fits_splice (fit9 j hj)
  denote_step_all w 9
  denote_eval w 9 9
  simp only [simp_spine] at hw9
  rw [hV.outPtr, hV.off10] at hw9
  change w9 = PoisonOr.value (out.withOffset 640) at hw9
  subst hw9
  obtain ⟨s11, hs11⟩ : ∃ t : GlobalState,
      t = { s10 with mem := s10.mem.splice (out.withOffset 640) (packBits (v 10)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s11)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s10)
        (run_store (p := (out.withOffset 640)) (flatten_packBits (v 10))
          (fit10 10 (by omega)))]
      rw [hs11]
      rfl)]
  have fit11 : ∀ j < 16, Fits s11.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs11]
    exact fits_splice (fit10 j hj)
  denote_step_all w 10
  denote_eval w 10 10
  simp only [simp_spine] at hw10
  rw [hV.outPtr, hV.off11] at hw10
  change w10 = PoisonOr.value (out.withOffset 704) at hw10
  subst hw10
  obtain ⟨s12, hs12⟩ : ∃ t : GlobalState,
      t = { s11 with mem := s11.mem.splice (out.withOffset 704) (packBits (v 11)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s12)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s11)
        (run_store (p := (out.withOffset 704)) (flatten_packBits (v 11))
          (fit11 11 (by omega)))]
      rw [hs12]
      rfl)]
  have fit12 : ∀ j < 16, Fits s12.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs12]
    exact fits_splice (fit11 j hj)
  denote_step_all w 11
  denote_eval w 11 11
  simp only [simp_spine] at hw11
  rw [hV.outPtr, hV.off12] at hw11
  change w11 = PoisonOr.value (out.withOffset 768) at hw11
  subst hw11
  obtain ⟨s13, hs13⟩ : ∃ t : GlobalState,
      t = { s12 with mem := s12.mem.splice (out.withOffset 768) (packBits (v 12)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s13)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s12)
        (run_store (p := (out.withOffset 768)) (flatten_packBits (v 12))
          (fit12 12 (by omega)))]
      rw [hs13]
      rfl)]
  have fit13 : ∀ j < 16, Fits s13.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs13]
    exact fits_splice (fit12 j hj)
  denote_step_all w 12
  denote_eval w 12 12
  simp only [simp_spine] at hw12
  rw [hV.outPtr, hV.off13] at hw12
  change w12 = PoisonOr.value (out.withOffset 832) at hw12
  subst hw12
  obtain ⟨s14, hs14⟩ : ∃ t : GlobalState,
      t = { s13 with mem := s13.mem.splice (out.withOffset 832) (packBits (v 13)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s14)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s13)
        (run_store (p := (out.withOffset 832)) (flatten_packBits (v 13))
          (fit13 13 (by omega)))]
      rw [hs14]
      rfl)]
  have fit14 : ∀ j < 16, Fits s14.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs14]
    exact fits_splice (fit13 j hj)
  denote_step_all w 13
  denote_eval w 13 13
  simp only [simp_spine] at hw13
  rw [hV.outPtr, hV.off14] at hw13
  change w13 = PoisonOr.value (out.withOffset 896) at hw13
  subst hw13
  obtain ⟨s15, hs15⟩ : ∃ t : GlobalState,
      t = { s14 with mem := s14.mem.splice (out.withOffset 896) (packBits (v 14)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s15)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s14)
        (run_store (p := (out.withOffset 896)) (flatten_packBits (v 14))
          (fit14 14 (by omega)))]
      rw [hs15]
      rfl)]
  have fit15 : ∀ j < 16, Fits s15.mem
      (out.withOffset (BitVec.ofNat 64 (64*j))) 512 := by
    intro j hj
    rw [hs15]
    exact fits_splice (fit14 j hj)
  denote_step_all w 14
  denote_eval w 14 14
  simp only [simp_spine] at hw14
  rw [hV.outPtr, hV.off15] at hw14
  change w14 = PoisonOr.value (out.withOffset 960) at hw14
  subst hw14
  obtain ⟨s16, hs16⟩ : ∃ t : GlobalState,
      t = { s15 with mem := s15.mem.splice (out.withOffset 960) (packBits (v 15)) } := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s16)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM (s := s15)
        (run_store (p := (out.withOffset 960)) (flatten_packBits (v 15))
          (fit15 15 (by omega)))]
      rw [hs16]
      rfl)]
  simp -failIfUnchanged only [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]
  have state1 : s1 = {s with mem := outputMem out v 1 s.mem} :=
    outputState_step out v s 0 s s1 rfl (by simpa [Pointer.withOffset] using hs1)
  have state2 : s2 = {s with mem := outputMem out v 2 s.mem} :=
    outputState_step out v s 1 s1 s2 state1 hs2
  have state3 : s3 = {s with mem := outputMem out v 3 s.mem} :=
    outputState_step out v s 2 s2 s3 state2 hs3
  have state4 : s4 = {s with mem := outputMem out v 4 s.mem} :=
    outputState_step out v s 3 s3 s4 state3 hs4
  have state5 : s5 = {s with mem := outputMem out v 5 s.mem} :=
    outputState_step out v s 4 s4 s5 state4 hs5
  have state6 : s6 = {s with mem := outputMem out v 6 s.mem} :=
    outputState_step out v s 5 s5 s6 state5 hs6
  have state7 : s7 = {s with mem := outputMem out v 7 s.mem} :=
    outputState_step out v s 6 s6 s7 state6 hs7
  have state8 : s8 = {s with mem := outputMem out v 8 s.mem} :=
    outputState_step out v s 7 s7 s8 state7 hs8
  have state9 : s9 = {s with mem := outputMem out v 9 s.mem} :=
    outputState_step out v s 8 s8 s9 state8 hs9
  have state10 : s10 = {s with mem := outputMem out v 10 s.mem} :=
    outputState_step out v s 9 s9 s10 state9 hs10
  have state11 : s11 = {s with mem := outputMem out v 11 s.mem} :=
    outputState_step out v s 10 s10 s11 state10 hs11
  have state12 : s12 = {s with mem := outputMem out v 12 s.mem} :=
    outputState_step out v s 11 s11 s12 state11 hs12
  have state13 : s13 = {s with mem := outputMem out v 13 s.mem} :=
    outputState_step out v s 12 s12 s13 state12 hs13
  have state14 : s14 = {s with mem := outputMem out v 14 s.mem} :=
    outputState_step out v s 13 s13 s14 state13 hs14
  have state15 : s15 = {s with mem := outputMem out v 15 s.mem} :=
    outputState_step out v s 14 s14 s15 state14 hs15
  have state16 : s16 = {s with mem := outputMem out v 16 s.mem} :=
    outputState_step out v s 15 s15 s16 state15 hs16
  rw [state16]

end AgaveLatticeHash.MLIR.CompressionExit
