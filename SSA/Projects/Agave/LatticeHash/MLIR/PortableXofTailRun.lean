/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofTailData
import SSA.Projects.Agave.LatticeHash.MLIR.PortableStores
namespace AgaveLatticeHash.MLIR.PortableXof
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem pre_tail_run (V : preRound.middle.Valuation) (out : Pointer)
    (x : State Word) (env : TailEnv V out)
    (hx : ∀ i, V (resultVar i) = .value (x i))
    (s : GlobalState) (hout : Fits s.mem out 512) :
    StateT.run ((preRound.tail.denote V) >>= fun _ =>
      pure ([]ₕ : HVector (fun t : SLLVM.Ty => TyDenote.toType t) [])) s =
    .value ([]ₕ, {s with mem := portableCompressionMemory s.mem out x}) := by
  have hx0 : V ⟨47, rfl⟩ = .value (x 0) := hx 0
  have hx1 : V ⟨33, rfl⟩ = .value (x 1) := hx 1
  have hx2 : V ⟨19, rfl⟩ = .value (x 2) := hx 2
  have hx3 : V ⟨5, rfl⟩ = .value (x 3) := hx 3
  have hx4 : V ⟨0, rfl⟩ = .value (x 4) := hx 4
  have hx5 : V ⟨42, rfl⟩ = .value (x 5) := hx 5
  have hx6 : V ⟨28, rfl⟩ = .value (x 6) := hx 6
  have hx7 : V ⟨14, rfl⟩ = .value (x 7) := hx 7
  have hx8 : V ⟨16, rfl⟩ = .value (x 8) := hx 8
  have hx9 : V ⟨2, rfl⟩ = .value (x 9) := hx 9
  have hx10 : V ⟨44, rfl⟩ = .value (x 10) := hx 10
  have hx11 : V ⟨30, rfl⟩ = .value (x 11) := hx 11
  have hx12 : V ⟨31, rfl⟩ = .value (x 12) := hx 12
  have hx13 : V ⟨17, rfl⟩ = .value (x 13) := hx 13
  have hx14 : V ⟨3, rfl⟩ = .value (x 14) := hx 14
  have hx15 : V ⟨45, rfl⟩ = .value (x 15) := hx 15
  change StateT.run ((preRound.tail.denote V) >>= fun _ => pure ([]ₕ : HVector (fun t : SLLVM.Ty => TyDenote.toType t) [])) s = _
  dsimp -failIfUnchanged only [preRound]
  denote_number_from 0
  obtain ⟨s1, hs1⟩ : ∃ t : GlobalState,
      t = {s with mem := s.mem.splice out (x 0)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s1)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [env.out, hx0]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 0)) rfl
        (show Fits s.mem out 32 from Fits.mono hout (by omega)))]
      rw [hs1]; rfl)]
  have hout1 : Fits s1.mem out 512 := by
    rw [hs1]; exact fits_splice hout
  denote_step_all w 0
  denote_eval w 0 0
  simp -failIfUnchanged only [simp_spine] at hw0
  rw [env.out, env.off4] at hw0
  change w0 = PoisonOr.value (out.withOffset 4) at hw0
  subst hw0
  have fit1 := remainingFits s1.mem out hout1 (4 : BitVec 64) (by simp)
  norm_num at fit1
  obtain ⟨s2, hs2⟩ : ∃ t : GlobalState,
      t = {s1 with mem := s1.mem.splice (out.withOffset 4) (x 1)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s2)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx1]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 1)) rfl
        (show Fits s1.mem (out.withOffset 4) 32 from Fits.mono fit1 (by omega)))]
      rw [hs2]; rfl)]
  have hout2 : Fits s2.mem out 512 := by
    rw [hs2]; exact fits_splice hout1
  denote_step_all w 1
  denote_eval w 1 1
  simp -failIfUnchanged only [simp_spine] at hw1
  rw [env.out, env.off8] at hw1
  change w1 = PoisonOr.value (out.withOffset 8) at hw1
  subst hw1
  have fit2 := remainingFits s2.mem out hout2 (8 : BitVec 64) (by simp)
  norm_num at fit2
  obtain ⟨s3, hs3⟩ : ∃ t : GlobalState,
      t = {s2 with mem := s2.mem.splice (out.withOffset 8) (x 2)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s3)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx2]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 2)) rfl
        (show Fits s2.mem (out.withOffset 8) 32 from Fits.mono fit2 (by omega)))]
      rw [hs3]; rfl)]
  have hout3 : Fits s3.mem out 512 := by
    rw [hs3]; exact fits_splice hout2
  denote_step_all w 2
  denote_eval w 2 2
  simp -failIfUnchanged only [simp_spine] at hw2
  rw [env.out, env.off12] at hw2
  change w2 = PoisonOr.value (out.withOffset 12) at hw2
  subst hw2
  have fit3 := remainingFits s3.mem out hout3 (12 : BitVec 64) (by simp)
  norm_num at fit3
  obtain ⟨s4, hs4⟩ : ∃ t : GlobalState,
      t = {s3 with mem := s3.mem.splice (out.withOffset 12) (x 3)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s4)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx3]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 3)) rfl
        (show Fits s3.mem (out.withOffset 12) 32 from Fits.mono fit3 (by omega)))]
      rw [hs4]; rfl)]
  have hout4 : Fits s4.mem out 512 := by
    rw [hs4]; exact fits_splice hout3
  denote_step_all w 3
  denote_eval w 3 3
  simp -failIfUnchanged only [simp_spine] at hw3
  rw [env.out, env.off16] at hw3
  change w3 = PoisonOr.value (out.withOffset 16) at hw3
  subst hw3
  have fit4 := remainingFits s4.mem out hout4 (16 : BitVec 64) (by simp)
  norm_num at fit4
  obtain ⟨s5, hs5⟩ : ∃ t : GlobalState,
      t = {s4 with mem := s4.mem.splice (out.withOffset 16) (x 4)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s5)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx4]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 4)) rfl
        (show Fits s4.mem (out.withOffset 16) 32 from Fits.mono fit4 (by omega)))]
      rw [hs5]; rfl)]
  have hout5 : Fits s5.mem out 512 := by
    rw [hs5]; exact fits_splice hout4
  denote_step_all w 4
  denote_eval w 4 4
  simp -failIfUnchanged only [simp_spine] at hw4
  rw [env.out, env.off20] at hw4
  change w4 = PoisonOr.value (out.withOffset 20) at hw4
  subst hw4
  have fit5 := remainingFits s5.mem out hout5 (20 : BitVec 64) (by simp)
  norm_num at fit5
  obtain ⟨s6, hs6⟩ : ∃ t : GlobalState,
      t = {s5 with mem := s5.mem.splice (out.withOffset 20) (x 5)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s6)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx5]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 5)) rfl
        (show Fits s5.mem (out.withOffset 20) 32 from Fits.mono fit5 (by omega)))]
      rw [hs6]; rfl)]
  have hout6 : Fits s6.mem out 512 := by
    rw [hs6]; exact fits_splice hout5
  denote_step_all w 5
  denote_eval w 5 5
  simp -failIfUnchanged only [simp_spine] at hw5
  rw [env.out, env.off24] at hw5
  change w5 = PoisonOr.value (out.withOffset 24) at hw5
  subst hw5
  have fit6 := remainingFits s6.mem out hout6 (24 : BitVec 64) (by simp)
  norm_num at fit6
  obtain ⟨s7, hs7⟩ : ∃ t : GlobalState,
      t = {s6 with mem := s6.mem.splice (out.withOffset 24) (x 6)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s7)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx6]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 6)) rfl
        (show Fits s6.mem (out.withOffset 24) 32 from Fits.mono fit6 (by omega)))]
      rw [hs7]; rfl)]
  have hout7 : Fits s7.mem out 512 := by
    rw [hs7]; exact fits_splice hout6
  denote_step_all w 6
  denote_eval w 6 6
  simp -failIfUnchanged only [simp_spine] at hw6
  rw [env.out, env.off28] at hw6
  change w6 = PoisonOr.value (out.withOffset 28) at hw6
  subst hw6
  have fit7 := remainingFits s7.mem out hout7 (28 : BitVec 64) (by simp)
  norm_num at fit7
  obtain ⟨s8, hs8⟩ : ∃ t : GlobalState,
      t = {s7 with mem := s7.mem.splice (out.withOffset 28) (x 7)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s8)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx7]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 7)) rfl
        (show Fits s7.mem (out.withOffset 28) 32 from Fits.mono fit7 (by omega)))]
      rw [hs8]; rfl)]
  have hout8 : Fits s8.mem out 512 := by
    rw [hs8]; exact fits_splice hout7
  denote_step_all w 7
  denote_eval w 7 7
  simp -failIfUnchanged only [simp_spine] at hw7
  rw [env.out, env.off32] at hw7
  change w7 = PoisonOr.value (out.withOffset 32) at hw7
  subst hw7
  have fit8 := remainingFits s8.mem out hout8 (32 : BitVec 64) (by simp)
  norm_num at fit8
  obtain ⟨s9, hs9⟩ : ∃ t : GlobalState,
      t = {s8 with mem := s8.mem.splice (out.withOffset 32) (x 8)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s9)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx8]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 8)) rfl
        (show Fits s8.mem (out.withOffset 32) 32 from Fits.mono fit8 (by omega)))]
      rw [hs9]; rfl)]
  have hout9 : Fits s9.mem out 512 := by
    rw [hs9]; exact fits_splice hout8
  denote_step_all w 8
  denote_eval w 8 8
  simp -failIfUnchanged only [simp_spine] at hw8
  rw [env.out, env.off36] at hw8
  change w8 = PoisonOr.value (out.withOffset 36) at hw8
  subst hw8
  have fit9 := remainingFits s9.mem out hout9 (36 : BitVec 64) (by simp)
  norm_num at fit9
  obtain ⟨s10, hs10⟩ : ∃ t : GlobalState,
      t = {s9 with mem := s9.mem.splice (out.withOffset 36) (x 9)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s10)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx9]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 9)) rfl
        (show Fits s9.mem (out.withOffset 36) 32 from Fits.mono fit9 (by omega)))]
      rw [hs10]; rfl)]
  have hout10 : Fits s10.mem out 512 := by
    rw [hs10]; exact fits_splice hout9
  denote_step_all w 9
  denote_eval w 9 9
  simp -failIfUnchanged only [simp_spine] at hw9
  rw [env.out, env.off40] at hw9
  change w9 = PoisonOr.value (out.withOffset 40) at hw9
  subst hw9
  have fit10 := remainingFits s10.mem out hout10 (40 : BitVec 64) (by simp)
  norm_num at fit10
  obtain ⟨s11, hs11⟩ : ∃ t : GlobalState,
      t = {s10 with mem := s10.mem.splice (out.withOffset 40) (x 10)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s11)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx10]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 10)) rfl
        (show Fits s10.mem (out.withOffset 40) 32 from Fits.mono fit10 (by omega)))]
      rw [hs11]; rfl)]
  have hout11 : Fits s11.mem out 512 := by
    rw [hs11]; exact fits_splice hout10
  denote_step_all w 10
  denote_eval w 10 10
  simp -failIfUnchanged only [simp_spine] at hw10
  rw [env.out, env.off44] at hw10
  change w10 = PoisonOr.value (out.withOffset 44) at hw10
  subst hw10
  have fit11 := remainingFits s11.mem out hout11 (44 : BitVec 64) (by simp)
  norm_num at fit11
  obtain ⟨s12, hs12⟩ : ∃ t : GlobalState,
      t = {s11 with mem := s11.mem.splice (out.withOffset 44) (x 11)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s12)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx11]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 11)) rfl
        (show Fits s11.mem (out.withOffset 44) 32 from Fits.mono fit11 (by omega)))]
      rw [hs12]; rfl)]
  have hout12 : Fits s12.mem out 512 := by
    rw [hs12]; exact fits_splice hout11
  denote_step_all w 11
  denote_eval w 11 11
  simp -failIfUnchanged only [simp_spine] at hw11
  rw [env.out, env.off48] at hw11
  change w11 = PoisonOr.value (out.withOffset 48) at hw11
  subst hw11
  have fit12 := remainingFits s12.mem out hout12 (48 : BitVec 64) (by simp)
  norm_num at fit12
  obtain ⟨s13, hs13⟩ : ∃ t : GlobalState,
      t = {s12 with mem := s12.mem.splice (out.withOffset 48) (x 12)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s13)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx12]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 12)) rfl
        (show Fits s12.mem (out.withOffset 48) 32 from Fits.mono fit12 (by omega)))]
      rw [hs13]; rfl)]
  have hout13 : Fits s13.mem out 512 := by
    rw [hs13]; exact fits_splice hout12
  denote_step_all w 12
  denote_eval w 12 12
  simp -failIfUnchanged only [simp_spine] at hw12
  rw [env.out, env.off52] at hw12
  change w12 = PoisonOr.value (out.withOffset 52) at hw12
  subst hw12
  have fit13 := remainingFits s13.mem out hout13 (52 : BitVec 64) (by simp)
  norm_num at fit13
  obtain ⟨s14, hs14⟩ : ∃ t : GlobalState,
      t = {s13 with mem := s13.mem.splice (out.withOffset 52) (x 13)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s14)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx13]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 13)) rfl
        (show Fits s13.mem (out.withOffset 52) 32 from Fits.mono fit13 (by omega)))]
      rw [hs14]; rfl)]
  have hout14 : Fits s14.mem out 512 := by
    rw [hs14]; exact fits_splice hout13
  denote_step_all w 13
  denote_eval w 13 13
  simp -failIfUnchanged only [simp_spine] at hw13
  rw [env.out, env.off56] at hw13
  change w13 = PoisonOr.value (out.withOffset 56) at hw13
  subst hw13
  have fit14 := remainingFits s14.mem out hout14 (56 : BitVec 64) (by simp)
  norm_num at fit14
  obtain ⟨s15, hs15⟩ : ∃ t : GlobalState,
      t = {s14 with mem := s14.mem.splice (out.withOffset 56) (x 14)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s15)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx14]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 14)) rfl
        (show Fits s14.mem (out.withOffset 56) 32 from Fits.mono fit14 (by omega)))]
      rw [hs15]; rfl)]
  have hout15 : Fits s15.mem out 512 := by
    rw [hs15]; exact fits_splice hout14
  denote_step_all w 14
  denote_eval w 14 14
  simp -failIfUnchanged only [simp_spine] at hw14
  rw [env.out, env.off60] at hw14
  change w14 = PoisonOr.value (out.withOffset 60) at hw14
  subst hw14
  have fit15 := remainingFits s15.mem out hout15 (60 : BitVec 64) (by simp)
  norm_num at fit15
  obtain ⟨s16, hs16⟩ : ∃ t : GlobalState,
      t = {s15 with mem := s15.mem.splice (out.withOffset 60) (x 15)} := ⟨_, rfl⟩
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s16)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      simp -failIfUnchanged only [hx15]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value (x 15)) rfl
        (show Fits s15.mem (out.withOffset 60) 32 from Fits.mono fit15 (by omega)))]
      rw [hs16]; rfl)]
  simp_return
  have state1 := portableStateStep out x s 0 s s1 rfl
    (by rw [show Fin.ofNat 16 0 = (0 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs1)
  have state2 := portableStateStep out x s 1 s1 s2 state1
    (by rw [show Fin.ofNat 16 1 = (1 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs2)
  have state3 := portableStateStep out x s 2 s2 s3 state2
    (by rw [show Fin.ofNat 16 2 = (2 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs3)
  have state4 := portableStateStep out x s 3 s3 s4 state3
    (by rw [show Fin.ofNat 16 3 = (3 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs4)
  have state5 := portableStateStep out x s 4 s4 s5 state4
    (by rw [show Fin.ofNat 16 4 = (4 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs5)
  have state6 := portableStateStep out x s 5 s5 s6 state5
    (by rw [show Fin.ofNat 16 5 = (5 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs6)
  have state7 := portableStateStep out x s 6 s6 s7 state6
    (by rw [show Fin.ofNat 16 6 = (6 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs7)
  have state8 := portableStateStep out x s 7 s7 s8 state7
    (by rw [show Fin.ofNat 16 7 = (7 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs8)
  have state9 := portableStateStep out x s 8 s8 s9 state8
    (by rw [show Fin.ofNat 16 8 = (8 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs9)
  have state10 := portableStateStep out x s 9 s9 s10 state9
    (by rw [show Fin.ofNat 16 9 = (9 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs10)
  have state11 := portableStateStep out x s 10 s10 s11 state10
    (by rw [show Fin.ofNat 16 10 = (10 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs11)
  have state12 := portableStateStep out x s 11 s11 s12 state11
    (by rw [show Fin.ofNat 16 11 = (11 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs12)
  have state13 := portableStateStep out x s 12 s12 s13 state12
    (by rw [show Fin.ofNat 16 12 = (12 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs13)
  have state14 := portableStateStep out x s 13 s13 s14 state13
    (by rw [show Fin.ofNat 16 13 = (13 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs14)
  have state15 := portableStateStep out x s 14 s14 s15 state14
    (by rw [show Fin.ofNat 16 14 = (14 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs15)
  have state16 := portableStateStep out x s 15 s15 s16 state15
    (by rw [show Fin.ofNat 16 15 = (15 : Fin 16) from rfl]; simpa [Pointer.withOffset] using hs16)
  rw [state16, ← portableCompressionMemory_eq_outputMem]

end AgaveLatticeHash.MLIR.PortableXof
