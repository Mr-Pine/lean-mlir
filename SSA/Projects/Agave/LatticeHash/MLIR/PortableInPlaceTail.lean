import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceData
import SSA.Projects.Agave.LatticeHash.MLIR.PortableStores
namespace AgaveLatticeHash.MLIR.PortableInPlace
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionExit
open InstCombine (LLVM)
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

def resultVars : Vector (rounds.middle.Var (SLLVM.Ty.bitvec 32)) 16 :=
  #v[⟨47, rfl⟩, ⟨33, rfl⟩, ⟨19, rfl⟩, ⟨5, rfl⟩, ⟨0, rfl⟩, ⟨42, rfl⟩, ⟨28, rfl⟩, ⟨14, rfl⟩, ⟨16, rfl⟩, ⟨2, rfl⟩, ⟨44, rfl⟩, ⟨30, rfl⟩, ⟨31, rfl⟩, ⟨17, rfl⟩, ⟨3, rfl⟩, ⟨45, rfl⟩]
def resultVar (i : Fin 16) := resultVars[i]

structure TailEnv (V : rounds.middle.Valuation) (cvp : Pointer) : Prop where
  ptr0 : V ⟨862, rfl⟩ = .value (cvp.withOffset 0)
  ptr1 : V ⟨802, rfl⟩ = .value (cvp.withOffset 4)
  ptr2 : V ⟨800, rfl⟩ = .value (cvp.withOffset 8)
  ptr3 : V ⟨798, rfl⟩ = .value (cvp.withOffset 12)
  ptr4 : V ⟨796, rfl⟩ = .value (cvp.withOffset 16)
  ptr5 : V ⟨794, rfl⟩ = .value (cvp.withOffset 20)
  ptr6 : V ⟨792, rfl⟩ = .value (cvp.withOffset 24)
  ptr7 : V ⟨790, rfl⟩ = .value (cvp.withOffset 28)

/-- Exactly the eight CV stores emitted by compress_in_place. -/
def cvMemory (m : MemoryState) (cvp : Pointer) (x : State Word) : MemoryState :=
  outputMem cvp (fun i => #v[x i]) 8 m

theorem tail_run (V : rounds.middle.Valuation) (cvp : Pointer) (x : State Word) (cv : CV Word)
    (env : TailEnv V cvp) (hx : ∀ i, V (resultVar i) = .value (x i))
    (s : GlobalState) (hcvp : Fits s.mem cvp 256) :
    StateT.run ((rounds.tail.denote V) >>= fun _ =>
      pure ([]ₕ : HVector (fun t : SLLVM.Ty => TyDenote.toType t) [])) s =
    .value ([]ₕ, {s with mem := cvMemory s.mem cvp (feedForward (· ^^^ ·) cv x)}) := by
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
  dsimp only [rounds]
  denote_number_from 0
  denote_step_all z 0
  denote_eval z 0 0
  simp -failIfUnchanged only [simp_spine] at hz0
  simp only [hx0, hx8] at hz0
  have ez0 : z0 = PoisonOr.value ((feedForward (· ^^^ ·) cv x) 0) := by
    simpa [feedForward, LLVM.xor, simp_llvm, BitVec.xor_comm] using hz0
  subst ez0
  have fit0 := remainingFits s.mem cvp hcvp (0 : BitVec 64) (by simp)
  norm_num at fit0
  obtain ⟨s1, hs1⟩ : ∃ t : GlobalState,
    t = {s with mem := s.mem.splice (cvp.withOffset 0) ((feedForward (· ^^^ ·) cv x) 0)} := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s1)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      rw [env.ptr0]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value ((feedForward (· ^^^ ·) cv x) 0)) rfl
        (show Fits s.mem (cvp.withOffset 0) 32 from Fits.mono fit0 (by omega)))]
      rw [hs1]; rfl)]
  have hcvp1 : Fits s1.mem cvp 256 := by
    rw [hs1]; exact fits_splice hcvp
  denote_step_all z 1
  denote_eval z 1 1
  simp -failIfUnchanged only [simp_spine] at hz1
  simp only [hx1, hx9] at hz1
  have ez1 : z1 = PoisonOr.value ((feedForward (· ^^^ ·) cv x) 1) := by
    simpa [feedForward, LLVM.xor, simp_llvm, BitVec.xor_comm] using hz1
  subst ez1
  have fit1 := remainingFits s1.mem cvp hcvp1 (4 : BitVec 64) (by simp)
  norm_num at fit1
  obtain ⟨s2, hs2⟩ : ∃ t : GlobalState,
    t = {s1 with mem := s1.mem.splice (cvp.withOffset 4) ((feedForward (· ^^^ ·) cv x) 1)} := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s2)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      rw [env.ptr1]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value ((feedForward (· ^^^ ·) cv x) 1)) rfl
        (show Fits s1.mem (cvp.withOffset 4) 32 from Fits.mono fit1 (by omega)))]
      rw [hs2]; rfl)]
  have hcvp2 : Fits s2.mem cvp 256 := by
    rw [hs2]; exact fits_splice hcvp1
  denote_step_all z 2
  denote_eval z 2 2
  simp -failIfUnchanged only [simp_spine] at hz2
  simp only [hx2, hx10] at hz2
  have ez2 : z2 = PoisonOr.value ((feedForward (· ^^^ ·) cv x) 2) := by
    simpa [feedForward, LLVM.xor, simp_llvm, BitVec.xor_comm] using hz2
  subst ez2
  have fit2 := remainingFits s2.mem cvp hcvp2 (8 : BitVec 64) (by simp)
  norm_num at fit2
  obtain ⟨s3, hs3⟩ : ∃ t : GlobalState,
    t = {s2 with mem := s2.mem.splice (cvp.withOffset 8) ((feedForward (· ^^^ ·) cv x) 2)} := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s3)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      rw [env.ptr2]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value ((feedForward (· ^^^ ·) cv x) 2)) rfl
        (show Fits s2.mem (cvp.withOffset 8) 32 from Fits.mono fit2 (by omega)))]
      rw [hs3]; rfl)]
  have hcvp3 : Fits s3.mem cvp 256 := by
    rw [hs3]; exact fits_splice hcvp2
  denote_step_all z 3
  denote_eval z 3 3
  simp -failIfUnchanged only [simp_spine] at hz3
  simp only [hx3, hx11] at hz3
  have ez3 : z3 = PoisonOr.value ((feedForward (· ^^^ ·) cv x) 3) := by
    simpa [feedForward, LLVM.xor, simp_llvm, BitVec.xor_comm] using hz3
  subst ez3
  have fit3 := remainingFits s3.mem cvp hcvp3 (12 : BitVec 64) (by simp)
  norm_num at fit3
  obtain ⟨s4, hs4⟩ : ∃ t : GlobalState,
    t = {s3 with mem := s3.mem.splice (cvp.withOffset 12) ((feedForward (· ^^^ ·) cv x) 3)} := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s4)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      rw [env.ptr3]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value ((feedForward (· ^^^ ·) cv x) 3)) rfl
        (show Fits s3.mem (cvp.withOffset 12) 32 from Fits.mono fit3 (by omega)))]
      rw [hs4]; rfl)]
  have hcvp4 : Fits s4.mem cvp 256 := by
    rw [hs4]; exact fits_splice hcvp3
  denote_step_all z 4
  denote_eval z 4 4
  simp -failIfUnchanged only [simp_spine] at hz4
  simp only [hx4, hx12] at hz4
  have ez4 : z4 = PoisonOr.value ((feedForward (· ^^^ ·) cv x) 4) := by
    simpa [feedForward, LLVM.xor, simp_llvm, BitVec.xor_comm] using hz4
  subst ez4
  have fit4 := remainingFits s4.mem cvp hcvp4 (16 : BitVec 64) (by simp)
  norm_num at fit4
  obtain ⟨s5, hs5⟩ : ∃ t : GlobalState,
    t = {s4 with mem := s4.mem.splice (cvp.withOffset 16) ((feedForward (· ^^^ ·) cv x) 4)} := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s5)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      rw [env.ptr4]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value ((feedForward (· ^^^ ·) cv x) 4)) rfl
        (show Fits s4.mem (cvp.withOffset 16) 32 from Fits.mono fit4 (by omega)))]
      rw [hs5]; rfl)]
  have hcvp5 : Fits s5.mem cvp 256 := by
    rw [hs5]; exact fits_splice hcvp4
  denote_step_all z 5
  denote_eval z 5 5
  simp -failIfUnchanged only [simp_spine] at hz5
  simp only [hx5, hx13] at hz5
  have ez5 : z5 = PoisonOr.value ((feedForward (· ^^^ ·) cv x) 5) := by
    simpa [feedForward, LLVM.xor, simp_llvm, BitVec.xor_comm] using hz5
  subst ez5
  have fit5 := remainingFits s5.mem cvp hcvp5 (20 : BitVec 64) (by simp)
  norm_num at fit5
  obtain ⟨s6, hs6⟩ : ∃ t : GlobalState,
    t = {s5 with mem := s5.mem.splice (cvp.withOffset 20) ((feedForward (· ^^^ ·) cv x) 5)} := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s6)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      rw [env.ptr5]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value ((feedForward (· ^^^ ·) cv x) 5)) rfl
        (show Fits s5.mem (cvp.withOffset 20) 32 from Fits.mono fit5 (by omega)))]
      rw [hs6]; rfl)]
  have hcvp6 : Fits s6.mem cvp 256 := by
    rw [hs6]; exact fits_splice hcvp5
  denote_step_all z 6
  denote_eval z 6 6
  simp -failIfUnchanged only [simp_spine] at hz6
  simp only [hx6, hx14] at hz6
  have ez6 : z6 = PoisonOr.value ((feedForward (· ^^^ ·) cv x) 6) := by
    simpa [feedForward, LLVM.xor, simp_llvm, BitVec.xor_comm] using hz6
  subst ez6
  have fit6 := remainingFits s6.mem cvp hcvp6 (24 : BitVec 64) (by simp)
  norm_num at fit6
  obtain ⟨s7, hs7⟩ : ∃ t : GlobalState,
    t = {s6 with mem := s6.mem.splice (cvp.withOffset 24) ((feedForward (· ^^^ ·) cv x) 6)} := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s7)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      rw [env.ptr6]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value ((feedForward (· ^^^ ·) cv x) 6)) rfl
        (show Fits s6.mem (cvp.withOffset 24) 32 from Fits.mono fit6 (by omega)))]
      rw [hs7]; rfl)]
  have hcvp7 : Fits s7.mem cvp 256 := by
    rw [hs7]; exact fits_splice hcvp6
  denote_step_all z 7
  denote_eval z 7 7
  simp -failIfUnchanged only [simp_spine] at hz7
  simp only [hx7, hx15] at hz7
  have ez7 : z7 = PoisonOr.value ((feedForward (· ^^^ ·) cv x) 7) := by
    simpa [feedForward, LLVM.xor, simp_llvm, BitVec.xor_comm] using hz7
  subst ez7
  have fit7 := remainingFits s7.mem cvp hcvp7 (28 : BitVec 64) (by simp)
  norm_num at fit7
  obtain ⟨s8, hs8⟩ : ∃ t : GlobalState,
    t = {s7 with mem := s7.mem.splice (cvp.withOffset 28) ((feedForward (· ^^^ ·) cv x) 7)} := ⟨_, rfl⟩
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s8)
    (by
      simp -failIfUnchanged only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp -failIfUnchanged only [simp_spine]
      rw [env.ptr7]
      rw [run_liftM (run_store (t := .bitvec (.concrete 32))
        (x := PoisonOr.value ((feedForward (· ^^^ ·) cv x) 7)) rfl
        (show Fits s7.mem (cvp.withOffset 28) 32 from Fits.mono fit7 (by omega)))]
      rw [hs8]; rfl)]
  simp_return
  have state1 := portableStateStep cvp (feedForward (· ^^^ ·) cv x) s 0 s s1 rfl
    (by rw [show Fin.ofNat 16 0 = (0 : Fin 16) from rfl]; exact hs1)
  have state2 := portableStateStep cvp (feedForward (· ^^^ ·) cv x) s 1 s1 s2 state1
    (by rw [show Fin.ofNat 16 1 = (1 : Fin 16) from rfl]; exact hs2)
  have state3 := portableStateStep cvp (feedForward (· ^^^ ·) cv x) s 2 s2 s3 state2
    (by rw [show Fin.ofNat 16 2 = (2 : Fin 16) from rfl]; exact hs3)
  have state4 := portableStateStep cvp (feedForward (· ^^^ ·) cv x) s 3 s3 s4 state3
    (by rw [show Fin.ofNat 16 3 = (3 : Fin 16) from rfl]; exact hs4)
  have state5 := portableStateStep cvp (feedForward (· ^^^ ·) cv x) s 4 s4 s5 state4
    (by rw [show Fin.ofNat 16 4 = (4 : Fin 16) from rfl]; exact hs5)
  have state6 := portableStateStep cvp (feedForward (· ^^^ ·) cv x) s 5 s5 s6 state5
    (by rw [show Fin.ofNat 16 5 = (5 : Fin 16) from rfl]; exact hs6)
  have state7 := portableStateStep cvp (feedForward (· ^^^ ·) cv x) s 6 s6 s7 state6
    (by rw [show Fin.ofNat 16 6 = (6 : Fin 16) from rfl]; exact hs7)
  have state8 := portableStateStep cvp (feedForward (· ^^^ ·) cv x) s 7 s7 s8 state7
    (by rw [show Fin.ofNat 16 7 = (7 : Fin 16) from rfl]; exact hs8)
  exact state8

end AgaveLatticeHash.MLIR.PortableInPlace
