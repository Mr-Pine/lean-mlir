import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreValues

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def chainState (m : MemoryState) (chain : Pointer) : State :=
  ⟨readBits m chain 64, readBits m (chain.withOffset (8 : BitVec 64)) 64,
    readBits m (chain.withOffset (16 : BitVec 64)) 64, readBits m (chain.withOffset (24 : BitVec 64)) 64,
    readBits m (chain.withOffset (32 : BitVec 64)) 64, readBits m (chain.withOffset (40 : BitVec 64)) 64,
    readBits m (chain.withOffset (48 : BitVec 64)) 64, readBits m (chain.withOffset (56 : BitVec 64)) 64⟩

macro "peel_core_load " p:term ", " hp:term ", " st:term : tactic =>
  `(tactic|
    (try simp only [bind_assoc]
     reduce_cfg_indices
     rw [BlockCom.run_bind_denote_var_of_value
       (x := PoisonOr.value (readBits (($st).mem) $p 64)) (s' := $st)
       (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
           rw [run_liftM (run_load_readBits (show Fits (($st).mem) $p 64 from $hp))]
           rfl)]))

/-- Actual source entry, through the first outer-loop edge. The continuation
receives the complete immutable SSA ambient environment, not an assumed one. -/
theorem entry_cont (before : GlobalState) (kp chain data : Pointer) (count : Word)
    (hwf : before.WF) (hc : SmallRange before.mem chain 64)
    (hg : GlobalPtr before "fd_sha512_core_ref.K" kp)
    (k : Ctxt.Valuation core.cfgCtx × (HVector toType [] ⊕ SuccArgs core.cfgSigs) → EffectM α) :
    StateT.run (core.cfgEntry.denote (Ctxt.Valuation.ofHVector
      [.value count, .value data, .value chain]ₕ) >>= k) before =
    StateT.run (k (ambient kp chain ⟨⟨before.alloc.nextFreeBlock⟩, 0⟩ data count
      (chainState before.mem chain), .inr (outerTarget (chainState before.mem chain) data count)))
      (before.afterAlloca 1024) := by
  denote_expose
  denote_step_all v 13
  denote_eval v 0 13
  simp only [LLVM.const?] at hv0
  have c0 : BitVec.ofInt 32 (1) = (1#32) := by decide
  rw [c0] at hv0
  simp only [LLVM.const?] at hv1
  have c1 : BitVec.ofInt 64 (8) = (8#64) := by decide
  rw [c1] at hv1
  simp only [LLVM.const?] at hv2
  have c2 : BitVec.ofInt 64 (16) = (16#64) := by decide
  rw [c2] at hv2
  simp only [LLVM.const?] at hv3
  have c3 : BitVec.ofInt 64 (24) = (24#64) := by decide
  rw [c3] at hv3
  simp only [LLVM.const?] at hv4
  have c4 : BitVec.ofInt 64 (32) = (32#64) := by decide
  rw [c4] at hv4
  simp only [LLVM.const?] at hv5
  have c5 : BitVec.ofInt 64 (40) = (40#64) := by decide
  rw [c5] at hv5
  simp only [LLVM.const?] at hv6
  have c6 : BitVec.ofInt 64 (48) = (48#64) := by decide
  rw [c6] at hv6
  simp only [LLVM.const?] at hv7
  have c7 : BitVec.ofInt 64 (56) = (56#64) := by decide
  rw [c7] at hv7
  simp only [LLVM.const?] at hv8
  have c8 : BitVec.ofInt 64 (0) = (0#64) := by decide
  rw [c8] at hv8
  simp only [LLVM.const?] at hv9
  have c9 : BitVec.ofInt 64 (3) = (3#64) := by decide
  rw [c9] at hv9
  simp only [LLVM.const?] at hv10
  have c10 : BitVec.ofInt 64 (50) = (50#64) := by decide
  rw [c10] at hv10
  simp only [LLVM.const?] at hv11
  have c11 : BitVec.ofInt 64 (46) = (46#64) := by decide
  rw [c11] at hv11
  simp only [LLVM.const?] at hv12
  have c12 : BitVec.ofInt 64 (23) = (23#64) := by decide
  rw [c12] at hv12
  simp only [LLVM.const?] at hv13
  have c13 : BitVec.ofInt 64 (-1) = (18446744073709551615#64) := by decide
  rw [c13] at hv13
  peel_addressof hg
  denote_step_all v 27
  denote_eval v 15 27
  simp only [LLVM.const?] at hv15
  have c15 : BitVec.ofInt 64 (36) = (36#64) := by decide
  rw [c15] at hv15
  simp only [LLVM.const?] at hv16
  have c16 : BitVec.ofInt 64 (30) = (30#64) := by decide
  rw [c16] at hv16
  simp only [LLVM.const?] at hv17
  have c17 : BitVec.ofInt 64 (25) = (25#64) := by decide
  rw [c17] at hv17
  simp only [LLVM.const?] at hv18
  have c18 : BitVec.ofInt 64 (1) = (1#64) := by decide
  rw [c18] at hv18
  simp only [LLVM.const?] at hv19
  have c19 : BitVec.ofInt 64 (15) = (15#64) := by decide
  rw [c19] at hv19
  simp only [LLVM.const?] at hv20
  have c20 : BitVec.ofInt 64 (14) = (14#64) := by decide
  rw [c20] at hv20
  simp only [LLVM.const?] at hv21
  have c21 : BitVec.ofInt 64 (63) = (63#64) := by decide
  rw [c21] at hv21
  simp only [LLVM.const?] at hv22
  have c22 : BitVec.ofInt 64 (7) = (7#64) := by decide
  rw [c22] at hv22
  simp only [LLVM.const?] at hv23
  have c23 : BitVec.ofInt 64 (45) = (45#64) := by decide
  rw [c23] at hv23
  simp only [LLVM.const?] at hv24
  have c24 : BitVec.ofInt 64 (6) = (6#64) := by decide
  rw [c24] at hv24
  simp only [LLVM.const?] at hv25
  have c25 : BitVec.ofInt 64 (9) = (9#64) := by decide
  rw [c25] at hv25
  simp only [LLVM.const?] at hv26
  have c26 : BitVec.ofInt 64 (80) = (80#64) := by decide
  rw [c26] at hv26
  simp only [LLVM.const?] at hv27
  have c27 : BitVec.ofInt 64 (128) = (128#64) := by decide
  rw [c27] at hv27
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27
  obtain ⟨middle, hm⟩ : ∃ t : GlobalState, t = before.afterAlloca 1024 := ⟨_, rfl⟩
  peel_alloca from before as middle with hm
  have hcm : SmallRange middle.mem chain 64 := by
    rw [hm]
    exact hc.afterAlloca hwf 1024
  peel_gep 8 with chain, hcm.fits, middle as ptr1
  peel_gep 16 with chain, hcm.fits, middle as ptr2
  peel_gep 24 with chain, hcm.fits, middle as ptr3
  peel_gep 32 with chain, hcm.fits, middle as ptr4
  peel_gep 40 with chain, hcm.fits, middle as ptr5
  peel_gep 48 with chain, hcm.fits, middle as ptr6
  peel_gep 56 with chain, hcm.fits, middle as ptr7
  have hf0 : Fits middle.mem chain 64 := (hcm.mono (by decide : 8 ≤ 64)).fits
  peel_core_load chain, hf0, middle
  have hf1 : Fits middle.mem ptr1 64 := Fits.mono hptr1 (by decide)
  peel_core_load ptr1, hf1, middle
  have hf2 : Fits middle.mem ptr2 64 := Fits.mono hptr2 (by decide)
  peel_core_load ptr2, hf2, middle
  have hf3 : Fits middle.mem ptr3 64 := Fits.mono hptr3 (by decide)
  peel_core_load ptr3, hf3, middle
  have hf4 : Fits middle.mem ptr4 64 := Fits.mono hptr4 (by decide)
  peel_core_load ptr4, hf4, middle
  have hf5 : Fits middle.mem ptr5 64 := Fits.mono hptr5 (by decide)
  peel_core_load ptr5, hf5, middle
  have hf6 : Fits middle.mem ptr6 64 := Fits.mono hptr6 (by decide)
  peel_core_load ptr6, hf6, middle
  have hf7 : Fits middle.mem ptr7 64 := Fits.mono hptr7 (by decide)
  peel_core_load ptr7, hf7, middle
  have hr0 : readBits middle.mem chain 64 = readBits before.mem chain 64 := by
    rw [hm, readBits_afterAlloca ((hc.mono (by decide : 8 ≤ 64)).fits) hwf]
  have hr1 : readBits middle.mem (chain.withOffset (8 : BitVec 64)) 64 = readBits before.mem (chain.withOffset (8 : BitVec 64)) 64 := by
    rw [hm]
    exact readBits_afterAlloca (show Fits before.mem (chain.withOffset (8 : BitVec 64)) 64 from (hc.add (k := 8) (n := 8) (by decide)).fits) hwf 1024
  have hr2 : readBits middle.mem (chain.withOffset (16 : BitVec 64)) 64 = readBits before.mem (chain.withOffset (16 : BitVec 64)) 64 := by
    rw [hm]
    exact readBits_afterAlloca (show Fits before.mem (chain.withOffset (16 : BitVec 64)) 64 from (hc.add (k := 16) (n := 8) (by decide)).fits) hwf 1024
  have hr3 : readBits middle.mem (chain.withOffset (24 : BitVec 64)) 64 = readBits before.mem (chain.withOffset (24 : BitVec 64)) 64 := by
    rw [hm]
    exact readBits_afterAlloca (show Fits before.mem (chain.withOffset (24 : BitVec 64)) 64 from (hc.add (k := 24) (n := 8) (by decide)).fits) hwf 1024
  have hr4 : readBits middle.mem (chain.withOffset (32 : BitVec 64)) 64 = readBits before.mem (chain.withOffset (32 : BitVec 64)) 64 := by
    rw [hm]
    exact readBits_afterAlloca (show Fits before.mem (chain.withOffset (32 : BitVec 64)) 64 from (hc.add (k := 32) (n := 8) (by decide)).fits) hwf 1024
  have hr5 : readBits middle.mem (chain.withOffset (40 : BitVec 64)) 64 = readBits before.mem (chain.withOffset (40 : BitVec 64)) 64 := by
    rw [hm]
    exact readBits_afterAlloca (show Fits before.mem (chain.withOffset (40 : BitVec 64)) 64 from (hc.add (k := 40) (n := 8) (by decide)).fits) hwf 1024
  have hr6 : readBits middle.mem (chain.withOffset (48 : BitVec 64)) 64 = readBits before.mem (chain.withOffset (48 : BitVec 64)) 64 := by
    rw [hm]
    exact readBits_afterAlloca (show Fits before.mem (chain.withOffset (48 : BitVec 64)) 64 from (hc.add (k := 48) (n := 8) (by decide)).fits) hwf 1024
  have hr7 : readBits middle.mem (chain.withOffset (56 : BitVec 64)) 64 = readBits before.mem (chain.withOffset (56 : BitVec 64)) 64 := by
    rw [hm]
    exact readBits_afterAlloca (show Fits before.mem (chain.withOffset (56 : BitVec 64)) 64 from (hc.add (k := 56) (n := 8) (by decide)).fits) hwf 1024
  simp only [ptr1, ptr2, ptr3, ptr4, ptr5, ptr6, ptr7]
  rw [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7]
  simp only [BlockCom.denote_term,
    Terminator.denote_br, Target.denote, ambient, chainState, outerTarget,
    EffectM.run_bind, EffectM.run_pure, PoisonOr.value_bind, hm, simp_denote, simp_sllvm]
  rfl

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
