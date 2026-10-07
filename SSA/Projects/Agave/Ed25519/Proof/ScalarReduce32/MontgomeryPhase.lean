import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.MontgomeryChunks
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.MontgomeryPhaseBounds

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

structure MontgomeryReady (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Prop where
  z0 : E.read (%178) = .value (z 0)
  z1 : E.read (%182) = .value (z 1)
  z2 : E.read (%188) = .value (z 2)
  z3 : E.read (%196) = .value (z 3)
  z4 : E.read (%206) = .value (z 4)
  z5 : E.read (%213) = .value (z 5)
  z6 : E.read (%218) = .value (z 6)
  z7 : E.read (%221) = .value (z 7)
  z8 : E.read (%222) = .value (z 8)
  c23 : E.read (%23) = .value 4503599627370495#64
  c29 : E.read (%29) = .value 1439961107955227#64
  c30 : E.read (%30) = .value 671914833335277#128
  c31 : E.read (%31) = .value 52#128
  c32 : E.read (%32) = .value 3916664325105025#128
  c33 : E.read (%33) = .value 1367801#128
  c34 : E.read (%34) = .value 44#128

def montgomeryPhaseEnv (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  let E0 := E
  let t0 := z 0
  let d0 := cancellationDigit t0
  let c0 := cancellationCarry t0
  let E1 := cancellationEnv0 E0 t0
  let t1 := carryGapSum0 d0 (z 1) c0
  let E2 := carryGapEnv0 E1 d0 (z 1) c0
  let d1 := cancellationDigit t1
  let c1 := cancellationCarry t1
  let E3 := cancellationEnv1 E2 t1
  let t2 := carryGapSum1 d0 d1 (z 2) c1
  let E4 := carryGapEnv1 E3 d0 d1 (z 2) c1
  let d2 := cancellationDigit t2
  let c2 := cancellationCarry t2
  let E5 := cancellationEnv2 E4 t2
  let t3 := carryGapSum2 d1 d2 (z 3) c2
  let E6 := carryGapEnv2 E5 d1 d2 (z 3) c2
  let d3 := cancellationDigit t3
  let c3 := cancellationCarry t3
  let E7 := cancellationEnv3 E6 t3
  let t4 := carryGapSum3 d0 d2 d3 (z 4) c3
  let E8 := carryGapEnv3 E7 d0 d2 d3 (z 4) c3
  let d4 := cancellationDigit t4
  let c4 := cancellationCarry t4
  let E9 := cancellationEnv4 E8 t4
  let t5 := carryGapSum4 d1 d3 d4 (z 5) c4
  let E10 := carryGapEnv4 E9 d1 d3 d4 (z 5) c4
  let t6 := carryGapSum5 d2 d4 (z 6) (t5 >>> 52)
  let E11 := carryGapEnv5 E10 d2 d4 (z 6) (t5 >>> 52)
  let t7 := carryGapSum6 d3 (z 7) (t6 >>> 52)
  let E12 := carryGapEnv6 E11 d3 (z 7) (t6 >>> 52)
  let t8 := carryGapSum7 d4 (z 8) (t7 >>> 52)
  let E13 := carryGapEnv7 E12 d4 (z 8) (t7 >>> 52)
  E13

/-- Complete execution of all 86 Montgomery instructions from the nine
bounded product columns. No call or phase-execution hypothesis is supplied. -/
theorem montgomery_phase (E : Env program.Γ) (s : GlobalState)
    (z : Fin 9 → BitVec 128) (hr : MontgomeryReady E z)
    (hz : ∀ i, (z i).toNat < 2 ^ 107) :
    List.foldlM Instr.run E montgomery s = .value (montgomeryPhaseEnv E z, s) := by
  let E0 := E
  let t0 := z 0
  let d0 := cancellationDigit t0
  let c0 := cancellationCarry t0
  let E1 := cancellationEnv0 E0 t0
  let t1 := carryGapSum0 d0 (z 1) c0
  let E2 := carryGapEnv0 E1 d0 (z 1) c0
  let d1 := cancellationDigit t1
  let c1 := cancellationCarry t1
  let E3 := cancellationEnv1 E2 t1
  let t2 := carryGapSum1 d0 d1 (z 2) c1
  let E4 := carryGapEnv1 E3 d0 d1 (z 2) c1
  let d2 := cancellationDigit t2
  let c2 := cancellationCarry t2
  let E5 := cancellationEnv2 E4 t2
  let t3 := carryGapSum2 d1 d2 (z 3) c2
  let E6 := carryGapEnv2 E5 d1 d2 (z 3) c2
  let d3 := cancellationDigit t3
  let c3 := cancellationCarry t3
  let E7 := cancellationEnv3 E6 t3
  let t4 := carryGapSum3 d0 d2 d3 (z 4) c3
  let E8 := carryGapEnv3 E7 d0 d2 d3 (z 4) c3
  let d4 := cancellationDigit t4
  let c4 := cancellationCarry t4
  let E9 := cancellationEnv4 E8 t4
  let t5 := carryGapSum4 d1 d3 d4 (z 5) c4
  let E10 := carryGapEnv4 E9 d1 d3 d4 (z 5) c4
  let t6 := carryGapSum5 d2 d4 (z 6) (t5 >>> 52)
  let E11 := carryGapEnv5 E10 d2 d4 (z 6) (t5 >>> 52)
  let t7 := carryGapSum6 d3 (z 7) (t6 >>> 52)
  let E12 := carryGapEnv6 E11 d3 (z 7) (t6 >>> 52)
  let t8 := carryGapSum7 d4 (z 8) (t7 >>> 52)
  let E13 := carryGapEnv7 E12 d4 (z 8) (t7 >>> 52)
  have hzc (i : Fin 9) : (z i).toNat < 2 ^ 110 := (hz i).trans (by decide)
  have ht0 : t0.toNat < 2 ^ 120 := (hz 0).trans (by decide)
  have hd0 := cancellationDigit_bound t0
  have hc0 := cancellationCarry_bound t0 ht0
  have he1 := cancellation_chunk0 E0 s t0 ht0
    (by simpa [E0, mlir_env] using hr.z0)
    (by simpa [E0, mlir_env] using hr.c29)
    (by simpa [E0, mlir_env] using hr.c23)
    (by simpa [E0, mlir_env] using hr.c30)
    (by simpa [E0, mlir_env] using hr.c31)
  change List.foldlM Instr.run E0 cancellationBlock0.body s = .value (E1, s) at he1
  have ht1 := carryGapSum0_bound d0 (z 1) c0 hd0 (hzc 1) hc0
  have he2 := carry_gap0 E1 s d0 (z 1) c0
    hd0
    (by simp [E0, E1, cancellationEnv0, mlir_env] <;> rfl)
    (hzc 1)
    (by simpa [E0, E1, cancellationEnv0, mlir_env] using hr.z1)
    hc0
    (by simp [E0, E1, cancellationEnv0, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, mlir_env] using hr.c32)
  change List.foldlM Instr.run E1 carryGapBlock0.body s = .value (E2, s) at he2
  have hd1 := cancellationDigit_bound t1
  have hc1 := cancellationCarry_bound t1 ht1
  have he3 := cancellation_chunk1 E2 s t1 ht1
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, t1, carryGapSum0, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, t1, carryGapSum0, mlir_env] using hr.c29)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, t1, carryGapSum0, mlir_env] using hr.c23)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, t1, carryGapSum0, mlir_env] using hr.c30)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, t1, carryGapSum0, mlir_env] using hr.c31)
  change List.foldlM Instr.run E2 cancellationBlock1.body s = .value (E3, s) at he3
  have ht2 := carryGapSum1_bound d0 d1 (z 2) c1 hd0 hd1 (hzc 2) hc1
  have he4 := carry_gap1 E3 s d0 d1 (z 2) c1
    hd0
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, t1, carryGapSum0, mlir_env] <;> rfl)
    hd1
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, t1, carryGapSum0, mlir_env] <;> rfl)
    (hzc 2)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, t1, carryGapSum0, mlir_env] using hr.z2)
    hc1
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, t1, carryGapSum0, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, t1, carryGapSum0, mlir_env] using hr.c32)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, t1, carryGapSum0, mlir_env] using hr.c33)
  change List.foldlM Instr.run E3 carryGapBlock1.body s = .value (E4, s) at he4
  have hd2 := cancellationDigit_bound t2
  have hc2 := cancellationCarry_bound t2 ht2
  have he5 := cancellation_chunk2 E4 s t2 ht2
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, t1, carryGapSum0, t2, carryGapSum1, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, t1, carryGapSum0, t2, carryGapSum1, mlir_env] using hr.c29)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, t1, carryGapSum0, t2, carryGapSum1, mlir_env] using hr.c23)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, t1, carryGapSum0, t2, carryGapSum1, mlir_env] using hr.c30)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, t1, carryGapSum0, t2, carryGapSum1, mlir_env] using hr.c31)
  change List.foldlM Instr.run E4 cancellationBlock2.body s = .value (E5, s) at he5
  have ht3 := carryGapSum2_bound d1 d2 (z 3) c2 hd1 hd2 (hzc 3) hc2
  have he6 := carry_gap2 E5 s d1 d2 (z 3) c2
    hd1
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, t1, carryGapSum0, t2, carryGapSum1, mlir_env] <;> rfl)
    hd2
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, t1, carryGapSum0, t2, carryGapSum1, mlir_env] <;> rfl)
    (hzc 3)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, t1, carryGapSum0, t2, carryGapSum1, mlir_env] using hr.z3)
    hc2
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, t1, carryGapSum0, t2, carryGapSum1, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, t1, carryGapSum0, t2, carryGapSum1, mlir_env] using hr.c32)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, t1, carryGapSum0, t2, carryGapSum1, mlir_env] using hr.c33)
  change List.foldlM Instr.run E5 carryGapBlock2.body s = .value (E6, s) at he6
  have hd3 := cancellationDigit_bound t3
  have hc3 := cancellationCarry_bound t3 ht3
  have he7 := cancellation_chunk3 E6 s t3 ht3
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] using hr.c29)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] using hr.c23)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] using hr.c30)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] using hr.c31)
  change List.foldlM Instr.run E6 cancellationBlock3.body s = .value (E7, s) at he7
  have ht4 := carryGapSum3_bound d0 d2 d3 (z 4) c3 hd0 hd2 hd3 (hzc 4) hc3
  have he8 := carry_gap3 E7 s d0 d2 d3 (z 4) c3
    hd0
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] <;> rfl)
    hd2
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] <;> rfl)
    hd3
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] <;> rfl)
    (hzc 4)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] using hr.z4)
    hc3
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] using hr.c32)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] using hr.c33)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, mlir_env] using hr.c34)
  change List.foldlM Instr.run E7 carryGapBlock3.body s = .value (E8, s) at he8
  have hd4 := cancellationDigit_bound t4
  have hc4 := cancellationCarry_bound t4 ht4
  have he9 := cancellation_chunk4 E8 s t4 ht4
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.c29)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.c23)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.c30)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.c31)
  change List.foldlM Instr.run E8 cancellationBlock4.body s = .value (E9, s) at he9
  have ht5 := carryGapSum4_bound d1 d3 d4 (z 5) c4 hd1 hd3 hd4 (hzc 5) hc4
  have he10 := carry_gap4 E9 s d1 d3 d4 (z 5) c4
    hd1
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] <;> rfl)
    hd3
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] <;> rfl)
    hd4
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] <;> rfl)
    (hzc 5)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.z5)
    hc4
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.c23)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.c31)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.c32)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.c33)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, mlir_env] using hr.c34)
  change List.foldlM Instr.run E9 carryGapBlock4.body s = .value (E10, s) at he10
  have ht6 := carryGapSum5_bound d2 d4 (z 6) (t5 >>> 52) hd2 hd4 (hzc 6) (shifted_carry_bound t5 ht5)
  have he11 := carry_gap5 E10 s d2 d4 (z 6) (t5 >>> 52)
    hd2
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, mlir_env] <;> rfl)
    hd4
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, mlir_env] <;> rfl)
    (hzc 6)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, mlir_env] using hr.z6)
    (shifted_carry_bound t5 ht5)
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, mlir_env] using hr.c23)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, mlir_env] using hr.c31)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, mlir_env] using hr.c33)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, mlir_env] using hr.c34)
  change List.foldlM Instr.run E10 carryGapBlock5.body s = .value (E11, s) at he11
  have ht7 := carryGapSum6_bound d3 (z 7) (t6 >>> 52) hd3 (hzc 7) (shifted_carry_bound t6 ht6)
  have he12 := carry_gap6 E11 s d3 (z 7) (t6 >>> 52)
    hd3
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, mlir_env] <;> rfl)
    (hzc 7)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, mlir_env] using hr.z7)
    (shifted_carry_bound t6 ht6)
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, mlir_env] using hr.c23)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, mlir_env] using hr.c31)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, mlir_env] using hr.c34)
  change List.foldlM Instr.run E11 carryGapBlock6.body s = .value (E12, s) at he12
  have ht8 := carryGapSum7_bound d4 (z 8) (t7 >>> 52) hd4 (hzc 8) (shifted_carry_bound t7 ht7)
  have he13 := carry_gap7 E12 s d4 (z 8) (t7 >>> 52)
    hd4
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, E12, carryGapEnv6, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, t7, carryGapSum6, mlir_env] <;> rfl)
    (hzc 8)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, E12, carryGapEnv6, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, t7, carryGapSum6, mlir_env] using hr.z8)
    (shifted_carry_bound t7 ht7)
    (by simp [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, E12, carryGapEnv6, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, t7, carryGapSum6, mlir_env] <;> rfl)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, E12, carryGapEnv6, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, t7, carryGapSum6, mlir_env] using hr.c23)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, E12, carryGapEnv6, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, t7, carryGapSum6, mlir_env] using hr.c31)
    (by simpa [E0, E1, cancellationEnv0, E2, carryGapEnv0, E3, cancellationEnv1, E4, carryGapEnv1, E5, cancellationEnv2, E6, carryGapEnv2, E7, cancellationEnv3, E8, carryGapEnv3, E9, cancellationEnv4, E10, carryGapEnv4, E11, carryGapEnv5, E12, carryGapEnv6, t1, carryGapSum0, t2, carryGapSum1, t3, carryGapSum2, t4, carryGapSum3, t5, carryGapSum4, t6, carryGapSum5, t7, carryGapSum6, mlir_env] using hr.c34)
  change List.foldlM Instr.run E12 carryGapBlock7.body s = .value (E13, s) at he13
  have hf : List.foldlM Instr.run E0 montgomery s = .value (E13, s) := by
    rw [montgomery_body_decomposition]
    simp only [List.foldlM_append, EffectM.bind_eq, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12, he13, PoisonOr.value_bind]
  exact hf

end Agave.Ed25519.ScalarReduce32.Execution
