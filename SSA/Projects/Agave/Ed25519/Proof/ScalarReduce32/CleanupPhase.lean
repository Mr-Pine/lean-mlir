import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Cleanup

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

structure CleanupReady (E : Env program.Γ) (scratch : Fin 33 → Pointer) : Prop where
  p62 : E.read (%62) = .value (scratch 0)
  p63 : E.read (%63) = .value (scratch 1)
  p64 : E.read (%64) = .value (scratch 2)
  p65 : E.read (%65) = .value (scratch 3)
  p66 : E.read (%66) = .value (scratch 4)
  p67 : E.read (%67) = .value (scratch 5)
  p68 : E.read (%68) = .value (scratch 6)
  p69 : E.read (%69) = .value (scratch 7)
  p70 : E.read (%70) = .value (scratch 8)
  p71 : E.read (%71) = .value (scratch 9)
  p76 : E.read (%76) = .value (scratch 14)
  p77 : E.read (%77) = .value (scratch 15)
  p78 : E.read (%78) = .value (scratch 16)
  p79 : E.read (%79) = .value (scratch 17)
  p80 : E.read (%80) = .value (scratch 18)
  p81 : E.read (%81) = .value (scratch 19)
  p82 : E.read (%82) = .value (scratch 20)
  p83 : E.read (%83) = .value (scratch 21)
  p84 : E.read (%84) = .value (scratch 22)
  p85 : E.read (%85) = .value (scratch 23)
  p86 : E.read (%86) = .value (scratch 24)
  p87 : E.read (%87) = .value (scratch 25)
  p88 : E.read (%88) = .value (scratch 26)
  p89 : E.read (%89) = .value (scratch 27)
  p90 : E.read (%90) = .value (scratch 28)
  p91 : E.read (%91) = .value (scratch 29)
  p92 : E.read (%92) = .value (scratch 30)
  p93 : E.read (%93) = .value (scratch 31)
  p94 : E.read (%94) = .value (scratch 32)
  zero64 : E.read (%21) = .value 0#64
  zero128 : E.read (%61) = .value 0#128

def scratchBytes (i : Fin 33) : Nat := if 19 ≤ i.val ∧ i.val < 28 then 16 else 8

def cleanupPhaseResult (E : Env program.Γ) (s : GlobalState)
    (scratch : Fin 33 → Pointer) : Env program.Γ × GlobalState :=
  let q0 := (E, s)
  let q1 := cleanupChunks0Result q0.1 q0.2 (scratch 5) (scratch 6) (scratch 7) (scratch 8) (scratch 9) 0#64
  let q2 := cleanupChunks1Result q1.1 q1.2 (scratch 5) (scratch 6) (scratch 7) (scratch 8) (scratch 9) (scratch 28) (scratch 29) (scratch 30) (scratch 31) (scratch 32)
  let q3 := cleanupChunks2Result q2.1 q2.2 (scratch 19) (scratch 20) (scratch 21) (scratch 22) (scratch 23) (scratch 24) (scratch 25) (scratch 26) (scratch 27) 0#128
  let q4 := cleanupChunks3Result q3.1 q3.2 (scratch 0) (scratch 1) (scratch 2) (scratch 3) (scratch 4) 0#64
  let q5 := cleanupChunks4Result q4.1 q4.2 (scratch 0) (scratch 1) (scratch 2) (scratch 3) (scratch 4) (scratch 14) (scratch 15) (scratch 16) (scratch 17) (scratch 18)
  let q6 := cleanupChunks5Result q5.1 q5.2
  q6

/-- Execute every retained cleanup read, store, fence, and lifetime marker.
The concrete intermediate memories are retained even if scratch pointers alias. -/
theorem cleanup_phase (E : Env program.Γ) (s : GlobalState)
    (scratch : Fin 33 → Pointer) (hr : CleanupReady E scratch)
    (hfit : ∀ i, SmallRange s.mem (scratch i) (scratchBytes i)) :
    List.foldlM Instr.run E cleanup s = .value (cleanupPhaseResult E s scratch) := by
  let q0 : Env program.Γ × GlobalState := (E, s)
  let q1 := cleanupChunks0Result q0.1 q0.2 (scratch 5) (scratch 6) (scratch 7) (scratch 8) (scratch 9) 0#64
  have hf0_67 : SmallRange q0.2.mem (scratch 5) 8 := by
    dsimp only [q0]
    repeat' apply SmallRange.storeAt
    exact hfit 5
  have hf0_68 : SmallRange q0.2.mem (scratch 6) 8 := by
    dsimp only [q0]
    repeat' apply SmallRange.storeAt
    exact hfit 6
  have hf0_69 : SmallRange q0.2.mem (scratch 7) 8 := by
    dsimp only [q0]
    repeat' apply SmallRange.storeAt
    exact hfit 7
  have hf0_70 : SmallRange q0.2.mem (scratch 8) 8 := by
    dsimp only [q0]
    repeat' apply SmallRange.storeAt
    exact hfit 8
  have hf0_71 : SmallRange q0.2.mem (scratch 9) 8 := by
    dsimp only [q0]
    repeat' apply SmallRange.storeAt
    exact hfit 9
  have h0 := cleanupChunks0_execute q0.1 q0.2 (scratch 5) (scratch 6) (scratch 7) (scratch 8) (scratch 9) 0#64
    hf0_67
    (by simpa [q0, mlir_env] using hr.p67)
    hf0_68
    (by simpa [q0, mlir_env] using hr.p68)
    hf0_69
    (by simpa [q0, mlir_env] using hr.p69)
    hf0_70
    (by simpa [q0, mlir_env] using hr.p70)
    hf0_71
    (by simpa [q0, mlir_env] using hr.p71)
    (by simpa [q0, mlir_env] using hr.zero64)
  change List.foldlM Instr.run q0.1 cleanupChunks0Block.body q0.2 = .value q1 at h0
  let q2 := cleanupChunks1Result q1.1 q1.2 (scratch 5) (scratch 6) (scratch 7) (scratch 8) (scratch 9) (scratch 28) (scratch 29) (scratch 30) (scratch 31) (scratch 32)
  have hf1_67 : SmallRange q1.2.mem (scratch 5) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 5
  have hf1_68 : SmallRange q1.2.mem (scratch 6) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 6
  have hf1_69 : SmallRange q1.2.mem (scratch 7) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 7
  have hf1_70 : SmallRange q1.2.mem (scratch 8) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 8
  have hf1_71 : SmallRange q1.2.mem (scratch 9) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 9
  have hf1_90 : SmallRange q1.2.mem (scratch 28) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 28
  have hf1_91 : SmallRange q1.2.mem (scratch 29) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 29
  have hf1_92 : SmallRange q1.2.mem (scratch 30) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 30
  have hf1_93 : SmallRange q1.2.mem (scratch 31) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 31
  have hf1_94 : SmallRange q1.2.mem (scratch 32) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result]
    repeat' apply SmallRange.storeAt
    exact hfit 32
  have h1 := cleanupChunks1_execute q1.1 q1.2 (scratch 5) (scratch 6) (scratch 7) (scratch 8) (scratch 9) (scratch 28) (scratch 29) (scratch 30) (scratch 31) (scratch 32)
    hf1_67
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p67)
    hf1_68
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p68)
    hf1_69
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p69)
    hf1_70
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p70)
    hf1_71
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p71)
    hf1_90
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p90)
    hf1_91
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p91)
    hf1_92
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p92)
    hf1_93
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p93)
    hf1_94
    (by simpa [q0, q1, cleanupChunks0Result, mlir_env] using hr.p94)
  change List.foldlM Instr.run q1.1 cleanupChunks1Block.body q1.2 = .value q2 at h1
  let q3 := cleanupChunks2Result q2.1 q2.2 (scratch 19) (scratch 20) (scratch 21) (scratch 22) (scratch 23) (scratch 24) (scratch 25) (scratch 26) (scratch 27) 0#128
  have hf2_81 : SmallRange q2.2.mem (scratch 19) 16 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result]
    repeat' apply SmallRange.storeAt
    exact hfit 19
  have hf2_82 : SmallRange q2.2.mem (scratch 20) 16 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result]
    repeat' apply SmallRange.storeAt
    exact hfit 20
  have hf2_83 : SmallRange q2.2.mem (scratch 21) 16 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result]
    repeat' apply SmallRange.storeAt
    exact hfit 21
  have hf2_84 : SmallRange q2.2.mem (scratch 22) 16 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result]
    repeat' apply SmallRange.storeAt
    exact hfit 22
  have hf2_85 : SmallRange q2.2.mem (scratch 23) 16 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result]
    repeat' apply SmallRange.storeAt
    exact hfit 23
  have hf2_86 : SmallRange q2.2.mem (scratch 24) 16 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result]
    repeat' apply SmallRange.storeAt
    exact hfit 24
  have hf2_87 : SmallRange q2.2.mem (scratch 25) 16 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result]
    repeat' apply SmallRange.storeAt
    exact hfit 25
  have hf2_88 : SmallRange q2.2.mem (scratch 26) 16 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result]
    repeat' apply SmallRange.storeAt
    exact hfit 26
  have hf2_89 : SmallRange q2.2.mem (scratch 27) 16 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result]
    repeat' apply SmallRange.storeAt
    exact hfit 27
  have h2 := cleanupChunks2_execute q2.1 q2.2 (scratch 19) (scratch 20) (scratch 21) (scratch 22) (scratch 23) (scratch 24) (scratch 25) (scratch 26) (scratch 27) 0#128
    hf2_81
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.p81)
    hf2_82
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.p82)
    hf2_83
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.p83)
    hf2_84
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.p84)
    hf2_85
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.p85)
    hf2_86
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.p86)
    hf2_87
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.p87)
    hf2_88
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.p88)
    hf2_89
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.p89)
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, mlir_env] using hr.zero128)
  change List.foldlM Instr.run q2.1 cleanupChunks2Block.body q2.2 = .value q3 at h2
  let q4 := cleanupChunks3Result q3.1 q3.2 (scratch 0) (scratch 1) (scratch 2) (scratch 3) (scratch 4) 0#64
  have hf3_62 : SmallRange q3.2.mem (scratch 0) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result]
    repeat' apply SmallRange.storeAt
    exact hfit 0
  have hf3_63 : SmallRange q3.2.mem (scratch 1) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result]
    repeat' apply SmallRange.storeAt
    exact hfit 1
  have hf3_64 : SmallRange q3.2.mem (scratch 2) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result]
    repeat' apply SmallRange.storeAt
    exact hfit 2
  have hf3_65 : SmallRange q3.2.mem (scratch 3) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result]
    repeat' apply SmallRange.storeAt
    exact hfit 3
  have hf3_66 : SmallRange q3.2.mem (scratch 4) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result]
    repeat' apply SmallRange.storeAt
    exact hfit 4
  have h3 := cleanupChunks3_execute q3.1 q3.2 (scratch 0) (scratch 1) (scratch 2) (scratch 3) (scratch 4) 0#64
    hf3_62
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, mlir_env] using hr.p62)
    hf3_63
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, mlir_env] using hr.p63)
    hf3_64
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, mlir_env] using hr.p64)
    hf3_65
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, mlir_env] using hr.p65)
    hf3_66
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, mlir_env] using hr.p66)
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, mlir_env] using hr.zero64)
  change List.foldlM Instr.run q3.1 cleanupChunks3Block.body q3.2 = .value q4 at h3
  let q5 := cleanupChunks4Result q4.1 q4.2 (scratch 0) (scratch 1) (scratch 2) (scratch 3) (scratch 4) (scratch 14) (scratch 15) (scratch 16) (scratch 17) (scratch 18)
  have hf4_62 : SmallRange q4.2.mem (scratch 0) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 0
  have hf4_63 : SmallRange q4.2.mem (scratch 1) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 1
  have hf4_64 : SmallRange q4.2.mem (scratch 2) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 2
  have hf4_65 : SmallRange q4.2.mem (scratch 3) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 3
  have hf4_66 : SmallRange q4.2.mem (scratch 4) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 4
  have hf4_76 : SmallRange q4.2.mem (scratch 14) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 14
  have hf4_77 : SmallRange q4.2.mem (scratch 15) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 15
  have hf4_78 : SmallRange q4.2.mem (scratch 16) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 16
  have hf4_79 : SmallRange q4.2.mem (scratch 17) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 17
  have hf4_80 : SmallRange q4.2.mem (scratch 18) 8 := by
    dsimp only [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result]
    repeat' apply SmallRange.storeAt
    exact hfit 18
  have h4 := cleanupChunks4_execute q4.1 q4.2 (scratch 0) (scratch 1) (scratch 2) (scratch 3) (scratch 4) (scratch 14) (scratch 15) (scratch 16) (scratch 17) (scratch 18)
    hf4_62
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p62)
    hf4_63
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p63)
    hf4_64
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p64)
    hf4_65
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p65)
    hf4_66
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p66)
    hf4_76
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p76)
    hf4_77
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p77)
    hf4_78
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p78)
    hf4_79
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p79)
    hf4_80
    (by simpa [q0, q1, cleanupChunks0Result, q2, cleanupChunks1Result, q3, cleanupChunks2Result, q4, cleanupChunks3Result, mlir_env] using hr.p80)
  change List.foldlM Instr.run q4.1 cleanupChunks4Block.body q4.2 = .value q5 at h4
  let q6 := cleanupChunks5Result q5.1 q5.2
  have h5 := cleanupChunks5_execute q5.1 q5.2
  change List.foldlM Instr.run q5.1 cleanupChunks5Block.body q5.2 = .value q6 at h5
  have hf : List.foldlM Instr.run q0.1 cleanup q0.2 = .value q6 := by
    rw [cleanup_body_decomposition]
    simp only [List.foldlM_append, EffectM.bind_eq, h0, h1, h2, h3, h4, h5,
      PoisonOr.value_bind]
  exact hf

end Agave.Ed25519.ScalarReduce32.Execution
