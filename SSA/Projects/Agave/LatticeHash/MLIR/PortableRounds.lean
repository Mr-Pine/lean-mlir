/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionSupport

/-! Structural wiring for the portable compiler proof. The G results are
opaque parameters with equations supplied by instruction-level proofs. No
scalarG arithmetic is unfolded when assembling the seven-round state. -/
namespace AgaveLatticeHash.MLIR
open Blake3Compression

/-- State order after the four diagonal G operations of one round. -/
def portableRoundState {α : Type} (q4 q5 q6 q7 : Quad α) : State α :=
  fun i => match i.val with
    | 0 => q4.a | 1 => q5.a | 2 => q6.a | 3 => q7.a
    | 4 => q7.b | 5 => q4.b | 6 => q5.b | 7 => q6.b
    | 8 => q6.c | 9 => q7.c | 10 => q4.c | 11 => q5.c
    | 12 => q5.d | 13 => q6.d | 14 => q7.d | _ => q4.d

/-- Assemble a round while keeping all eight G applications opaque. -/
theorem namedRound_eq {α : Type} (g : GFn α) (s m : State α) (r : Fin 7)
    (q0 q1 q2 q3 q4 q5 q6 q7 : Quad α)
    (h0 : q0 = g (s 0) (s 4) (s 8) (s 12) (m (schedule r 0)) (m (schedule r 1)))
    (h1 : q1 = g (s 1) (s 5) (s 9) (s 13) (m (schedule r 2)) (m (schedule r 3)))
    (h2 : q2 = g (s 2) (s 6) (s 10) (s 14) (m (schedule r 4)) (m (schedule r 5)))
    (h3 : q3 = g (s 3) (s 7) (s 11) (s 15) (m (schedule r 6)) (m (schedule r 7)))
    (h4 : q4 = g q0.a q1.b q2.c q3.d (m (schedule r 8)) (m (schedule r 9)))
    (h5 : q5 = g q1.a q2.b q3.c q0.d (m (schedule r 10)) (m (schedule r 11)))
    (h6 : q6 = g q2.a q3.b q0.c q1.d (m (schedule r 12)) (m (schedule r 13)))
    (h7 : q7 = g q3.a q0.b q1.c q2.d (m (schedule r 14)) (m (schedule r 15))) :
    portableRoundState q4 q5 q6 q7 = roundFn g s m r := by
  rw [← roundRegisters_eq]
  simp only [roundRegisters, ← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7]
  rfl

/-- Seven named intermediate states compose without expanding their G DAGs. -/
theorem sevenNamedRounds_eq {α : Type} (g : GFn α) (m : State α)
    (s0 s1 s2 s3 s4 s5 s6 s7 : State α)
    (h0 : s1 = roundFn g s0 m 0) (h1 : s2 = roundFn g s1 m 1)
    (h2 : s3 = roundFn g s2 m 2) (h3 : s4 = roundFn g s3 m 3)
    (h4 : s5 = roundFn g s4 m 4) (h5 : s6 = roundFn g s5 m 5)
    (h6 : s7 = roundFn g s6 m 6) :
    s7 = sevenRounds g s0 m := by
  simp only [sevenRounds, sevenRoundSchedule, rounds]
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The 56 instruction-level scalar G equalities used by the actual portable
wrapper imply the independent compression specification. Hypotheses contain
only one G each; the conclusion is obtained by seven structural round steps. -/
theorem portableRounds_eq (cv : CV Word) (m : State Word) (counter : Counter)
    (len flags : BitVec 8)
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 : Quad Word)
    (hq0 : q0 = scalarG (cv 0) (cv 4) (1779033703 : Word) (counter.extractLsb' 0 32) (m 0) (m 1))
    (hq1 : q1 = scalarG (cv 1) (cv 5) (3144134277 : Word) (counter.extractLsb' 32 32) (m 2) (m 3))
    (hq2 : q2 = scalarG (cv 2) (cv 6) (1013904242 : Word) (len.zeroExtend 32) (m 4) (m 5))
    (hq3 : q3 = scalarG (cv 3) (cv 7) (2773480762 : Word) (flags.zeroExtend 32) (m 6) (m 7))
    (hq4 : q4 = scalarG q0.a q1.b q2.c q3.d (m 8) (m 9))
    (hq5 : q5 = scalarG q1.a q2.b q3.c q0.d (m 10) (m 11))
    (hq6 : q6 = scalarG q2.a q3.b q0.c q1.d (m 12) (m 13))
    (hq7 : q7 = scalarG q3.a q0.b q1.c q2.d (m 14) (m 15))
    (hq8 : q8 = scalarG q4.a q7.b q6.c q5.d (m 2) (m 6))
    (hq9 : q9 = scalarG q5.a q4.b q7.c q6.d (m 3) (m 10))
    (hq10 : q10 = scalarG q6.a q5.b q4.c q7.d (m 7) (m 0))
    (hq11 : q11 = scalarG q7.a q6.b q5.c q4.d (m 4) (m 13))
    (hq12 : q12 = scalarG q8.a q9.b q10.c q11.d (m 1) (m 11))
    (hq13 : q13 = scalarG q9.a q10.b q11.c q8.d (m 12) (m 5))
    (hq14 : q14 = scalarG q10.a q11.b q8.c q9.d (m 9) (m 14))
    (hq15 : q15 = scalarG q11.a q8.b q9.c q10.d (m 15) (m 8))
    (hq16 : q16 = scalarG q12.a q15.b q14.c q13.d (m 3) (m 4))
    (hq17 : q17 = scalarG q13.a q12.b q15.c q14.d (m 10) (m 12))
    (hq18 : q18 = scalarG q14.a q13.b q12.c q15.d (m 13) (m 2))
    (hq19 : q19 = scalarG q15.a q14.b q13.c q12.d (m 7) (m 14))
    (hq20 : q20 = scalarG q16.a q17.b q18.c q19.d (m 6) (m 5))
    (hq21 : q21 = scalarG q17.a q18.b q19.c q16.d (m 9) (m 0))
    (hq22 : q22 = scalarG q18.a q19.b q16.c q17.d (m 11) (m 15))
    (hq23 : q23 = scalarG q19.a q16.b q17.c q18.d (m 8) (m 1))
    (hq24 : q24 = scalarG q20.a q23.b q22.c q21.d (m 10) (m 7))
    (hq25 : q25 = scalarG q21.a q20.b q23.c q22.d (m 12) (m 9))
    (hq26 : q26 = scalarG q22.a q21.b q20.c q23.d (m 14) (m 3))
    (hq27 : q27 = scalarG q23.a q22.b q21.c q20.d (m 13) (m 15))
    (hq28 : q28 = scalarG q24.a q25.b q26.c q27.d (m 4) (m 0))
    (hq29 : q29 = scalarG q25.a q26.b q27.c q24.d (m 11) (m 2))
    (hq30 : q30 = scalarG q26.a q27.b q24.c q25.d (m 5) (m 8))
    (hq31 : q31 = scalarG q27.a q24.b q25.c q26.d (m 1) (m 6))
    (hq32 : q32 = scalarG q28.a q31.b q30.c q29.d (m 12) (m 13))
    (hq33 : q33 = scalarG q29.a q28.b q31.c q30.d (m 9) (m 11))
    (hq34 : q34 = scalarG q30.a q29.b q28.c q31.d (m 15) (m 10))
    (hq35 : q35 = scalarG q31.a q30.b q29.c q28.d (m 14) (m 8))
    (hq36 : q36 = scalarG q32.a q33.b q34.c q35.d (m 7) (m 2))
    (hq37 : q37 = scalarG q33.a q34.b q35.c q32.d (m 5) (m 3))
    (hq38 : q38 = scalarG q34.a q35.b q32.c q33.d (m 0) (m 1))
    (hq39 : q39 = scalarG q35.a q32.b q33.c q34.d (m 6) (m 4))
    (hq40 : q40 = scalarG q36.a q39.b q38.c q37.d (m 9) (m 14))
    (hq41 : q41 = scalarG q37.a q36.b q39.c q38.d (m 11) (m 5))
    (hq42 : q42 = scalarG q38.a q37.b q36.c q39.d (m 8) (m 12))
    (hq43 : q43 = scalarG q39.a q38.b q37.c q36.d (m 15) (m 1))
    (hq44 : q44 = scalarG q40.a q41.b q42.c q43.d (m 13) (m 3))
    (hq45 : q45 = scalarG q41.a q42.b q43.c q40.d (m 0) (m 10))
    (hq46 : q46 = scalarG q42.a q43.b q40.c q41.d (m 2) (m 6))
    (hq47 : q47 = scalarG q43.a q40.b q41.c q42.d (m 4) (m 7))
    (hq48 : q48 = scalarG q44.a q47.b q46.c q45.d (m 11) (m 15))
    (hq49 : q49 = scalarG q45.a q44.b q47.c q46.d (m 5) (m 0))
    (hq50 : q50 = scalarG q46.a q45.b q44.c q47.d (m 1) (m 9))
    (hq51 : q51 = scalarG q47.a q46.b q45.c q44.d (m 8) (m 6))
    (hq52 : q52 = scalarG q48.a q49.b q50.c q51.d (m 14) (m 10))
    (hq53 : q53 = scalarG q49.a q50.b q51.c q48.d (m 2) (m 12))
    (hq54 : q54 = scalarG q50.a q51.b q48.c q49.d (m 3) (m 4))
    (hq55 : q55 = scalarG q51.a q48.b q49.c q50.d (m 7) (m 13))
    : portableRoundState q52 q53 q54 q55 =
      scalarCompressPre cv m counter (len.zeroExtend 32) (flags.zeroExtend 32) := by
  let s0 := scalarInit cv counter (len.zeroExtend 32) (flags.zeroExtend 32)
  let s1 := portableRoundState q4 q5 q6 q7
  let s2 := portableRoundState q12 q13 q14 q15
  let s3 := portableRoundState q20 q21 q22 q23
  let s4 := portableRoundState q28 q29 q30 q31
  let s5 := portableRoundState q36 q37 q38 q39
  let s6 := portableRoundState q44 q45 q46 q47
  let s7 := portableRoundState q52 q53 q54 q55
  have h0 : s1 = roundFn scalarG s0 m 0 :=
    namedRound_eq scalarG s0 m 0 q0 q1 q2 q3 q4 q5 q6 q7 hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7
  have h1 : s2 = roundFn scalarG s1 m 1 :=
    namedRound_eq scalarG s1 m 1 q8 q9 q10 q11 q12 q13 q14 q15 hq8 hq9 hq10 hq11 hq12 hq13 hq14 hq15
  have h2 : s3 = roundFn scalarG s2 m 2 :=
    namedRound_eq scalarG s2 m 2 q16 q17 q18 q19 q20 q21 q22 q23 hq16 hq17 hq18 hq19 hq20 hq21 hq22 hq23
  have h3 : s4 = roundFn scalarG s3 m 3 :=
    namedRound_eq scalarG s3 m 3 q24 q25 q26 q27 q28 q29 q30 q31 hq24 hq25 hq26 hq27 hq28 hq29 hq30 hq31
  have h4 : s5 = roundFn scalarG s4 m 4 :=
    namedRound_eq scalarG s4 m 4 q32 q33 q34 q35 q36 q37 q38 q39 hq32 hq33 hq34 hq35 hq36 hq37 hq38 hq39
  have h5 : s6 = roundFn scalarG s5 m 5 :=
    namedRound_eq scalarG s5 m 5 q40 q41 q42 q43 q44 q45 q46 q47 hq40 hq41 hq42 hq43 hq44 hq45 hq46 hq47
  have h6 : s7 = roundFn scalarG s6 m 6 :=
    namedRound_eq scalarG s6 m 6 q48 q49 q50 q51 q52 q53 q54 q55 hq48 hq49 hq50 hq51 hq52 hq53 hq54 hq55
  exact sevenNamedRounds_eq scalarG m s0 s1 s2 s3 s4 s5 s6 s7 h0 h1 h2 h3 h4 h5 h6

end AgaveLatticeHash.MLIR
