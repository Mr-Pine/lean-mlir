import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Data

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def copyEnv0 (E : Env program.Γ) (u left : Pointer) : Env program.Γ :=
  E[%237 := .value (u.add 8#64),
    %238 := .value (left.add 1#64),
    %239 := .value (left.add 2#64),
    %240 := .value (left.add 3#64),
    %241 := .value (left.add 4#64),
    %242 := .value (left.add 5#64),
    %243 := .value (left.add 6#64),
    %244 := .value (left.add 7#64)]

def copyState0 (s : GlobalState) (left : Pointer) (b : Fin 32 → BitVec 8) : GlobalState :=
  {s with mem := ((((((((s.mem).storeAt (left.add 0#64) (b 0)).storeAt (left.add 1#64) (b 1)).storeAt (left.add 2#64) (b 2)).storeAt (left.add 3#64) (b 3)).storeAt (left.add 4#64) (b 4)).storeAt (left.add 5#64) (b 5)).storeAt (left.add 6#64) (b 6)).storeAt (left.add 7#64) (b 7)}

theorem copy_frame0 (E : Env program.Γ) (u left : Pointer) :
    Frame E (copyEnv0 E u left) := by
  unfold copyEnv0
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem copy_segment0 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (u left : Pointer) (b : Fin 32 → BitVec 8)
    (hu : SmallRange s.mem u 40) (hl : SmallRange s.mem left 32)
    (hc : Constants E) (hb : Cached E b)
    (eu : E.read (%arg1) = .value u) (el : E.read (%65) = .value left) :
    Cutpoint.segment (program p g) 0 308 19 E s =
      .value (copyEnv0 E u left, copyState0 s left b) := by
  simp only [Env.read_arg] at eu
  have e133 : E.read (%133) = .value (b 0) := hb 0
  have e136 : E.read (%136) = .value (b 1) := hb 1
  have e139 : E.read (%139) = .value (b 2) := hb 2
  have e142 : E.read (%142) = .value (b 3) := hb 3
  have e145 : E.read (%145) = .value (b 4) := hb 4
  have e148 : E.read (%148) = .value (b 5) := hb 5
  have e154 : E.read (%154) = .value (b 6) := hb 6
  have e157 : E.read (%157) = .value (b 7) := hb 7
  have c3 := hc.c3
  have c10 := hc.c10
  have c11 := hc.c11
  have c12 := hc.c12
  have c13 := hc.c13
  have c14 := hc.c14
  have c16 := hc.c16
  have c17 := hc.c17
  have gu := hu.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at gu
  have g1 := ((hl).storeAt (left.add 0#64) (b 0)).gep (k := 1) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g1
  have g2 := (((hl).storeAt (left.add 0#64) (b 0)).storeAt (left.add 1#64) (b 1)).gep (k := 2) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g2
  have g3 := ((((hl).storeAt (left.add 0#64) (b 0)).storeAt (left.add 1#64) (b 1)).storeAt (left.add 2#64) (b 2)).gep (k := 3) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g3
  have g4 := (((((hl).storeAt (left.add 0#64) (b 0)).storeAt (left.add 1#64) (b 1)).storeAt (left.add 2#64) (b 2)).storeAt (left.add 3#64) (b 3)).gep (k := 4) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g4
  have g5 := ((((((hl).storeAt (left.add 0#64) (b 0)).storeAt (left.add 1#64) (b 1)).storeAt (left.add 2#64) (b 2)).storeAt (left.add 3#64) (b 3)).storeAt (left.add 4#64) (b 4)).gep (k := 5) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g5
  have g6 := (((((((hl).storeAt (left.add 0#64) (b 0)).storeAt (left.add 1#64) (b 1)).storeAt (left.add 2#64) (b 2)).storeAt (left.add 3#64) (b 3)).storeAt (left.add 4#64) (b 4)).storeAt (left.add 5#64) (b 5)).gep (k := 6) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g6
  have g7 := ((((((((hl).storeAt (left.add 0#64) (b 0)).storeAt (left.add 1#64) (b 1)).storeAt (left.add 2#64) (b 2)).storeAt (left.add 3#64) (b 3)).storeAt (left.add 4#64) (b 4)).storeAt (left.add 5#64) (b 5)).storeAt (left.add 6#64) (b 6)).gep (k := 7) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g7
  have f0 := hl.fits_add (k := 0) (count := 1) (by decide)
  have f1 := hl.fits_add (k := 1) (count := 1) (by decide)
  have f2 := hl.fits_add (k := 2) (count := 1) (by decide)
  have f3 := hl.fits_add (k := 3) (count := 1) (by decide)
  have f4 := hl.fits_add (k := 4) (count := 1) (by decide)
  have f5 := hl.fits_add (k := 5) (count := 1) (by decide)
  have f6 := hl.fits_add (k := 6) (count := 1) (by decide)
  have f7 := hl.fits_add (k := 7) (count := 1) (by decide)
  simp only [Pointer.add_zero] at f0
  change List.foldlM Instr.run E (((program.entry p g).body.drop 308).take 19) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (maxSteps := 200000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
     Operation.gepInboundsIndex, GepIndex.inboundsOffset, Operation.GepSignedRange,
     EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
     copyEnv0, copyState0, Pointer.add_zero, throwUBIf,
     eu, el, gu, c3, c10, c11, c12, c13, c14, c16, c17, e133, e136, e139, e142, e145, e148, e154, e157, g1, g2, g3, g4, g5, g6, g7, f0, f1, f2, f3, f4, f5, f6, f7]

def copyEnv1 (E : Env program.Γ) (u left : Pointer) : Env program.Γ :=
  E[%245 := .value (left.add 8#64),
    %246 := .value (left.add 9#64),
    %247 := .value (left.add 10#64),
    %248 := .value (left.add 11#64),
    %249 := .value (left.add 12#64),
    %250 := .value (left.add 13#64),
    %251 := .value (left.add 14#64),
    %252 := .value (left.add 15#64)]

def copyState1 (s : GlobalState) (left : Pointer) (b : Fin 32 → BitVec 8) : GlobalState :=
  {s with mem := ((((((((s.mem).storeAt (left.add 8#64) (b 8)).storeAt (left.add 9#64) (b 9)).storeAt (left.add 10#64) (b 10)).storeAt (left.add 11#64) (b 11)).storeAt (left.add 12#64) (b 12)).storeAt (left.add 13#64) (b 13)).storeAt (left.add 14#64) (b 14)).storeAt (left.add 15#64) (b 15)}

theorem copy_frame1 (E : Env program.Γ) (u left : Pointer) :
    Frame E (copyEnv1 E u left) := by
  unfold copyEnv1
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem copy_segment1 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (u left : Pointer) (b : Fin 32 → BitVec 8)
    (hu : SmallRange s.mem u 40) (hl : SmallRange s.mem left 32)
    (hc : Constants E) (hb : Cached E b)
    (eu : E.read (%arg1) = .value u) (el : E.read (%65) = .value left) :
    Cutpoint.segment (program p g) 0 327 16 E s =
      .value (copyEnv1 E u left, copyState1 s left b) := by
  have e160 : E.read (%160) = .value (b 8) := hb 8
  have e163 : E.read (%163) = .value (b 9) := hb 9
  have e166 : E.read (%166) = .value (b 10) := hb 10
  have e169 : E.read (%169) = .value (b 11) := hb 11
  have e174 : E.read (%174) = .value (b 12) := hb 12
  have e177 : E.read (%177) = .value (b 13) := hb 13
  have e180 : E.read (%180) = .value (b 14) := hb 14
  have e183 : E.read (%183) = .value (b 15) := hb 15
  have c3 := hc.c3
  have c18 := hc.c18
  have c20 := hc.c20
  have c22 := hc.c22
  have c24 := hc.c24
  have c26 := hc.c26
  have c27 := hc.c27
  have c29 := hc.c29
  have g8 := (hl).gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g8
  have g9 := ((hl).storeAt (left.add 8#64) (b 8)).gep (k := 9) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g9
  have g10 := (((hl).storeAt (left.add 8#64) (b 8)).storeAt (left.add 9#64) (b 9)).gep (k := 10) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g10
  have g11 := ((((hl).storeAt (left.add 8#64) (b 8)).storeAt (left.add 9#64) (b 9)).storeAt (left.add 10#64) (b 10)).gep (k := 11) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g11
  have g12 := (((((hl).storeAt (left.add 8#64) (b 8)).storeAt (left.add 9#64) (b 9)).storeAt (left.add 10#64) (b 10)).storeAt (left.add 11#64) (b 11)).gep (k := 12) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g12
  have g13 := ((((((hl).storeAt (left.add 8#64) (b 8)).storeAt (left.add 9#64) (b 9)).storeAt (left.add 10#64) (b 10)).storeAt (left.add 11#64) (b 11)).storeAt (left.add 12#64) (b 12)).gep (k := 13) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g13
  have g14 := (((((((hl).storeAt (left.add 8#64) (b 8)).storeAt (left.add 9#64) (b 9)).storeAt (left.add 10#64) (b 10)).storeAt (left.add 11#64) (b 11)).storeAt (left.add 12#64) (b 12)).storeAt (left.add 13#64) (b 13)).gep (k := 14) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g14
  have g15 := ((((((((hl).storeAt (left.add 8#64) (b 8)).storeAt (left.add 9#64) (b 9)).storeAt (left.add 10#64) (b 10)).storeAt (left.add 11#64) (b 11)).storeAt (left.add 12#64) (b 12)).storeAt (left.add 13#64) (b 13)).storeAt (left.add 14#64) (b 14)).gep (k := 15) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g15
  have f8 := hl.fits_add (k := 8) (count := 1) (by decide)
  have f9 := hl.fits_add (k := 9) (count := 1) (by decide)
  have f10 := hl.fits_add (k := 10) (count := 1) (by decide)
  have f11 := hl.fits_add (k := 11) (count := 1) (by decide)
  have f12 := hl.fits_add (k := 12) (count := 1) (by decide)
  have f13 := hl.fits_add (k := 13) (count := 1) (by decide)
  have f14 := hl.fits_add (k := 14) (count := 1) (by decide)
  have f15 := hl.fits_add (k := 15) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 327).take 16) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (maxSteps := 200000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
     Operation.gepInboundsIndex, GepIndex.inboundsOffset, Operation.GepSignedRange,
     EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
     copyEnv1, copyState1, Pointer.add_zero, throwUBIf,
     eu, el, c3, c18, c20, c22, c24, c26, c27, c29, e160, e163, e166, e169, e174, e177, e180, e183, g8, g9, g10, g11, g12, g13, g14, g15, f8, f9, f10, f11, f12, f13, f14, f15]

def copyEnv2 (E : Env program.Γ) (u left : Pointer) : Env program.Γ :=
  E[%253 := .value (left.add 16#64),
    %254 := .value (left.add 17#64),
    %255 := .value (left.add 18#64),
    %256 := .value (left.add 19#64),
    %257 := .value (left.add 20#64),
    %258 := .value (left.add 21#64),
    %259 := .value (left.add 22#64),
    %260 := .value (left.add 23#64)]

def copyState2 (s : GlobalState) (left : Pointer) (b : Fin 32 → BitVec 8) : GlobalState :=
  {s with mem := ((((((((s.mem).storeAt (left.add 16#64) (b 16)).storeAt (left.add 17#64) (b 17)).storeAt (left.add 18#64) (b 18)).storeAt (left.add 19#64) (b 19)).storeAt (left.add 20#64) (b 20)).storeAt (left.add 21#64) (b 21)).storeAt (left.add 22#64) (b 22)).storeAt (left.add 23#64) (b 23)}

theorem copy_frame2 (E : Env program.Γ) (u left : Pointer) :
    Frame E (copyEnv2 E u left) := by
  unfold copyEnv2
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem copy_segment2 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (u left : Pointer) (b : Fin 32 → BitVec 8)
    (hu : SmallRange s.mem u 40) (hl : SmallRange s.mem left 32)
    (hc : Constants E) (hb : Cached E b)
    (eu : E.read (%arg1) = .value u) (el : E.read (%65) = .value left) :
    Cutpoint.segment (program p g) 0 343 16 E s =
      .value (copyEnv2 E u left, copyState2 s left b) := by
  have e186 : E.read (%186) = .value (b 16) := hb 16
  have e189 : E.read (%189) = .value (b 17) := hb 17
  have e192 : E.read (%192) = .value (b 18) := hb 18
  have e197 : E.read (%197) = .value (b 19) := hb 19
  have e200 : E.read (%200) = .value (b 20) := hb 20
  have e203 : E.read (%203) = .value (b 21) := hb 21
  have e206 : E.read (%206) = .value (b 22) := hb 22
  have e209 : E.read (%209) = .value (b 23) := hb 23
  have c4 := hc.c4
  have c9 := hc.c9
  have c19 := hc.c19
  have c28 := hc.c28
  have c32 := hc.c32
  have c35 := hc.c35
  have c36 := hc.c36
  have c37 := hc.c37
  have g16 := (hl).gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g16
  have g17 := ((hl).storeAt (left.add 16#64) (b 16)).gep (k := 17) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g17
  have g18 := (((hl).storeAt (left.add 16#64) (b 16)).storeAt (left.add 17#64) (b 17)).gep (k := 18) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g18
  have g19 := ((((hl).storeAt (left.add 16#64) (b 16)).storeAt (left.add 17#64) (b 17)).storeAt (left.add 18#64) (b 18)).gep (k := 19) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g19
  have g20 := (((((hl).storeAt (left.add 16#64) (b 16)).storeAt (left.add 17#64) (b 17)).storeAt (left.add 18#64) (b 18)).storeAt (left.add 19#64) (b 19)).gep (k := 20) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g20
  have g21 := ((((((hl).storeAt (left.add 16#64) (b 16)).storeAt (left.add 17#64) (b 17)).storeAt (left.add 18#64) (b 18)).storeAt (left.add 19#64) (b 19)).storeAt (left.add 20#64) (b 20)).gep (k := 21) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g21
  have g22 := (((((((hl).storeAt (left.add 16#64) (b 16)).storeAt (left.add 17#64) (b 17)).storeAt (left.add 18#64) (b 18)).storeAt (left.add 19#64) (b 19)).storeAt (left.add 20#64) (b 20)).storeAt (left.add 21#64) (b 21)).gep (k := 22) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g22
  have g23 := ((((((((hl).storeAt (left.add 16#64) (b 16)).storeAt (left.add 17#64) (b 17)).storeAt (left.add 18#64) (b 18)).storeAt (left.add 19#64) (b 19)).storeAt (left.add 20#64) (b 20)).storeAt (left.add 21#64) (b 21)).storeAt (left.add 22#64) (b 22)).gep (k := 23) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g23
  have f16 := hl.fits_add (k := 16) (count := 1) (by decide)
  have f17 := hl.fits_add (k := 17) (count := 1) (by decide)
  have f18 := hl.fits_add (k := 18) (count := 1) (by decide)
  have f19 := hl.fits_add (k := 19) (count := 1) (by decide)
  have f20 := hl.fits_add (k := 20) (count := 1) (by decide)
  have f21 := hl.fits_add (k := 21) (count := 1) (by decide)
  have f22 := hl.fits_add (k := 22) (count := 1) (by decide)
  have f23 := hl.fits_add (k := 23) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 343).take 16) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (maxSteps := 200000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
     Operation.gepInboundsIndex, GepIndex.inboundsOffset, Operation.GepSignedRange,
     EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
     copyEnv2, copyState2, Pointer.add_zero, throwUBIf,
     eu, el, c4, c9, c19, c28, c32, c35, c36, c37, e186, e189, e192, e197, e200, e203, e206, e209, g16, g17, g18, g19, g20, g21, g22, g23, f16, f17, f18, f19, f20, f21, f22, f23]

def copyEnv3 (E : Env program.Γ) (u left : Pointer) : Env program.Γ :=
  E[%261 := .value (left.add 24#64),
    %262 := .value (left.add 25#64),
    %263 := .value (left.add 26#64),
    %264 := .value (left.add 27#64),
    %265 := .value (left.add 28#64),
    %266 := .value (left.add 29#64),
    %267 := .value (left.add 30#64),
    %268 := .value (left.add 31#64)]

def copyState3 (s : GlobalState) (left : Pointer) (b : Fin 32 → BitVec 8) : GlobalState :=
  {s with mem := ((((((((s.mem).storeAt (left.add 24#64) (b 24)).storeAt (left.add 25#64) (b 25)).storeAt (left.add 26#64) (b 26)).storeAt (left.add 27#64) (b 27)).storeAt (left.add 28#64) (b 28)).storeAt (left.add 29#64) (b 29)).storeAt (left.add 30#64) (b 30)).storeAt (left.add 31#64) (b 31)}

theorem copy_frame3 (E : Env program.Γ) (u left : Pointer) :
    Frame E (copyEnv3 E u left) := by
  unfold copyEnv3
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem copy_segment3 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (u left : Pointer) (b : Fin 32 → BitVec 8)
    (hu : SmallRange s.mem u 40) (hl : SmallRange s.mem left 32)
    (hc : Constants E) (hb : Cached E b)
    (eu : E.read (%arg1) = .value u) (el : E.read (%65) = .value left) :
    Cutpoint.segment (program p g) 0 359 16 E s =
      .value (copyEnv3 E u left, copyState3 s left b) := by
  have e212 : E.read (%212) = .value (b 24) := hb 24
  have e217 : E.read (%217) = .value (b 25) := hb 25
  have e220 : E.read (%220) = .value (b 26) := hb 26
  have e223 : E.read (%223) = .value (b 27) := hb 27
  have e226 : E.read (%226) = .value (b 28) := hb 28
  have e229 : E.read (%229) = .value (b 29) := hb 29
  have e232 : E.read (%232) = .value (b 30) := hb 30
  have e235 : E.read (%235) = .value (b 31) := hb 31
  have c5 := hc.c5
  have c21 := hc.c21
  have c30 := hc.c30
  have c38 := hc.c38
  have c41 := hc.c41
  have c42 := hc.c42
  have c43 := hc.c43
  have c45 := hc.c45
  have g24 := (hl).gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g24
  have g25 := ((hl).storeAt (left.add 24#64) (b 24)).gep (k := 25) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g25
  have g26 := (((hl).storeAt (left.add 24#64) (b 24)).storeAt (left.add 25#64) (b 25)).gep (k := 26) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g26
  have g27 := ((((hl).storeAt (left.add 24#64) (b 24)).storeAt (left.add 25#64) (b 25)).storeAt (left.add 26#64) (b 26)).gep (k := 27) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g27
  have g28 := (((((hl).storeAt (left.add 24#64) (b 24)).storeAt (left.add 25#64) (b 25)).storeAt (left.add 26#64) (b 26)).storeAt (left.add 27#64) (b 27)).gep (k := 28) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g28
  have g29 := ((((((hl).storeAt (left.add 24#64) (b 24)).storeAt (left.add 25#64) (b 25)).storeAt (left.add 26#64) (b 26)).storeAt (left.add 27#64) (b 27)).storeAt (left.add 28#64) (b 28)).gep (k := 29) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g29
  have g30 := (((((((hl).storeAt (left.add 24#64) (b 24)).storeAt (left.add 25#64) (b 25)).storeAt (left.add 26#64) (b 26)).storeAt (left.add 27#64) (b 27)).storeAt (left.add 28#64) (b 28)).storeAt (left.add 29#64) (b 29)).gep (k := 30) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g30
  have g31 := ((((((((hl).storeAt (left.add 24#64) (b 24)).storeAt (left.add 25#64) (b 25)).storeAt (left.add 26#64) (b 26)).storeAt (left.add 27#64) (b 27)).storeAt (left.add 28#64) (b 28)).storeAt (left.add 29#64) (b 29)).storeAt (left.add 30#64) (b 30)).gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat, Pointer.add_zero] at g31
  have f24 := hl.fits_add (k := 24) (count := 1) (by decide)
  have f25 := hl.fits_add (k := 25) (count := 1) (by decide)
  have f26 := hl.fits_add (k := 26) (count := 1) (by decide)
  have f27 := hl.fits_add (k := 27) (count := 1) (by decide)
  have f28 := hl.fits_add (k := 28) (count := 1) (by decide)
  have f29 := hl.fits_add (k := 29) (count := 1) (by decide)
  have f30 := hl.fits_add (k := 30) (count := 1) (by decide)
  have f31 := hl.fits_add (k := 31) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 359).take 16) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (maxSteps := 200000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
     Operation.gepInboundsIndex, GepIndex.inboundsOffset, Operation.GepSignedRange,
     EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
     copyEnv3, copyState3, Pointer.add_zero, throwUBIf,
     eu, el, c5, c21, c30, c38, c41, c42, c43, c45, e212, e217, e220, e223, e226, e229, e232, e235, g24, g25, g26, g27, g28, g29, g30, g31, f24, f25, f26, f27, f28, f29, f30, f31]

def setupEnv (E : Env program.Γ) (right neg : Pointer) : Env program.Γ :=
  E[%269 := .value (right.add 1#64),
    %270 := .value (right.add 2#64),
    %271 := .value (right.add 3#64),
    %272 := .value (right.add 4#64),
    %273 := .value (right.add 5#64),
    %274 := .value (right.add 6#64),
    %275 := .value (right.add 7#64),
    %276 := .value (right.add 8#64),
    %277 := .value (right.add 9#64),
    %278 := .value (right.add 10#64),
    %279 := .value (right.add 11#64),
    %280 := .value (right.add 12#64),
    %281 := .value (right.add 13#64),
    %282 := .value (right.add 14#64),
    %283 := .value (right.add 15#64),
    %284 := .value (right.add 16#64),
    %285 := .value (right.add 17#64),
    %286 := .value (right.add 18#64),
    %287 := .value (right.add 19#64),
    %288 := .value (right.add 20#64),
    %289 := .value (right.add 21#64),
    %290 := .value (right.add 22#64),
    %291 := .value (right.add 23#64),
    %292 := .value (right.add 24#64),
    %293 := .value (right.add 25#64),
    %294 := .value (right.add 26#64),
    %295 := .value (right.add 27#64),
    %296 := .value (right.add 28#64),
    %297 := .value (right.add 29#64),
    %298 := .value (right.add 30#64),
    %299 := .value (right.add 31#64),
    %300 := .value (neg.add 8#64)]

theorem setup_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right neg : Pointer)
    (hr : SmallRange s.mem right 32) (hn : SmallRange s.mem neg 40)
    (hc : Constants E) (er : E.read (%64) = .value right)
    (en : E.read (%72) = .value neg) :
    Cutpoint.segment (program p g) 0 375 33 E s =
      .value (setupEnv E right neg, s) := by
  have c1 := hc.c1
  have c3 := hc.c3
  have c4 := hc.c4
  have c5 := hc.c5
  have c6 := hc.c6
  have c7 := hc.c7
  have c8 := hc.c8
  have c9 := hc.c9
  have c10 := hc.c10
  have c11 := hc.c11
  have c12 := hc.c12
  have c13 := hc.c13
  have c14 := hc.c14
  have c15 := hc.c15
  have c16 := hc.c16
  have c17 := hc.c17
  have c18 := hc.c18
  have c19 := hc.c19
  have c20 := hc.c20
  have c21 := hc.c21
  have c22 := hc.c22
  have c23 := hc.c23
  have c24 := hc.c24
  have c25 := hc.c25
  have c26 := hc.c26
  have c27 := hc.c27
  have c28 := hc.c28
  have c29 := hc.c29
  have c30 := hc.c30
  have c31 := hc.c31
  have c32 := hc.c32
  have c33 := hc.c33
  have c34 := hc.c34
  have c35 := hc.c35
  have c36 := hc.c36
  have c37 := hc.c37
  have c38 := hc.c38
  have c39 := hc.c39
  have c40 := hc.c40
  have c41 := hc.c41
  have c42 := hc.c42
  have c43 := hc.c43
  have c44 := hc.c44
  have c45 := hc.c45
  have c46 := hc.c46
  have c50 := hc.c50
  have c54 := hc.c54
  have c59 := hc.c59
  have gn := hn.gep (k := 8) (by decide)
  have g1 := hr.gep (k := 1) (by decide)
  have g2 := hr.gep (k := 2) (by decide)
  have g3 := hr.gep (k := 3) (by decide)
  have g4 := hr.gep (k := 4) (by decide)
  have g5 := hr.gep (k := 5) (by decide)
  have g6 := hr.gep (k := 6) (by decide)
  have g7 := hr.gep (k := 7) (by decide)
  have g8 := hr.gep (k := 8) (by decide)
  have g9 := hr.gep (k := 9) (by decide)
  have g10 := hr.gep (k := 10) (by decide)
  have g11 := hr.gep (k := 11) (by decide)
  have g12 := hr.gep (k := 12) (by decide)
  have g13 := hr.gep (k := 13) (by decide)
  have g14 := hr.gep (k := 14) (by decide)
  have g15 := hr.gep (k := 15) (by decide)
  have g16 := hr.gep (k := 16) (by decide)
  have g17 := hr.gep (k := 17) (by decide)
  have g18 := hr.gep (k := 18) (by decide)
  have g19 := hr.gep (k := 19) (by decide)
  have g20 := hr.gep (k := 20) (by decide)
  have g21 := hr.gep (k := 21) (by decide)
  have g22 := hr.gep (k := 22) (by decide)
  have g23 := hr.gep (k := 23) (by decide)
  have g24 := hr.gep (k := 24) (by decide)
  have g25 := hr.gep (k := 25) (by decide)
  have g26 := hr.gep (k := 26) (by decide)
  have g27 := hr.gep (k := 27) (by decide)
  have g28 := hr.gep (k := 28) (by decide)
  have g29 := hr.gep (k := 29) (by decide)
  have g30 := hr.gep (k := 30) (by decide)
  have g31 := hr.gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat] at gn g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31
  change List.foldlM Instr.run E (((program.entry p g).body.drop 375).take 33) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run,
     Operation.gepInboundsIndex, GepIndex.inboundsOffset, Operation.GepSignedRange,
     EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
     setupEnv, throwUBIf,
     er, en, gn, c1, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c50, c54, c59, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
