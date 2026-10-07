import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixOperations

/-! Small original-source slices for the numerator's flagged carries and
three stores. No symbolic operation is substituted for an RIR instruction. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul SerialPoint
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

theorem pack_pair (a b : BitVec 64) : BitVec.packLanes #v[a, b] = b ++ a := by
  change (0#0 ++ b) ++ a = b ++ a
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero]
  grind only

def carryOne (x : Words) : BitVec 64 :=
  (numeratorBias x 1 &&& 2251799813685247#64) + (numeratorBias x 0 >>> 51)
def carryTwo (x : Words) : BitVec 64 :=
  (numeratorBias x 2 &&& 2251799813685247#64) + (numeratorBias x 1 >>> 51)
def carryThree (x : Words) : BitVec 64 :=
  (numeratorBias x 3 &&& 2251799813685247#64) + (numeratorBias x 2 >>> 51)
def carryFour (x : Words) : BitVec 64 :=
  (numeratorBias x 4 &&& 2251799813685247#64) + (numeratorBias x 3 >>> 51)
def carryZero (x : Words) : BitVec 64 :=
  (numeratorBias x 4 >>> 51) * 19#64 + (numeratorBias x 0 &&& 2251799813685247#64)

def carryOneState (s : GlobalState) (r : Pointer) (x : Words) : GlobalState :=
  {s with mem := s.mem.storeAt (r.add 8#64) (BitVec.packLanes #v[carryOne x, carryTwo x])}

def carryResultState (s : GlobalState) (r : Pointer) (x : Words) : GlobalState :=
  {s with mem := (s.mem.storeAt r (carryZero x)).storeAt (r.add 24#64) (BitVec.packLanes #v[carryThree x, carryFour x])}

def carryOneEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  (numeratorEnvA E r a x)[%73 := Ty.wrap #v[carryOne x, carryTwo x]]

def carryLoadEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  (carryOneEnv E r a x)[%74 := .value (r.add 24#64), %75 := Ty.wrap #v[x 3, x 4]]

def carryBiasEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  (carryLoadEnv E r a x)[%76 := Ty.wrap #v[numeratorBias x 3, numeratorBias x 4],
    %77 := .value (numeratorBias x 4), %78 := .value (numeratorBias x 4 >>> 51)]

def carryPrepEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  (carryBiasEnv E r a x)[%79 := Ty.wrap #v[numeratorBias x 3 &&& 2251799813685247#64, numeratorBias x 4 &&& 2251799813685247#64],
    %80 := .value ((numeratorBias x 4 >>> 51) * 19#64)]

def carryShuffleEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  (carryPrepEnv E r a x)[%81 := Ty.wrap #v[numeratorBias x 2, numeratorBias x 3],
    %82 := Ty.wrap #v[numeratorBias x 2 >>> 51, numeratorBias x 3 >>> 51]]

def carryEndEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  (carryShuffleEnv E r a x)[%83 := .value (carryZero x), %84 := Ty.wrap #v[carryThree x, carryFour x]]

theorem carry_add_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (hr : SmallRange s.mem r 40)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 88 1 (numeratorEnvA E r a x) s =
      .value (carryOneEnv E r a x, s) := by
  have e72 : (numeratorEnvA E r a x).read (%72) = Ty.wrap #v[numeratorBias x 1 &&& 2251799813685247#64, numeratorBias x 2 &&& 2251799813685247#64] := rfl
  have e69 : (numeratorEnvA E r a x).read (%69) = Ty.wrap #v[numeratorBias x 0 >>> 51, numeratorBias x 1 >>> 51] := rfl
  change List.foldlM Instr.run (numeratorEnvA E r a x)
    (((program.bb0 p g).body.drop 88).take 1) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    e72, e69, carry_vector_operation, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, carryOneEnv, carryOne, carryTwo, carryThree, carryFour, carryZero]

theorem carry_first_store_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (hr : SmallRange s.mem r 40)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 89 1 (carryOneEnv E r a x) s =
      .value (carryOneEnv E r a x, carryOneState s r x) := by
  have e73 : (carryOneEnv E r a x).read (%73) = Ty.wrap #v[carryOne x, carryTwo x] := rfl
  have e64 : (carryOneEnv E r a x).read (%64) = .value (r.add 8#64) := rfl
  have fr8 := hr.fits_add (k := 8) (count := 16) (by decide)
  change List.foldlM Instr.run (carryOneEnv E r a x)
    (((program.bb0 p g).body.drop 89).take 1) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect, mlir_operation,
      Operation.load, Operation.store, Operation.gepInboundsIndex, GepIndex.inboundsOffset,
      Operation.GepSignedRange, throwUBIf, Fits.storeAt_iff,
      e73, e64,
      carryOneState, carryResultState, carryOne,carryTwo,carryThree,carryFour,carryZero,
      vector_two, weak_carry_add_nooverflow, weak_mul_nooverflow,
      weak_fold_nooverflow, load_two_words, extract_two_low,extract_two_high,
      Pointer.add_add, fr8]

theorem carry_one_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (hr : SmallRange s.mem r 40)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 88 2 (numeratorEnvA E r a x) s =
      .value (carryOneEnv E r a x, carryOneState s r x) := by
  have hs : (((program p g).blocks 0).body.drop 88).take 2 =
      (((program p g).blocks 0).body.drop 88).take 1 ++
      (((program p g).blocks 0).body.drop 89).take 1 := rfl
  unfold Cutpoint.segment
  rw [hs, List.foldlM_append]
  change (Cutpoint.segment (program p g) 0 88 1 (numeratorEnvA E r a x) >>=
    fun F => Cutpoint.segment (program p g) 0 89 1 F) s = _
  simp only [EffectM.bind_eq, carry_add_segment p g E s r a x hr he,
    PoisonOr.value_bind, carry_first_store_segment p g E s r a x hr he]

theorem carry_load_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (hr : SmallRange s.mem r 40)
    (ha : SmallRange s.mem a 40) (hx : readLimbs s a = x)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 90 2 (carryOneEnv E r a x) s =
      .value (carryLoadEnv E r a x, s) := by
  have e33 : (carryOneEnv E r a x).read (%33) = .value r := by
    simpa (disch := decide) only [carryEndEnv, carryShuffleEnv, carryPrepEnv, carryBiasEnv, carryLoadEnv, carryOneEnv, numeratorEnvA, mlir_env] using he.r33
  have e63 : (carryOneEnv E r a x).read (%63) = .value (a.add 24#64) := rfl
  have gr24 := hr.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at gr24
  have fa24 := ha.fits_add (k := 24) (count := 16) (by decide)
  have va24 := smallRange_add ha (k := 24) (count := 16) (by decide)
  have hx3 : s.mem.readAt (a.add 24#64) 64 = x 3 := congrFun hx 3
  have hx4 : s.mem.readAt (a.add 32#64) 64 = x 4 := congrFun hx 4
  change List.foldlM Instr.run (carryOneEnv E r a x)
    (((program.bb0 p g).body.drop 90).take 2) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect, mlir_operation,
      Operation.load, Operation.store, Operation.gepInboundsIndex, GepIndex.inboundsOffset,
      Operation.GepSignedRange, throwUBIf, Fits.storeAt_iff,
      e33, e63,
      carryLoadEnv,
      carryOneState, carryResultState, carryOne,carryTwo,carryThree,carryFour,carryZero,
      vector_two, weak_carry_add_nooverflow, weak_mul_nooverflow,
      weak_fold_nooverflow, load_two_words, extract_two_low,extract_two_high,
      Pointer.add_add, gr24, fa24, va24, hx3, hx4]

theorem carry_bias_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 92 3 (carryLoadEnv E r a x) s =
      .value (carryBiasEnv E r a x, s) := by
  have e75 : (carryLoadEnv E r a x).read (%75) = Ty.wrap #v[x 3, x 4] := rfl
  have e12 : (carryLoadEnv E r a x).read (%12) = Ty.wrap (Vector.replicate 2 36028797018963952#64) := by
    simpa (disch := decide) only [carryEndEnv, carryShuffleEnv, carryPrepEnv, carryBiasEnv, carryLoadEnv, carryOneEnv, numeratorEnvA, mlir_env] using he.c12
  have e6 : (carryLoadEnv E r a x).read (%6) = .value 1#64 := by
    simpa (disch := decide) only [carryEndEnv, carryShuffleEnv, carryPrepEnv, carryBiasEnv, carryLoadEnv, carryOneEnv, numeratorEnvA, mlir_env] using he.c6
  have e16 : (carryLoadEnv E r a x).read (%16) = .value 51#64 := by
    simpa (disch := decide) only [carryEndEnv, carryShuffleEnv, carryPrepEnv, carryBiasEnv, carryLoadEnv, carryOneEnv, numeratorEnvA, mlir_env] using he.c16
  change List.foldlM Instr.run (carryLoadEnv E r a x)
    (((program.bb0 p g).body.drop 92).take 3) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect, mlir_operation,
      Operation.load, Operation.store, Operation.gepInboundsIndex, GepIndex.inboundsOffset,
      Operation.GepSignedRange, throwUBIf, Fits.storeAt_iff,
      e75, e12, e6, e16,
      carryBiasEnv,
      carryOneState, carryResultState, carryOne,carryTwo,carryThree,carryFour,carryZero,
      vector_two, weak_carry_add_nooverflow, weak_mul_nooverflow,
      weak_fold_nooverflow, load_two_words, extract_two_low,extract_two_high,
      Pointer.add_add]
  rfl

theorem carry_prep_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 95 2 (carryBiasEnv E r a x) s =
      .value (carryPrepEnv E r a x, s) := by
  have e76 : (carryBiasEnv E r a x).read (%76) = Ty.wrap #v[numeratorBias x 3, numeratorBias x 4] := rfl
  have e15 : (carryBiasEnv E r a x).read (%15) = Ty.wrap (Vector.replicate 2 2251799813685247#64) := by
    simpa (disch := decide) only [carryEndEnv, carryShuffleEnv, carryPrepEnv, carryBiasEnv, carryLoadEnv, carryOneEnv, numeratorEnvA, mlir_env] using he.c15
  have e78 : (carryBiasEnv E r a x).read (%78) = .value (numeratorBias x 4 >>> 51) := rfl
  have e5 : (carryBiasEnv E r a x).read (%5) = .value 19#64 := by
    simpa (disch := decide) only [carryEndEnv, carryShuffleEnv, carryPrepEnv, carryBiasEnv, carryLoadEnv, carryOneEnv, numeratorEnvA, mlir_env] using he.c5
  change List.foldlM Instr.run (carryBiasEnv E r a x)
    (((program.bb0 p g).body.drop 95).take 2) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect, mlir_operation,
      Operation.load, Operation.store, Operation.gepInboundsIndex, GepIndex.inboundsOffset,
      Operation.GepSignedRange, throwUBIf, Fits.storeAt_iff,
      e76, e15, e78, e5,
      carryPrepEnv,
      carryOneState, carryResultState, carryOne,carryTwo,carryThree,carryFour,carryZero,
      vector_two, weak_carry_add_nooverflow, weak_mul_nooverflow,
      weak_fold_nooverflow, load_two_words, extract_two_low,extract_two_high,
      Pointer.add_add]

theorem carry_shuffle_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 97 2 (carryPrepEnv E r a x) s =
      .value (carryShuffleEnv E r a x, s) := by
  have e68 : (carryPrepEnv E r a x).read (%68) = Ty.wrap #v[numeratorBias x 1, numeratorBias x 2] := rfl
  have e76 : (carryPrepEnv E r a x).read (%76) = Ty.wrap #v[numeratorBias x 3, numeratorBias x 4] := rfl
  have e13 : (carryPrepEnv E r a x).read (%13) = Ty.wrap (Vector.replicate 2 51#64) := by
    simpa (disch := decide) only [carryEndEnv, carryShuffleEnv, carryPrepEnv, carryBiasEnv, carryLoadEnv, carryOneEnv, numeratorEnvA, mlir_env] using he.c13
  change List.foldlM Instr.run (carryPrepEnv E r a x)
    (((program.bb0 p g).body.drop 97).take 2) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect, mlir_operation,
      Operation.load, Operation.store, Operation.gepInboundsIndex, GepIndex.inboundsOffset,
      Operation.GepSignedRange, throwUBIf, Fits.storeAt_iff,
      e68, e76, e13,
      carryShuffleEnv,
      carryOneState, carryResultState, carryOne,carryTwo,carryThree,carryFour,carryZero,
      vector_two, weak_carry_add_nooverflow, weak_mul_nooverflow,
      weak_fold_nooverflow, load_two_words, extract_two_low,extract_two_high,
      Pointer.add_add]

def carryZeroEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  (carryShuffleEnv E r a x)[%83 := .value (carryZero x)]

theorem carry_zero_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 99 1 (carryShuffleEnv E r a x) s =
      .value (carryZeroEnv E r a x, s) := by
  have e80 : (carryShuffleEnv E r a x).read (%80) = .value ((numeratorBias x 4 >>> 51) * 19#64) := rfl
  have e71 : (carryShuffleEnv E r a x).read (%71) = .value (numeratorBias x 0 &&& 2251799813685247#64) := rfl
  change List.foldlM Instr.run (carryShuffleEnv E r a x)
    (((program.bb0 p g).body.drop 99).take 1) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    e80, e71, carry_vector_operation, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, carryZeroEnv, carryOne, carryTwo, carryThree, carryFour, carryZero, BinOp.compute, fold_operation]

theorem carry_last_vector_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 100 1 (carryZeroEnv E r a x) s =
      .value (carryEndEnv E r a x, s) := by
  have e79 : (carryZeroEnv E r a x).read (%79) = Ty.wrap #v[numeratorBias x 3 &&& 2251799813685247#64, numeratorBias x 4 &&& 2251799813685247#64] := rfl
  have e82 : (carryZeroEnv E r a x).read (%82) = Ty.wrap #v[numeratorBias x 2 >>> 51, numeratorBias x 3 >>> 51] := rfl
  change List.foldlM Instr.run (carryZeroEnv E r a x)
    (((program.bb0 p g).body.drop 100).take 1) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    e79, e82, carry_vector_operation, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, carryEndEnv, carryOne, carryTwo, carryThree, carryFour, carryZero]
  rfl

theorem carry_end_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 99 2 (carryShuffleEnv E r a x) s =
      .value (carryEndEnv E r a x, s) := by
  have hs : (((program p g).blocks 0).body.drop 99).take 2 =
      (((program p g).blocks 0).body.drop 99).take 1 ++
      (((program p g).blocks 0).body.drop 100).take 1 := rfl
  unfold Cutpoint.segment
  rw [hs, List.foldlM_append]
  change (Cutpoint.segment (program p g) 0 99 1 (carryShuffleEnv E r a x) >>=
    fun F => Cutpoint.segment (program p g) 0 100 1 F) s = _
  simp only [EffectM.bind_eq, carry_zero_segment p g E s r a x he,
    PoisonOr.value_bind, carry_last_vector_segment p g E s r a x he]

theorem carry_store_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (hr : SmallRange s.mem r 40)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 101 4 (carryEndEnv E r a x) s =
      .value (carryEndEnv E r a x, carryResultState s r x) := by
  have e33 : (carryEndEnv E r a x).read (%33) = .value r := by
    simpa (disch := decide) only [carryEndEnv, carryShuffleEnv, carryPrepEnv, carryBiasEnv, carryLoadEnv, carryOneEnv, numeratorEnvA, mlir_env] using he.r33
  have e74 : (carryEndEnv E r a x).read (%74) = .value (r.add 24#64) := rfl
  have e83 : (carryEndEnv E r a x).read (%83) = .value (carryZero x) := rfl
  have e84 : (carryEndEnv E r a x).read (%84) = Ty.wrap #v[carryThree x, carryFour x] := rfl
  have fr0 := hr.fits_add (k := 0) (count := 8) (by decide)
  have fr24 := hr.fits_add (k := 24) (count := 16) (by decide)
  simp only [Pointer.add_zero] at fr0
  change List.foldlM Instr.run (carryEndEnv E r a x)
    (((program.bb0 p g).body.drop 101).take 4) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect, mlir_operation,
      Operation.load, Operation.store, Operation.gepInboundsIndex, GepIndex.inboundsOffset,
      Operation.GepSignedRange, throwUBIf, Fits.storeAt_iff,
      e33, e74, e83, e84,
      carryOneState, carryResultState, carryOne,carryTwo,carryThree,carryFour,carryZero,
      vector_two, weak_carry_add_nooverflow, weak_mul_nooverflow,
      weak_fold_nooverflow, load_two_words, extract_two_low,extract_two_high,
      Pointer.add_add, fr0, fr24]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
