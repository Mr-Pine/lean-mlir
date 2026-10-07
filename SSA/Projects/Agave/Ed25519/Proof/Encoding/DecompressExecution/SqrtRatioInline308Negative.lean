import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Copy

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open SerialPoint.Execution
open Decode.InlinePrefix (carry_operation fold_operation)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

attribute [local implicit_reducible] Ty.width

theorem vector_four (f : Fin 4 → α) : Vector.ofFn f = #v[f 0, f 1, f 2, f 3] := by
  ext i hi
  interval_cases i <;> rfl

theorem load_four_words (m : MemoryState) (p : Pointer) (h : SmallRange m p 32) :
    (Ty.vec 4 64).unflatten (m.readAt p 256) =
      Ty.wrap #v[m.readAt p 64, m.readAt (p.add 8) 64,
        m.readAt (p.add 16) 64, m.readAt (p.add 24) 64] := by
  have h0 : m.readAt p 64 = (m.readAt p 256).extractLsb' 0 64 := by
    simpa using (MemoryState.readAt_add_of_readAt (off := 0#64) (w := 64)
      h.fits (h.no_wrap (k := 0) (by decide)) (by decide) rfl)
  have h1 : m.readAt (p.add 8) 64 = (m.readAt p 256).extractLsb' 64 64 := by
    simpa using (MemoryState.readAt_add_of_readAt (off := 8#64) (w := 64)
      h.fits (h.no_wrap (k := 8) (by decide)) (by decide) rfl)
  have h2 : m.readAt (p.add 16) 64 = (m.readAt p 256).extractLsb' 128 64 := by
    simpa using (MemoryState.readAt_add_of_readAt (off := 16#64) (w := 64)
      h.fits (h.no_wrap (k := 16) (by decide)) (by decide) rfl)
  have h3 : m.readAt (p.add 24) 64 = (m.readAt p 256).extractLsb' 192 64 := by
    simpa using (MemoryState.readAt_add_of_readAt (off := 24#64) (w := 64)
      h.fits (h.no_wrap (k := 24) (by decide)) (by decide) rfl)
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [Ty.unflatten, Ty.extractVecElem, Ty.wrap, h0]
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm

theorem extract_four_0 (m : MemoryState) (p : Pointer) (h : SmallRange m p 32) :
    Ty.extractVecElem 4 64 0 (m.readAt p 256) = m.readAt p 64 := by
  symm
  simpa [Ty.extractVecElem] using
    (MemoryState.readAt_add_of_readAt (off := 0#64) (w := 64)
      h.fits (h.no_wrap (k := 0) (by decide)) (by decide) rfl)

theorem extract_four_1 (m : MemoryState) (p : Pointer) (h : SmallRange m p 32) :
    Ty.extractVecElem 4 64 1 (m.readAt p 256) = m.readAt (p.add 8#64) 64 := by
  symm
  simpa [Ty.extractVecElem] using
    (MemoryState.readAt_add_of_readAt (off := 8#64) (w := 64)
      h.fits (h.no_wrap (k := 8) (by decide)) (by decide) rfl)

theorem extract_four_2 (m : MemoryState) (p : Pointer) (h : SmallRange m p 32) :
    Ty.extractVecElem 4 64 2 (m.readAt p 256) = m.readAt (p.add 16#64) 64 := by
  symm
  simpa [Ty.extractVecElem] using
    (MemoryState.readAt_add_of_readAt (off := 16#64) (w := 64)
      h.fits (h.no_wrap (k := 16) (by decide)) (by decide) rfl)

theorem extract_four_3 (m : MemoryState) (p : Pointer) (h : SmallRange m p 32) :
    Ty.extractVecElem 4 64 3 (m.readAt p 256) = m.readAt (p.add 24#64) 64 := by
  symm
  simpa [Ty.extractVecElem] using
    (MemoryState.readAt_add_of_readAt (off := 24#64) (w := 64)
      h.fits (h.no_wrap (k := 24) (by decide)) (by decide) rfl)

def bias (x : Words) : Words :=
  ![36028797018963664#64 - x 0, 36028797018963952#64 - x 1,
    36028797018963952#64 - x 2, 36028797018963952#64 - x 3,
    36028797018963952#64 - x 4]

def negated (x : Words) : Words := ![
  (bias x 4 >>> 51) * 19#64 + (bias x 0 &&& 2251799813685247#64),
  (bias x 1 &&& 2251799813685247#64) + (bias x 0 >>> 51),
  (bias x 2 &&& 2251799813685247#64) + (bias x 1 >>> 51),
  (bias x 3 &&& 2251799813685247#64) + (bias x 2 >>> 51),
  (bias x 4 &&& 2251799813685247#64) + (bias x 3 >>> 51)]

theorem negated_eq (x : Words) : negated x = negativeWords x := by
  funext i
  fin_cases i <;> simp [negated, bias, negativeWords, SerialPoint.subWord,
    SerialPoint.weakWord, SerialPoint.biasedSubWord, SerialPoint.bias, zeroWords, BitVec.add_comm]

def negativeEnv (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%301 := Ty.wrap #v[x 0, x 1, x 2, x 3],
    %302 := Ty.wrap #v[x 1, x 2, x 3, x 4],
    %303 := Ty.wrap #v[bias x 0, bias x 1, bias x 2, bias x 3],
    %304 := Ty.wrap #v[bias x 1, bias x 2, bias x 3, bias x 4],
    %305 := Ty.wrap #v[bias x 0 >>> 51, bias x 1 >>> 51, bias x 2 >>> 51, bias x 3 >>> 51],
    %306 := .value (bias x 4), %307 := .value (bias x 4 >>> 51),
    %308 := .value (bias x 0), %309 := .value (bias x 0 &&& 2251799813685247#64),
    %310 := Ty.wrap #v[bias x 1 &&& 2251799813685247#64, bias x 2 &&& 2251799813685247#64,
      bias x 3 &&& 2251799813685247#64, bias x 4 &&& 2251799813685247#64],
    %311 := .value ((bias x 4 >>> 51) * 19#64),
    %312 := .value (negated x 0),
    %313 := Ty.wrap #v[negated x 1, negated x 2, negated x 3, negated x 4]]

def negativeLoadEnv (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%301 := Ty.wrap #v[x 0, x 1, x 2, x 3], %302 := Ty.wrap #v[x 1, x 2, x 3, x 4]]
def negativeBiasEnv (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%303 := Ty.wrap #v[bias x 0, bias x 1, bias x 2, bias x 3],
    %304 := Ty.wrap #v[bias x 1, bias x 2, bias x 3, bias x 4]]
def negativePrepEnv (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%305 := Ty.wrap #v[bias x 0 >>> 51, bias x 1 >>> 51, bias x 2 >>> 51, bias x 3 >>> 51],
    %306 := .value (bias x 4), %307 := .value (bias x 4 >>> 51),
    %308 := .value (bias x 0), %309 := .value (bias x 0 &&& 2251799813685247#64),
    %310 := Ty.wrap #v[bias x 1 &&& 2251799813685247#64, bias x 2 &&& 2251799813685247#64,
      bias x 3 &&& 2251799813685247#64, bias x 4 &&& 2251799813685247#64]]
def negativeCarryEnv (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%311 := .value ((bias x 4 >>> 51) * 19#64), %312 := .value (negated x 0),
    %313 := Ty.wrap #v[negated x 1, negated x 2, negated x 3, negated x 4]]

theorem negative_load (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (u : Pointer) (hu : SmallRange s.mem u 40)
    (eu : E.read (%arg1) = .value u)
    (eu8 : E.read (%237) = .value (u.add 8#64)) :
    Cutpoint.segment (program p g) 0 408 2 E s =
      .value (negativeLoadEnv E (readLimbs s u), s) := by
  simp only [Env.read_arg] at eu
  have h0 := SerialPoint.Execution.smallRange_add hu (k := 0) (count := 32) (by decide)
  have h8 := SerialPoint.Execution.smallRange_add hu (k := 8) (count := 32) (by decide)
  have f0 := hu.fits_add (k := 0) (count := 32) (by decide)
  have f8 := hu.fits_add (k := 8) (count := 32) (by decide)
  simp only [Pointer.add_zero] at h0 f0
  change List.foldlM Instr.run E (((program.entry p g).body.drop 408).take 2) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
     EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
     mlir_operation, eu, eu8, h0, h8, f0, f8, negativeLoadEnv, readLimbs,
     Pointer.add_add, Pointer.add_zero, vector_four,
     extract_four_0, extract_four_1, extract_four_2, extract_four_3, throwUBIf]

theorem negative_bias (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e301 : E.read (%301) = Ty.wrap #v[x 0, x 1, x 2, x 3])
    (e302 : E.read (%302) = Ty.wrap #v[x 1, x 2, x 3, x 4])
    (e47 : E.read (%47) = Ty.wrap #v[36028797018963664#64,36028797018963952#64,36028797018963952#64,36028797018963952#64])
    (e48 : E.read (%48) = Ty.wrap (Vector.replicate 4 36028797018963952#64)) :
    Cutpoint.segment (program p g) 0 410 2 E s = .value (negativeBiasEnv E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 410).take 2) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_operation,
    e301, e302, e47, e48, negativeBiasEnv, bias, vector_four]

theorem negative_prep (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e303 : E.read (%303) = Ty.wrap #v[bias x 0,bias x 1,bias x 2,bias x 3])
    (e304 : E.read (%304) = Ty.wrap #v[bias x 1,bias x 2,bias x 3,bias x 4])
    (e49 : E.read (%49) = Ty.wrap (Vector.replicate 4 51#64))
    (e12 : E.read (%12) = .value 3#64) (e7 : E.read (%7) = .value 51#64)
    (e50 : E.read (%50) = .value 0#64) (e8 : E.read (%8) = .value 2251799813685247#64)
    (e51 : E.read (%51) = Ty.wrap (Vector.replicate 4 2251799813685247#64)) :
    Cutpoint.segment (program p g) 0 412 6 E s = .value (negativePrepEnv E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 412).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_operation,
    e303, e304, e49, e12, e7, e50, e8, e51, negativePrepEnv, vector_four]

theorem negative_mul_operation (x : Words) :
    BinOp.compute (.mul {nsw := true, nuw := true})
      (.value (bias x 4 >>> 51)) (.value 19#64) = .value ((bias x 4 >>> 51) * 19#64) := by
  have hs := (SerialPoint.weak_mul_nooverflow (bias x 4)).2
  have hu := (SerialPoint.weak_mul_nooverflow (bias x 4)).1
  simp only [BinOp.compute, Operation.mul, PoisonOr.value_bind, hs, hu,
    Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]

theorem negative_fold_operation (x : Words) :
    BinOp.compute (.add {nsw := true, nuw := true})
      (.value ((bias x 4 >>> 51) * 19#64))
      (.value (bias x 0 &&& 2251799813685247#64)) = .value (negated x 0) :=
  fold_operation (bias x 4) (bias x 0)

theorem negative_vector_operation (x : Words) :
    BinOp.compute (.vector (.add {nsw := true, nuw := true}))
      (Ty.wrap #v[bias x 1 &&& 2251799813685247#64,bias x 2 &&& 2251799813685247#64,
        bias x 3 &&& 2251799813685247#64,bias x 4 &&& 2251799813685247#64])
      (Ty.wrap #v[bias x 0 >>> 51,bias x 1 >>> 51,bias x 2 >>> 51,bias x 3 >>> 51]) =
        Ty.wrap #v[negated x 1,negated x 2,negated x 3,negated x 4] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [BinOp.compute, Ty.wrap, carry_operation, negated]

theorem negative_carry (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e305 : E.read (%305) = Ty.wrap #v[bias x 0 >>> 51,bias x 1 >>> 51,bias x 2 >>> 51,bias x 3 >>> 51])
    (e307 : E.read (%307) = .value (bias x 4 >>> 51))
    (e309 : E.read (%309) = .value (bias x 0 &&& 2251799813685247#64))
    (e310 : E.read (%310) = Ty.wrap #v[bias x 1 &&& 2251799813685247#64,bias x 2 &&& 2251799813685247#64,bias x 3 &&& 2251799813685247#64,bias x 4 &&& 2251799813685247#64])
    (e9 : E.read (%9) = .value 19#64) :
    Cutpoint.segment (program p g) 0 418 3 E s = .value (negativeCarryEnv E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 418).take 3) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    e305, e307, e309, e310, e9, negativeCarryEnv,
    negative_mul_operation, negative_fold_operation, negative_vector_operation]

theorem negative_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (u : Pointer) (hu : SmallRange s.mem u 40)
    (hc : Constants E) (eu : E.read (%arg1) = .value u)
    (eu8 : E.read (%237) = .value (u.add 8#64)) :
    Cutpoint.segment (program p g) 0 408 13 E s =
      .value (negativeEnv E (readLimbs s u), s) := by
  let x := readLimbs s u
  have h0 := negative_load p g E s u hu eu eu8
  have h1 := negative_bias p g (negativeLoadEnv E x) s x (by rfl) (by rfl)
    (by simpa (disch := decide) only [negativeLoadEnv, mlir_env] using hc.c47)
    (by simpa (disch := decide) only [negativeLoadEnv, mlir_env] using hc.c48)
  have h2 := negative_prep p g (negativeBiasEnv (negativeLoadEnv E x) x) s x
    (by rfl) (by rfl)
    (by simpa (disch := decide) only [negativeBiasEnv, negativeLoadEnv, mlir_env] using hc.c49)
    (by simpa (disch := decide) only [negativeBiasEnv, negativeLoadEnv, mlir_env] using hc.c12)
    (by simpa (disch := decide) only [negativeBiasEnv, negativeLoadEnv, mlir_env] using hc.c7)
    (by simpa (disch := decide) only [negativeBiasEnv, negativeLoadEnv, mlir_env] using hc.c50)
    (by simpa (disch := decide) only [negativeBiasEnv, negativeLoadEnv, mlir_env] using hc.c8)
    (by simpa (disch := decide) only [negativeBiasEnv, negativeLoadEnv, mlir_env] using hc.c51)
  have h3 := negative_carry p g (negativePrepEnv (negativeBiasEnv (negativeLoadEnv E x) x) x) s x
    (by rfl) (by rfl) (by rfl) (by rfl)
    (by simpa (disch := decide) only [negativePrepEnv, negativeBiasEnv, negativeLoadEnv, mlir_env] using hc.c9)
  dsimp only [x] at h1 h2 h3
  rw [show 13 = 2 + 11 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h0, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 11 = 2 + 9 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h1, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 9 = 6 + 3 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h2, PoisonOr.value_bind, Nat.reduceAdd]
  rw [h3]
  rfl

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
