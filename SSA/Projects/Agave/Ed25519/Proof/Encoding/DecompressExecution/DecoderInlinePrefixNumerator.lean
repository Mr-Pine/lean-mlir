import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixParse
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.InlineWords
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.VectorMemory

/-! Original bb0:74--104 vector bias/carry execution. Every flagged operation
is discharged by the existing arbitrary-word overflow bounds. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul SerialPoint
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

theorem vector_two (f : Fin 2 → α) : Vector.ofFn f = #v[f 0, f 1] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

def numeratorEnvA (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  let b := numeratorBias x
  E[%62 := .value (a.add 8#64), %63 := .value (a.add 24#64),
    %64 := .value (r.add 8#64),
    %65 := Ty.wrap #v[x 0, x 1], %66 := Ty.wrap #v[x 1, x 2],
    %67 := Ty.wrap #v[b 0, b 1], %68 := Ty.wrap #v[b 1, b 2],
    %69 := Ty.wrap #v[b 0 >>> 51, b 1 >>> 51], %70 := .value (b 0),
    %71 := .value (b 0 &&& 2251799813685247#64),
    %72 := Ty.wrap #v[b 1 &&& 2251799813685247#64, b 2 &&& 2251799813685247#64]]

def numeratorEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  let b := numeratorBias x
  E[%62 := .value (a.add 8#64), %63 := .value (a.add 24#64),
    %64 := .value (r.add 8#64),
    %65 := Ty.wrap #v[x 0, x 1], %66 := Ty.wrap #v[x 1, x 2],
    %67 := Ty.wrap #v[b 0, b 1], %68 := Ty.wrap #v[b 1, b 2],
    %69 := Ty.wrap #v[b 0 >>> 51, b 1 >>> 51], %70 := .value (b 0),
    %71 := .value (b 0 &&& 2251799813685247#64),
    %72 := Ty.wrap #v[b 1 &&& 2251799813685247#64, b 2 &&& 2251799813685247#64],
    %73 := Ty.wrap #v[(b 1 &&& 2251799813685247#64) + (b 0 >>> 51),
      (b 2 &&& 2251799813685247#64) + (b 1 >>> 51)],
    %74 := .value (r.add 24#64), %75 := Ty.wrap #v[x 3, x 4],
    %76 := Ty.wrap #v[b 3, b 4], %77 := .value (b 4),
    %78 := .value (b 4 >>> 51),
    %79 := Ty.wrap #v[b 3 &&& 2251799813685247#64, b 4 &&& 2251799813685247#64],
    %80 := .value ((b 4 >>> 51) * 19#64),
    %81 := Ty.wrap #v[b 2, b 3], %82 := Ty.wrap #v[b 2 >>> 51, b 3 >>> 51],
    %83 := .value ((b 4 >>> 51) * 19#64 + (b 0 &&& 2251799813685247#64)),
    %84 := Ty.wrap #v[(b 3 &&& 2251799813685247#64) + (b 2 >>> 51),
      (b 4 &&& 2251799813685247#64) + (b 3 >>> 51)]]

structure NumeratorRegisters (E : Env program.Γ) (r a : Pointer) : Prop where
  r33 : E.read (%33) = .value r
  a34 : E.read (%34) = .value a
  c1 : E.read (%1) = .value 2251799813685247#64
  c5 : E.read (%5) = .value 19#64
  c6 : E.read (%6) = .value 1#64
  c7 : E.read (%7) = .value 24#64
  c8 : E.read (%8) = .value 8#64
  c11 : E.read (%11) = Ty.wrap #v[36028797018963663#64, 36028797018963952#64]
  c12 : E.read (%12) = Ty.wrap (Vector.replicate 2 36028797018963952#64)
  c13 : E.read (%13) = Ty.wrap (Vector.replicate 2 51#64)
  c14 : E.read (%14) = .value 0#64
  c15 : E.read (%15) = Ty.wrap (Vector.replicate 2 2251799813685247#64)
  c16 : E.read (%16) = .value 51#64

theorem numerator_registers (g : Globals) (s : GlobalState) (out input : Pointer) :
    NumeratorRegisters (parseEnv g s out input) (slot3 s) (slot4 s) := by
  constructor <;> rfl

def numeratorLoadEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  E[%62 := .value (a.add 8#64), %63 := .value (a.add 24#64),
    %64 := .value (r.add 8#64), %65 := Ty.wrap #v[x 0, x 1],
    %66 := Ty.wrap #v[x 1, x 2]]

theorem numerator_load_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (hr : SmallRange s.mem r 40)
    (ha : SmallRange s.mem a 40) (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 74 8 E s =
      .value (numeratorLoadEnv E r a (readLimbs s a), s) := by
  obtain ⟨e33,e34,e1,e5,e6,e7,e8,e11,e12,e13,e14,e15,e16⟩ := he
  have ga8 := ha.gep (k := 8) (by decide)
  have ga24 := ha.gep (k := 24) (by decide)
  have gr8 := hr.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at ga8 ga24 gr8
  have fa0 := ha.fits_add (k := 0) (count := 16) (by decide)
  have fa8 := ha.fits_add (k := 8) (count := 16) (by decide)
  have va0 := smallRange_add ha (k := 0) (count := 16) (by decide)
  have va8 := smallRange_add ha (k := 8) (count := 16) (by decide)
  simp only [Pointer.add_zero] at fa0 va0
  change List.foldlM Instr.run E (((program.bb0 p g).body.drop 74).take 8) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      Operation.load, Operation.gepInboundsIndex, GepIndex.inboundsOffset,
      Operation.GepSignedRange, EffectM.bind_eq, EffectM.pure_eq,
      PoisonOr.value_bind, mlir_env, mlir_effect, mlir_operation,
      e33,e34,e7,e8, ga8,ga24,gr8,fa0,fa8, load_two_words, va0,va8,
      numeratorLoadEnv, readLimbs, vector_two,
      extract_two_low, extract_two_high, Pointer.add_add, throwUBIf]

def biasOneEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  (numeratorLoadEnv E r a x)[%67 := Ty.wrap #v[numeratorBias x 0, numeratorBias x 1],
    %68 := Ty.wrap #v[numeratorBias x 1, numeratorBias x 2]]

def biasTwoEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  (biasOneEnv E r a x)[%69 := Ty.wrap #v[numeratorBias x 0 >>> 51, numeratorBias x 1 >>> 51],
    %70 := .value (numeratorBias x 0)]

theorem bias_one_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 82 2 (numeratorLoadEnv E r a x) s =
      .value (biasOneEnv E r a x, s) := by
  obtain ⟨e33,e34,e1,e5,e6,e7,e8,e11,e12,e13,e14,e15,e16⟩ := he
  change List.foldlM Instr.run (numeratorLoadEnv E r a x)
    (((program.bb0 p g).body.drop 82).take 2) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_operation,
      e1,e11,e12,e13,e14,e15, biasOneEnv, numeratorLoadEnv, numeratorBias, vector_two]

theorem bias_two_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 84 2 (biasOneEnv E r a x) s =
      .value (biasTwoEnv E r a x, s) := by
  obtain ⟨e33,e34,e1,e5,e6,e7,e8,e11,e12,e13,e14,e15,e16⟩ := he
  change List.foldlM Instr.run (biasOneEnv E r a x)
    (((program.bb0 p g).body.drop 84).take 2) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_operation,
      e1,e11,e12,e13,e14,e15, biasTwoEnv, biasOneEnv, numeratorLoadEnv, numeratorBias, vector_two]

theorem bias_three_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 86 2 (biasTwoEnv E r a x) s =
      .value (numeratorEnvA E r a x, s) := by
  obtain ⟨e33,e34,e1,e5,e6,e7,e8,e11,e12,e13,e14,e15,e16⟩ := he
  change List.foldlM Instr.run (biasTwoEnv E r a x)
    (((program.bb0 p g).body.drop 86).take 2) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_operation,
      e1,e11,e12,e13,e14,e15, biasTwoEnv, biasOneEnv, numeratorLoadEnv, numeratorEnvA, numeratorBias, vector_two]

theorem numerator_bias_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (x : Words) (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 82 6 (numeratorLoadEnv E r a x) s =
      .value (numeratorEnvA E r a x, s) := by
  have hsplit : (((program p g).blocks 0).body.drop 82).take 6 =
      (((program p g).blocks 0).body.drop 82).take 2 ++
      (((program p g).blocks 0).body.drop 84).take 2 ++
      (((program p g).blocks 0).body.drop 86).take 2 := rfl
  unfold Cutpoint.segment
  rw [hsplit, List.foldlM_append, List.foldlM_append]
  change ((Cutpoint.segment (program p g) 0 82 2 (numeratorLoadEnv E r a x) >>=
    fun F => Cutpoint.segment (program p g) 0 84 2 F) >>=
    fun F => Cutpoint.segment (program p g) 0 86 2 F) s = _
  simp only [EffectM.bind_eq, bias_one_segment p g E s r a x he,
    PoisonOr.value_bind, bias_two_segment p g E s r a x he,
    bias_three_segment p g E s r a x he]

theorem numerator_segment_A (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (hr : SmallRange s.mem r 40)
    (ha : SmallRange s.mem a 40) (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 74 14 E s =
      .value (numeratorEnvA E r a (readLimbs s a), s) := by
  have hsplit : (((program p g).blocks 0).body.drop 74).take 14 =
      (((program p g).blocks 0).body.drop 74).take 8 ++
      (((program p g).blocks 0).body.drop 82).take 6 := rfl
  unfold Cutpoint.segment
  rw [hsplit, List.foldlM_append]
  change (Cutpoint.segment (program p g) 0 74 8 E >>=
    fun F => Cutpoint.segment (program p g) 0 82 6 F) s = _
  simp only [EffectM.bind_eq, numerator_load_segment p g E s r a hr ha he,
    PoisonOr.value_bind, numerator_bias_segment p g E s r a _ he]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
