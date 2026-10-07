import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Arithmetic

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
open LeanMLIR.RIR SerialFieldMul
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem calc314 (x : Words) :
    Operation.lshr false (.value (x 0)) (.value (51#64)) = .value (a314 x) := by
  simp (disch := decide) [a314, mlir_operation]

theorem calc315 (x : Words) :
    Operation.extractelement (Ty.wrap #v[x 1, x 2, x 3, x 4]) (.value (0#64)) = .value (a315 x) := by
  simp (disch := decide) [a315, mlir_operation]

theorem calc316 (x : Words) :
    Operation.lshr false (.value (a315 x)) (.value (51#64)) = .value (a316 x) := by
  simp (disch := decide) [a316, mlir_operation]

theorem calc317 (x : Words) :
    Operation.extractelement (Ty.wrap #v[x 1, x 2, x 3, x 4]) (.value (1#64)) = .value (a317 x) := by
  simp (disch := decide) [a317, mlir_operation]

theorem calc318 (x : Words) :
    Operation.lshr false (.value (a317 x)) (.value (51#64)) = .value (a318 x) := by
  simp (disch := decide) [a318, mlir_operation]

theorem calc319 (x : Words) :
    Operation.extractelement (Ty.wrap #v[x 1, x 2, x 3, x 4]) (.value (2#64)) = .value (a319 x) := by
  simp (disch := decide) [a319, mlir_operation]

theorem calc320 (x : Words) :
    Operation.lshr false (.value (a319 x)) (.value (51#64)) = .value (a320 x) := by
  simp (disch := decide) [a320, mlir_operation]

theorem calc321 (x : Words) :
    Operation.extractelement (Ty.wrap #v[x 1, x 2, x 3, x 4]) (.value (3#64)) = .value (a321 x) := by
  simp (disch := decide) [a321, mlir_operation]

theorem calc322 (x : Words) :
    Operation.lshr false (.value (a321 x)) (.value (51#64)) = .value (a322 x) := by
  simp (disch := decide) [a322, mlir_operation]

theorem calc323 (x : Words) :
    Operation.and (.value (x 0)) (.value (2251799813685247#64)) = .value (a323 x) := by
  simp (disch := decide) [a323, mlir_operation]

theorem calc324 (x : Words) :
    Operation.and (.value (a315 x)) (.value (2251799813685247#64)) = .value (a324 x) := by
  simp (disch := decide) [a324, mlir_operation]

theorem calc325 (x : Words) :
    Operation.and (.value (a317 x)) (.value (2251799813685247#64)) = .value (a325 x) := by
  simp (disch := decide) [a325, mlir_operation]

theorem calc326 (x : Words) :
    Operation.and (.value (a319 x)) (.value (2251799813685247#64)) = .value (a326 x) := by
  simp (disch := decide) [a326, mlir_operation]

theorem calc327 (x : Words) :
    Operation.and (.value (a321 x)) (.value (2251799813685247#64)) = .value (a327 x) := by
  simp (disch := decide) [a327, mlir_operation]

theorem calc328 (x : Words) :
    Operation.mul {nsw := true, nuw := true} (.value (a322 x)) (.value (19#64)) = .value (a328 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h328

theorem calc329 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a328 x)) (.value (a323 x)) = .value (a329 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h329

theorem calc330 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a314 x)) (.value (a324 x)) = .value (a330 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h330

theorem calc331 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a325 x)) (.value (a316 x)) = .value (a331 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h331

theorem calc332 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a326 x)) (.value (a318 x)) = .value (a332 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h332

theorem calc333 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a327 x)) (.value (a320 x)) = .value (a333 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h333

theorem calc334 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a329 x)) (.value (19#64)) = .value (a334 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h334

theorem calc335 (x : Words) :
    Operation.lshr false (.value (a334 x)) (.value (51#64)) = .value (a335 x) := by
  simp (disch := decide) [a335, mlir_operation]

theorem calc336 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a335 x)) (.value (a330 x)) = .value (a336 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h336

theorem calc337 (x : Words) :
    Operation.lshr false (.value (a336 x)) (.value (51#64)) = .value (a337 x) := by
  simp (disch := decide) [a337, mlir_operation]

theorem calc338 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a337 x)) (.value (a331 x)) = .value (a338 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h338

theorem calc339 (x : Words) :
    Operation.lshr false (.value (a338 x)) (.value (51#64)) = .value (a339 x) := by
  simp (disch := decide) [a339, mlir_operation]

theorem calc340 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a339 x)) (.value (a332 x)) = .value (a340 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h340

theorem calc341 (x : Words) :
    Operation.lshr false (.value (a340 x)) (.value (51#64)) = .value (a341 x) := by
  simp (disch := decide) [a341, mlir_operation]

theorem calc342 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a341 x)) (.value (a333 x)) = .value (a342 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h342

theorem calc343 (x : Words) :
    Operation.lshr false (.value (a342 x)) (.value (51#64)) = .value (a343 x) := by
  simp (disch := decide) [a343, mlir_operation]

theorem calc344 (x : Words) :
    Operation.mul {nsw := true, nuw := true} (.value (a343 x)) (.value (19#64)) = .value (a344 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h344

theorem calc345 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a344 x)) (.value (a329 x)) = .value (a345 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h345

theorem calc346 (x : Words) :
    Operation.lshr false (.value (a345 x)) (.value (51#64)) = .value (a346 x) := by
  simp (disch := decide) [a346, mlir_operation]

theorem calc347 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a346 x)) (.value (a330 x)) = .value (a347 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h347

theorem calc348 (x : Words) :
    Operation.lshr false (.value (a347 x)) (.value (51#64)) = .value (a348 x) := by
  simp (disch := decide) [a348, mlir_operation]

theorem calc349 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a348 x)) (.value (a331 x)) = .value (a349 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h349

theorem calc350 (x : Words) :
    Operation.and (.value (a347 x)) (.value (2251799813685247#64)) = .value (a350 x) := by
  simp (disch := decide) [a350, mlir_operation]

theorem calc351 (x : Words) :
    Operation.lshr false (.value (a349 x)) (.value (51#64)) = .value (a351 x) := by
  simp (disch := decide) [a351, mlir_operation]

theorem calc352 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a351 x)) (.value (a332 x)) = .value (a352 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h352

theorem calc353 (x : Words) :
    Operation.and (.value (a349 x)) (.value (2251799813685247#64)) = .value (a353 x) := by
  simp (disch := decide) [a353, mlir_operation]

theorem calc354 (x : Words) :
    Operation.lshr false (.value (a352 x)) (.value (51#64)) = .value (a354 x) := by
  simp (disch := decide) [a354, mlir_operation]

theorem calc355 (x : Words) :
    Operation.add {nsw := true, nuw := true} (.value (a354 x)) (.value (a333 x)) = .value (a355 x) := by
  rcases arithmetic_operations x with ⟨h328, h329, h330, h331, h332, h333, h334, h336, h338, h340, h342, h344, h345, h347, h349, h352, h355⟩
  exact h355

theorem calc356 (x : Words) :
    Operation.and (.value (a352 x)) (.value (2251799813685247#64)) = .value (a356 x) := by
  simp (disch := decide) [a356, mlir_operation]

theorem calc357 (x : Words) :
    Operation.and (.value (a355 x)) (.value (2251799813685247#64)) = .value (a357 x) := by
  simp (disch := decide) [a357, mlir_operation]

def arithmeticEnv0 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%314 := .value (a314 x),
    %315 := .value (a315 x),
    %316 := .value (a316 x),
    %317 := .value (a317 x),
    %318 := .value (a318 x)]

theorem arithmetic_frame0 (E : Env program.Γ) (x : Words) :
    Frame E (arithmeticEnv0 E x) 314 := by
  unfold arithmeticEnv0
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem arithmetic_segment0 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e7 : E.read (%7) = .value (51#64))
    (e10 : E.read (%10) = .value (1#64))
    (e50 : E.read (%50) = .value (0#64))
    (e312 : E.read (%312) = .value (x 0))
    (e313 : E.read (%313) = Ty.wrap #v[x 1, x 2, x 3, x 4])
    : Cutpoint.segment (program p g) 0 421 5 E s =
      .value (arithmeticEnv0 E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 421).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, arithmeticEnv0,
    e7, e10, e50, e312, e313, calc314 x, calc315 x, calc316 x, calc317 x, calc318 x]

def arithmeticEnv1 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%319 := .value (a319 x),
    %320 := .value (a320 x),
    %321 := .value (a321 x),
    %322 := .value (a322 x),
    %323 := .value (a323 x)]

theorem arithmetic_frame1 (E : Env program.Γ) (x : Words) :
    Frame E (arithmeticEnv1 E x) 314 := by
  unfold arithmeticEnv1
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem arithmetic_segment1 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e7 : E.read (%7) = .value (51#64))
    (e8 : E.read (%8) = .value (2251799813685247#64))
    (e11 : E.read (%11) = .value (2#64))
    (e12 : E.read (%12) = .value (3#64))
    (e312 : E.read (%312) = .value (x 0))
    (e313 : E.read (%313) = Ty.wrap #v[x 1, x 2, x 3, x 4])
    : Cutpoint.segment (program p g) 0 426 5 E s =
      .value (arithmeticEnv1 E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 426).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, arithmeticEnv1,
    e7, e8, e11, e12, e312, e313, calc319 x, calc320 x, calc321 x, calc322 x, calc323 x]

def arithmeticEnv2 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%324 := .value (a324 x),
    %325 := .value (a325 x),
    %326 := .value (a326 x),
    %327 := .value (a327 x),
    %328 := .value (a328 x)]

theorem arithmetic_frame2 (E : Env program.Γ) (x : Words) :
    Frame E (arithmeticEnv2 E x) 314 := by
  unfold arithmeticEnv2
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem arithmetic_segment2 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e8 : E.read (%8) = .value (2251799813685247#64))
    (e9 : E.read (%9) = .value (19#64))
    (e315 : E.read (%315) = .value (a315 x))
    (e317 : E.read (%317) = .value (a317 x))
    (e319 : E.read (%319) = .value (a319 x))
    (e321 : E.read (%321) = .value (a321 x))
    (e322 : E.read (%322) = .value (a322 x))
    : Cutpoint.segment (program p g) 0 431 5 E s =
      .value (arithmeticEnv2 E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 431).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, arithmeticEnv2,
    e8, e9, e315, e317, e319, e321, e322, calc324 x, calc325 x, calc326 x, calc327 x, calc328 x]

def arithmeticEnv3 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%329 := .value (a329 x),
    %330 := .value (a330 x),
    %331 := .value (a331 x),
    %332 := .value (a332 x),
    %333 := .value (a333 x)]

theorem arithmetic_frame3 (E : Env program.Γ) (x : Words) :
    Frame E (arithmeticEnv3 E x) 314 := by
  unfold arithmeticEnv3
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem arithmetic_segment3 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e314 : E.read (%314) = .value (a314 x))
    (e316 : E.read (%316) = .value (a316 x))
    (e318 : E.read (%318) = .value (a318 x))
    (e320 : E.read (%320) = .value (a320 x))
    (e323 : E.read (%323) = .value (a323 x))
    (e324 : E.read (%324) = .value (a324 x))
    (e325 : E.read (%325) = .value (a325 x))
    (e326 : E.read (%326) = .value (a326 x))
    (e327 : E.read (%327) = .value (a327 x))
    (e328 : E.read (%328) = .value (a328 x))
    : Cutpoint.segment (program p g) 0 436 5 E s =
      .value (arithmeticEnv3 E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 436).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, arithmeticEnv3,
    e314, e316, e318, e320, e323, e324, e325, e326, e327, e328, calc329 x, calc330 x, calc331 x, calc332 x, calc333 x]

def arithmeticEnv4 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%334 := .value (a334 x),
    %335 := .value (a335 x),
    %336 := .value (a336 x),
    %337 := .value (a337 x),
    %338 := .value (a338 x)]

theorem arithmetic_frame4 (E : Env program.Γ) (x : Words) :
    Frame E (arithmeticEnv4 E x) 314 := by
  unfold arithmeticEnv4
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem arithmetic_segment4 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e7 : E.read (%7) = .value (51#64))
    (e9 : E.read (%9) = .value (19#64))
    (e329 : E.read (%329) = .value (a329 x))
    (e330 : E.read (%330) = .value (a330 x))
    (e331 : E.read (%331) = .value (a331 x))
    : Cutpoint.segment (program p g) 0 441 5 E s =
      .value (arithmeticEnv4 E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 441).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, arithmeticEnv4,
    e7, e9, e329, e330, e331, calc334 x, calc335 x, calc336 x, calc337 x, calc338 x]

def arithmeticEnv5 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%339 := .value (a339 x),
    %340 := .value (a340 x),
    %341 := .value (a341 x),
    %342 := .value (a342 x),
    %343 := .value (a343 x)]

theorem arithmetic_frame5 (E : Env program.Γ) (x : Words) :
    Frame E (arithmeticEnv5 E x) 314 := by
  unfold arithmeticEnv5
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem arithmetic_segment5 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e7 : E.read (%7) = .value (51#64))
    (e332 : E.read (%332) = .value (a332 x))
    (e333 : E.read (%333) = .value (a333 x))
    (e338 : E.read (%338) = .value (a338 x))
    : Cutpoint.segment (program p g) 0 446 5 E s =
      .value (arithmeticEnv5 E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 446).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, arithmeticEnv5,
    e7, e332, e333, e338, calc339 x, calc340 x, calc341 x, calc342 x, calc343 x]

def arithmeticEnv6 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%344 := .value (a344 x),
    %345 := .value (a345 x),
    %346 := .value (a346 x),
    %347 := .value (a347 x),
    %348 := .value (a348 x)]

theorem arithmetic_frame6 (E : Env program.Γ) (x : Words) :
    Frame E (arithmeticEnv6 E x) 314 := by
  unfold arithmeticEnv6
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem arithmetic_segment6 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e7 : E.read (%7) = .value (51#64))
    (e9 : E.read (%9) = .value (19#64))
    (e329 : E.read (%329) = .value (a329 x))
    (e330 : E.read (%330) = .value (a330 x))
    (e343 : E.read (%343) = .value (a343 x))
    : Cutpoint.segment (program p g) 0 451 5 E s =
      .value (arithmeticEnv6 E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 451).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, arithmeticEnv6,
    e7, e9, e329, e330, e343, calc344 x, calc345 x, calc346 x, calc347 x, calc348 x]

def arithmeticEnv7 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%349 := .value (a349 x),
    %350 := .value (a350 x),
    %351 := .value (a351 x),
    %352 := .value (a352 x),
    %353 := .value (a353 x)]

theorem arithmetic_frame7 (E : Env program.Γ) (x : Words) :
    Frame E (arithmeticEnv7 E x) 314 := by
  unfold arithmeticEnv7
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem arithmetic_segment7 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e7 : E.read (%7) = .value (51#64))
    (e8 : E.read (%8) = .value (2251799813685247#64))
    (e331 : E.read (%331) = .value (a331 x))
    (e332 : E.read (%332) = .value (a332 x))
    (e347 : E.read (%347) = .value (a347 x))
    (e348 : E.read (%348) = .value (a348 x))
    : Cutpoint.segment (program p g) 0 456 5 E s =
      .value (arithmeticEnv7 E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 456).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, arithmeticEnv7,
    e7, e8, e331, e332, e347, e348, calc349 x, calc350 x, calc351 x, calc352 x, calc353 x]

def arithmeticEnv8 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%354 := .value (a354 x),
    %355 := .value (a355 x),
    %356 := .value (a356 x),
    %357 := .value (a357 x)]

theorem arithmetic_frame8 (E : Env program.Γ) (x : Words) :
    Frame E (arithmeticEnv8 E x) 314 := by
  unfold arithmeticEnv8
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem arithmetic_segment8 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (x : Words)
    (e7 : E.read (%7) = .value (51#64))
    (e8 : E.read (%8) = .value (2251799813685247#64))
    (e333 : E.read (%333) = .value (a333 x))
    (e352 : E.read (%352) = .value (a352 x))
    : Cutpoint.segment (program p g) 0 461 4 E s =
      .value (arithmeticEnv8 E x, s) := by
  change List.foldlM Instr.run E (((program.entry p g).body.drop 461).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := decide) only [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, arithmeticEnv8,
    e7, e8, e333, e352, calc354 x, calc355 x, calc356 x, calc357 x]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
