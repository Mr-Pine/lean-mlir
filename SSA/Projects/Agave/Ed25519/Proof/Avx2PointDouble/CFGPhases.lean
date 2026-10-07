import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.MixingPacking
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame
import SSA.Projects.RIR.Run.Memory

/-! Exact instruction intervals of the unchanged imported bb18. These source
proofs expose every write and keep helper bodies behind their proved local
contracts. The C/LLVM extraction and this generator are not trusted axioms. -/
namespace Agave.Ed25519.Avx2PointDouble.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
open Avx2PointAdd.Phases (packed_unflatten)
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

structure Constants (E : ⟪avx2Kernel.Γ⟫) : Prop where
  poison : E.read (%26) = Ty.poisoned (.vec 8 32)
  one : E.read (%27) = Ty.wrap (#v[1, 1, 1, 1, 1, 1, 1, 1] : Vec32)
  «prefix» : E.read (%45) = zeroPrefix
  difference : E.read (%62) = zeroDifference
  lazy0 : E.read (%81) = lazyConstants 134217690#32 67108862#32
  lazyN : E.read (%99) = lazyConstants 134217726#32 67108862#32
  sum : E.read (%116) = zeroSum

structure Pointers (E : ⟪avx2Kernel.Γ⟫) (prepared square result : Pointer) : Prop where
  r256 : E.read (%256) = .value (prepared)
  r327 : E.read (%327) = .value (prepared.add 32#64)
  r328 : E.read (%328) = .value (prepared.add 64#64)
  r329 : E.read (%329) = .value (prepared.add 96#64)
  r330 : E.read (%330) = .value (prepared.add 128#64)
  r255 : E.read (%255) = .value (square)
  r331 : E.read (%331) = .value (square.add 32#64)
  r332 : E.read (%332) = .value (square.add 64#64)
  r333 : E.read (%333) = .value (square.add 96#64)
  r334 : E.read (%334) = .value (square.add 128#64)
  r263 : E.read (%263) = .value (result)
  r335 : E.read (%335) = .value (result.add 32#64)
  r336 : E.read (%336) = .value (result.add 64#64)
  r337 : E.read (%337) = .value (result.add 96#64)
  r338 : E.read (%338) = .value (result.add 128#64)

def inputReads (E : ⟪avx2Kernel.Γ⟫) (a : Blocks) : Prop :=
  E.read (%424) = Ty.wrap (a 0) ∧
  E.read (%423) = Ty.wrap (a 1) ∧
  E.read (%422) = Ty.wrap (a 2) ∧
  E.read (%421) = Ty.wrap (a 3) ∧
  E.read (%425) = Ty.wrap (a 4)

def prepareEnv (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v427 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%424)) (E.read (%26))
  let v428 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%423)) (E.read (%26))
  let v429 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%422)) (E.read (%26))
  let v430 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%421)) (E.read (%26))
  let v431 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%425)) (E.read (%26))
  let v432 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%424)) (E.read (%26))
  let v433 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%423)) (E.read (%26))
  let v434 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%422)) (E.read (%26))
  let v435 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%421)) (E.read (%26))
  let v436 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%425)) (E.read (%26))
  let v437 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v432 v427
  let v438 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v433 v428
  let v439 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v434 v429
  let v440 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v435 v430
  let v441 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v436 v431
  let v442 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%424)) v437
  let v443 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%423)) v438
  let v444 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%422)) v439
  let v445 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%421)) v440
  let v446 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%425)) v441
  E[%427 := v427,
    %428 := v428,
    %429 := v429,
    %430 := v430,
    %431 := v431,
    %432 := v432,
    %433 := v433,
    %434 := v434,
    %435 := v435,
    %436 := v436,
    %437 := v437,
    %438 := v438,
    %439 := v439,
    %440 := v440,
    %441 := v441,
    %442 := v442,
    %443 := v443,
    %444 := v444,
    %445 := v445,
    %446 := v446]

theorem prepare_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 427 avx2Kernel.Γ.n E (prepareEnv E) := by
  unfold prepareEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem prepare_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb18 p) E 0 23 s = .value (prepareEnv E, s) := by
  simp [runSlice, avx2Kernel.bb18, prepareEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env]

def preparedReads (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%442), E.read (%443), E.read (%444), E.read (%445), E.read (%446)]

theorem prepare_field (E : ⟪avx2Kernel.Γ⟫) (a : Blocks)
    (hc : Constants E) (ha : inputReads E a) (k : Fin 5) :
    preparedReads (prepareEnv E) k = Ty.wrap (prepareBlocks a k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  have hnetwork : preparedReads (prepareEnv E) k = prepareOperation (Ty.wrap (a k)) := by
    fin_cases k <;> simp [preparedReads, prepareEnv, prepareOperation, maskA, maskB,
      maskBlend, hc.poison, h0, h1, h2, h3, h4, mlir_env]
  exact hnetwork.trans (prepareOperation_value (a k))

def mixEnv (E : ⟪avx2Kernel.Γ⟫) (v : Blocks) : ⟪avx2Kernel.Γ⟫ :=
  let v447 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 0)
  let v448 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 1)
  let v449 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 2)
  let v450 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 3)
  let v451 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v447 (E.read (%26))
  let v452 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v448 (E.read (%26))
  let v453 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v449 (E.read (%26))
  let v454 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v450 (E.read (%26))
  let v455 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 4)
  let v456 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v455 (E.read (%26))
  let v457 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v447 (E.read (%26))
  let v458 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v448 (E.read (%26))
  let v459 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v449 (E.read (%26))
  let v460 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v450 (E.read (%26))
  let v461 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v455 (E.read (%26))
  let v462 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v447 (E.read (%27))
  let v463 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v448 (E.read (%27))
  let v464 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v449 (E.read (%27))
  let v465 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v450 (E.read (%27))
  let v466 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v455 (E.read (%27))
  let v467 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%45)) v462
  let v468 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%45)) v463
  let v469 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%45)) v464
  let v470 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%45)) v465
  let v471 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%45)) v466
  let v472 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v467 v447
  let v473 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v468 v448
  let v474 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v469 v449
  let v475 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v470 v450
  let v476 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v471 v455
  let v477 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v457 (E.read (%62))
  let v478 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v458 (E.read (%62))
  let v479 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v459 (E.read (%62))
  let v480 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v460 (E.read (%62))
  let v481 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v461 (E.read (%62))
  let v482 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%81)) v457
  let v483 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%99)) v458
  let v484 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%99)) v459
  let v485 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%99)) v460
  let v486 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%99)) v461
  let v487 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%116)) v482
  let v488 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%116)) v483
  let v489 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%116)) v484
  let v490 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%116)) v485
  let v491 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%116)) v486
  let v492 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v477 v451
  let v493 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v492 v472
  let v494 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v493 v487
  let v495 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v478 v452
  let v496 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v495 v473
  let v497 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v496 v488
  let v498 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v479 v453
  let v499 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v498 v474
  let v500 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v499 v489
  let v501 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v480 v454
  let v502 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v501 v475
  let v503 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v502 v490
  let v504 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v481 v456
  let v505 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v504 v476
  let v506 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v505 v491
  let v507 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v494 (E.read (%26))
  let v508 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v497 (E.read (%26))
  let v509 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v500 (E.read (%26))
  let v510 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v503 (E.read (%26))
  let v511 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v506 (E.read (%26))
  E[%447 := v447,
    %448 := v448,
    %449 := v449,
    %450 := v450,
    %451 := v451,
    %452 := v452,
    %453 := v453,
    %454 := v454,
    %455 := v455,
    %456 := v456,
    %457 := v457,
    %458 := v458,
    %459 := v459,
    %460 := v460,
    %461 := v461,
    %462 := v462,
    %463 := v463,
    %464 := v464,
    %465 := v465,
    %466 := v466,
    %467 := v467,
    %468 := v468,
    %469 := v469,
    %470 := v470,
    %471 := v471,
    %472 := v472,
    %473 := v473,
    %474 := v474,
    %475 := v475,
    %476 := v476,
    %477 := v477,
    %478 := v478,
    %479 := v479,
    %480 := v480,
    %481 := v481,
    %482 := v482,
    %483 := v483,
    %484 := v484,
    %485 := v485,
    %486 := v486,
    %487 := v487,
    %488 := v488,
    %489 := v489,
    %490 := v490,
    %491 := v491,
    %492 := v492,
    %493 := v493,
    %494 := v494,
    %495 := v495,
    %496 := v496,
    %497 := v497,
    %498 := v498,
    %499 := v499,
    %500 := v500,
    %501 := v501,
    %502 := v502,
    %503 := v503,
    %504 := v504,
    %505 := v505,
    %506 := v506,
    %507 := v507,
    %508 := v508,
    %509 := v509,
    %510 := v510,
    %511 := v511]

theorem mix_frame (E : ⟪avx2Kernel.Γ⟫) (v : Blocks) :
    RegisterFrame 427 avx2Kernel.Γ.n E (mixEnv E v) := by
  unfold mixEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem mix_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks)
    (hr : SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%255) = .value r)
    (hp1 : E.read (%331) = .value (r.add 32#64))
    (hp2 : E.read (%332) = .value (r.add 64#64))
    (hp3 : E.read (%333) = .value (r.add 96#64))
    (hp4 : E.read (%334) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb18 p) E 29 65 s = .value (mixEnv E v, s) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hv0 := packed_unflatten s.mem r v hv 0
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 0#64) 256) = Ty.wrap (v 0) at hv0
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hv1 := packed_unflatten s.mem r v hv 1
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 32#64) 256) = Ty.wrap (v 1) at hv1
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv1
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hv2 := packed_unflatten s.mem r v hv 2
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 64#64) 256) = Ty.wrap (v 2) at hv2
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv2
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hv3 := packed_unflatten s.mem r v hv 3
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 96#64) 256) = Ty.wrap (v 3) at hv3
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv3
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv4 := packed_unflatten s.mem r v hv 4
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) = Ty.wrap (v 4) at hv4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv4
  simp only [Pointer.add_zero] at hf0 hv0
  simp (config := {maxSteps := 500000}) [runSlice, avx2Kernel.bb18, mixEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.load, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hf0, hv0, hp1, hf1, hv1,
    hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4, -reduceShufflevector]

def mixedReads (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%494), E.read (%497), E.read (%500), E.read (%503), E.read (%506)]
def rightReads (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%507), E.read (%508), E.read (%509), E.read (%510), E.read (%511)]

theorem mix_network (E : ⟪avx2Kernel.Γ⟫) (v : Blocks)
    (hc : Constants E) (k : Fin 5) :
    mixedReads (mixEnv E v) k = mixOperation (Ty.wrap (v k))
      (Avx2PointAdd.Phases.evenConstant k) (Avx2PointAdd.Phases.oddConstant k) := by
  fin_cases k <;> simp [mixedReads, mixEnv, mixOperation, hc.poison, hc.one,
    hc.prefix, hc.difference, hc.lazy0, hc.lazyN, hc.sum,
    Avx2PointAdd.Phases.evenConstant, Avx2PointAdd.Phases.oddConstant,
    Avx2PointAdd.Phases.evenIndex, Avx2PointAdd.Phases.oddIndex,
    Avx2PointAdd.twiceP, Avx2PointAdd.word, mlir_env]

theorem mix_field (E : ⟪avx2Kernel.Γ⟫) (q : Coordinates)
    (hc : Constants E) (hq : PointBound q) (k : Fin 5) :
    mixedReads (mixEnv E (packCoordinates q)) k = Ty.wrap (packCoordinates (mix q) k) := by
  rw [mix_network E _ hc k, mixOperation_value, mixBlock_packed hq]

theorem right_field (E : ⟪avx2Kernel.Γ⟫) (q : Coordinates)
    (hc : Constants E) (hq : PointBound q) (k : Fin 5) :
    rightReads (mixEnv E (packCoordinates q)) k = Ty.wrap (packCoordinates (right q) k) := by
  have h : rightReads (mixEnv E (packCoordinates q)) k =
      Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7]
        (mixedReads (mixEnv E (packCoordinates q)) k) (Ty.poisoned (.vec 8 32)) := by
    fin_cases k <;> simp [rightReads, mixedReads, mixEnv, hc.poison, mlir_env]
  rw [h, mix_field E q hc hq k, rightBlock_shuffle, rightBlock_packed]

def leftEnv (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v512 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%494)) (E.read (%26))
  let v513 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%497)) (E.read (%26))
  let v514 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%500)) (E.read (%26))
  let v515 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%503)) (E.read (%26))
  let v516 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%506)) (E.read (%26))
  E[%512 := v512,
    %513 := v513,
    %514 := v514,
    %515 := v515,
    %516 := v516]

theorem left_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 427 avx2Kernel.Γ.n E (leftEnv E) := by
  unfold leftEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem left_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb18 p) E 99 5 s = .value (leftEnv E, s) := by
  simp [runSlice, avx2Kernel.bb18, leftEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env]

def leftReads (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%512), E.read (%513), E.read (%514), E.read (%515), E.read (%516)]

theorem left_field (E : ⟪avx2Kernel.Γ⟫) (q : Coordinates)
    (hc : Constants E) (hq : PointBound q) (k : Fin 5) :
    leftReads (leftEnv (mixEnv E (packCoordinates q))) k = Ty.wrap (packCoordinates (left q) k) := by
  have h : leftReads (leftEnv (mixEnv E (packCoordinates q))) k =
      Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2]
        (mixedReads (mixEnv E (packCoordinates q)) k) (Ty.poisoned (.vec 8 32)) := by
    fin_cases k <;> simp [leftReads, leftEnv, mixedReads, mixEnv, hc.poison, mlir_env]
  rw [h, mix_field E q hc hq k, leftBlock_shuffle, leftBlock_packed]

theorem prepared_stores (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks) (hr : SmallRange s.mem r 160)
    (hp0 : E.read (%256) = .value r)
    (hv0 : E.read (%442) = Ty.wrap (v 0))
    (hp1 : E.read (%327) = .value (r.add 32#64))
    (hv1 : E.read (%443) = Ty.wrap (v 1))
    (hp2 : E.read (%328) = .value (r.add 64#64))
    (hv2 : E.read (%444) = Ty.wrap (v 2))
    (hp3 : E.read (%329) = .value (r.add 96#64))
    (hv3 : E.read (%445) = Ty.wrap (v 3))
    (hp4 : E.read (%330) = .value (r.add 128#64))
    (hv4 : E.read (%446) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb18 p) E 23 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb18, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem right_stores (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks) (hr : SmallRange s.mem r 160)
    (hp0 : E.read (%255) = .value r)
    (hv0 : E.read (%507) = Ty.wrap (v 0))
    (hp1 : E.read (%331) = .value (r.add 32#64))
    (hv1 : E.read (%508) = Ty.wrap (v 1))
    (hp2 : E.read (%332) = .value (r.add 64#64))
    (hv2 : E.read (%509) = Ty.wrap (v 2))
    (hp3 : E.read (%333) = .value (r.add 96#64))
    (hv3 : E.read (%510) = Ty.wrap (v 3))
    (hp4 : E.read (%334) = .value (r.add 128#64))
    (hv4 : E.read (%511) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb18 p) E 94 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb18, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem left_stores (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks) (hr : SmallRange s.mem r 160)
    (hp0 : E.read (%256) = .value r)
    (hv0 : E.read (%512) = Ty.wrap (v 0))
    (hp1 : E.read (%327) = .value (r.add 32#64))
    (hv1 : E.read (%513) = Ty.wrap (v 1))
    (hp2 : E.read (%328) = .value (r.add 64#64))
    (hv2 : E.read (%514) = Ty.wrap (v 2))
    (hp3 : E.read (%329) = .value (r.add 96#64))
    (hv3 : E.read (%515) = Ty.wrap (v 3))
    (hp4 : E.read (%330) = .value (r.add 128#64))
    (hv4 : E.read (%516) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb18 p) E 104 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb18, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

def loadResultEnv (E : ⟪avx2Kernel.Γ⟫) (v : Blocks) : ⟪avx2Kernel.Γ⟫ :=
  let v517 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 0)
  let v518 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 1)
  let v519 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 2)
  let v520 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 3)
  let v521 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 4)
  E[%517 := v517,
    %518 := v518,
    %519 := v519,
    %520 := v520,
    %521 := v521]

theorem loadResult_frame (E : ⟪avx2Kernel.Γ⟫) (v : Blocks) :
    RegisterFrame 427 avx2Kernel.Γ.n E (loadResultEnv E v) := by
  unfold loadResultEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem loadResult_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks) (hr : SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%263) = .value r)
    (hp1 : E.read (%335) = .value (r.add 32#64))
    (hp2 : E.read (%336) = .value (r.add 64#64))
    (hp3 : E.read (%337) = .value (r.add 96#64))
    (hp4 : E.read (%338) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb18 p) E 110 8 s = .value (loadResultEnv E v, s) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hv0 := packed_unflatten s.mem r v hv 0
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 0#64) 256) = Ty.wrap (v 0) at hv0
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hv1 := packed_unflatten s.mem r v hv 1
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 32#64) 256) = Ty.wrap (v 1) at hv1
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv1
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hv2 := packed_unflatten s.mem r v hv 2
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 64#64) 256) = Ty.wrap (v 2) at hv2
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv2
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hv3 := packed_unflatten s.mem r v hv 3
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 96#64) 256) = Ty.wrap (v 3) at hv3
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv3
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv4 := packed_unflatten s.mem r v hv 4
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) = Ty.wrap (v 4) at hv4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv4
  simp only [Pointer.add_zero] at hf0 hv0
  simp [runSlice, avx2Kernel.bb18, loadResultEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Operation.load, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hf0, hv0, hp1, hf1, hv1,
    hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4]

end Agave.Ed25519.Avx2PointDouble.CFG
