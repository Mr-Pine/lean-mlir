import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2Constructor
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Spec.Field

/-! The serial-to-SIMD packing interval of the exact imported constructor.
The instruction-slice theorem retains poison and every emitted operation.
The arithmetic statements explain the physical lane order and preserve the
integer field value under the constructor's ordinary radix-51 input bound.
-/
namespace Agave.Ed25519.Tables.Avx2Constructor.Packing
open LeanMLIR.RIR
open Avx2PointAdd.CFG (runSlice)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev SerialPoint := Fin 4 → Field.Serial
abbrev Blocks := Fin 5 → Vector (BitVec 32) 8

def lowWord (x : BitVec 64) : BitVec 32 := x.setWidth 32 &&& 67108863#32
def highWord (x : BitVec 64) : BitVec 32 := (x >>> 26).setWidth 32

def pack (a : SerialPoint) : Blocks := fun k =>
  #v[lowWord (a 0 k), lowWord (a 1 k), highWord (a 0 k), highWord (a 1 k),
    lowWord (a 2 k), lowWord (a 3 k), highWord (a 2 k), highWord (a 3 k)]

def input (E : ⟪kernel.Γ⟫) (a : SerialPoint) : ⟪kernel.Γ⟫ :=
  E[%20 := Ty.poisoned (.vec 4 32),
    %21 := .value 0#64, %22 := .value 1#64,
    %23 := .value 2#64, %24 := .value 3#64,
    %25 := Vector.replicate 4 (.value 67108863#32),
    %26 := Ty.poisoned (.vec 4 64),
    %27 := Vector.replicate 4 (.value 26#64),
    %361 := .value (a 0 0),
    %363 := .value (a 0 1),
    %365 := .value (a 0 2),
    %367 := .value (a 0 3),
    %369 := .value (a 0 4),
    %371 := .value (a 1 0),
    %373 := .value (a 1 1),
    %375 := .value (a 1 2),
    %377 := .value (a 1 3),
    %379 := .value (a 1 4),
    %381 := .value (a 2 0),
    %383 := .value (a 2 1),
    %385 := .value (a 2 2),
    %387 := .value (a 2 3),
    %389 := .value (a 2 4),
    %391 := .value (a 3 0),
    %393 := .value (a 3 1),
    %395 := .value (a 3 2),
    %397 := .value (a 3 3),
    %399 := .value (a 3 4)]

def result (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  let v400 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%391))
  let v401 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%381))
  let v402 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%371))
  let v403 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%361))
  let v404 : ⟦Ty.vec 4 32⟧ := Operation.insertelement (E.read (%20)) v403 (E.read (%21))
  let v405 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v404 v402 (E.read (%22))
  let v406 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v405 v401 (E.read (%23))
  let v407 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v406 v400 (E.read (%24))
  let v408 : ⟦Ty.vec 4 32⟧ := Vector.zipWith (Operation.and) v407 (E.read (%25))
  let v409 : ⟦Ty.vec 4 64⟧ := Operation.insertelement (E.read (%26)) (E.read (%361)) (E.read (%21))
  let v410 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v409 (E.read (%371)) (E.read (%22))
  let v411 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v410 (E.read (%381)) (E.read (%23))
  let v412 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v411 (E.read (%391)) (E.read (%24))
  let v413 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v412 (E.read (%27))
  let v414 : ⟦Ty.vec 4 32⟧ := Vector.ofFn (fun i => Operation.trunc {} v413[i])
  let v415 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 4, some 5, some 2, some 3, some 6, some 7] v408 v414
  let v416 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%393))
  let v417 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%383))
  let v418 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%373))
  let v419 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%363))
  let v420 : ⟦Ty.vec 4 32⟧ := Operation.insertelement (E.read (%20)) v419 (E.read (%21))
  let v421 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v420 v418 (E.read (%22))
  let v422 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v421 v417 (E.read (%23))
  let v423 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v422 v416 (E.read (%24))
  let v424 : ⟦Ty.vec 4 32⟧ := Vector.zipWith (Operation.and) v423 (E.read (%25))
  let v425 : ⟦Ty.vec 4 64⟧ := Operation.insertelement (E.read (%26)) (E.read (%363)) (E.read (%21))
  let v426 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v425 (E.read (%373)) (E.read (%22))
  let v427 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v426 (E.read (%383)) (E.read (%23))
  let v428 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v427 (E.read (%393)) (E.read (%24))
  let v429 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v428 (E.read (%27))
  let v430 : ⟦Ty.vec 4 32⟧ := Vector.ofFn (fun i => Operation.trunc {} v429[i])
  let v431 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 4, some 5, some 2, some 3, some 6, some 7] v424 v430
  let v432 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%395))
  let v433 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%385))
  let v434 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%375))
  let v435 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%365))
  let v436 : ⟦Ty.vec 4 32⟧ := Operation.insertelement (E.read (%20)) v435 (E.read (%21))
  let v437 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v436 v434 (E.read (%22))
  let v438 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v437 v433 (E.read (%23))
  let v439 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v438 v432 (E.read (%24))
  let v440 : ⟦Ty.vec 4 32⟧ := Vector.zipWith (Operation.and) v439 (E.read (%25))
  let v441 : ⟦Ty.vec 4 64⟧ := Operation.insertelement (E.read (%26)) (E.read (%365)) (E.read (%21))
  let v442 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v441 (E.read (%375)) (E.read (%22))
  let v443 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v442 (E.read (%385)) (E.read (%23))
  let v444 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v443 (E.read (%395)) (E.read (%24))
  let v445 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v444 (E.read (%27))
  let v446 : ⟦Ty.vec 4 32⟧ := Vector.ofFn (fun i => Operation.trunc {} v445[i])
  let v447 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 4, some 5, some 2, some 3, some 6, some 7] v440 v446
  let v448 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%397))
  let v449 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%387))
  let v450 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%377))
  let v451 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%367))
  let v452 : ⟦Ty.vec 4 32⟧ := Operation.insertelement (E.read (%20)) v451 (E.read (%21))
  let v453 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v452 v450 (E.read (%22))
  let v454 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v453 v449 (E.read (%23))
  let v455 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v454 v448 (E.read (%24))
  let v456 : ⟦Ty.vec 4 32⟧ := Vector.zipWith (Operation.and) v455 (E.read (%25))
  let v457 : ⟦Ty.vec 4 64⟧ := Operation.insertelement (E.read (%26)) (E.read (%367)) (E.read (%21))
  let v458 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v457 (E.read (%377)) (E.read (%22))
  let v459 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v458 (E.read (%387)) (E.read (%23))
  let v460 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v459 (E.read (%397)) (E.read (%24))
  let v461 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v460 (E.read (%27))
  let v462 : ⟦Ty.vec 4 32⟧ := Vector.ofFn (fun i => Operation.trunc {} v461[i])
  let v463 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 4, some 5, some 2, some 3, some 6, some 7] v456 v462
  let v464 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%399))
  let v465 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%389))
  let v466 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%379))
  let v467 : PoisonOr (BitVec 32) := Operation.trunc {} (E.read (%369))
  let v468 : ⟦Ty.vec 4 32⟧ := Operation.insertelement (E.read (%20)) v467 (E.read (%21))
  let v469 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v468 v466 (E.read (%22))
  let v470 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v469 v465 (E.read (%23))
  let v471 : ⟦Ty.vec 4 32⟧ := Operation.insertelement v470 v464 (E.read (%24))
  let v472 : ⟦Ty.vec 4 32⟧ := Vector.zipWith (Operation.and) v471 (E.read (%25))
  let v473 : ⟦Ty.vec 4 64⟧ := Operation.insertelement (E.read (%26)) (E.read (%369)) (E.read (%21))
  let v474 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v473 (E.read (%379)) (E.read (%22))
  let v475 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v474 (E.read (%389)) (E.read (%23))
  let v476 : ⟦Ty.vec 4 64⟧ := Operation.insertelement v475 (E.read (%399)) (E.read (%24))
  let v477 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v476 (E.read (%27))
  let v478 : ⟦Ty.vec 4 32⟧ := Vector.ofFn (fun i => Operation.trunc {} v477[i])
  let v479 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 4, some 5, some 2, some 3, some 6, some 7] v472 v478
  E[%400 := v400,
    %401 := v401,
    %402 := v402,
    %403 := v403,
    %404 := v404,
    %405 := v405,
    %406 := v406,
    %407 := v407,
    %408 := v408,
    %409 := v409,
    %410 := v410,
    %411 := v411,
    %412 := v412,
    %413 := v413,
    %414 := v414,
    %415 := v415,
    %416 := v416,
    %417 := v417,
    %418 := v418,
    %419 := v419,
    %420 := v420,
    %421 := v421,
    %422 := v422,
    %423 := v423,
    %424 := v424,
    %425 := v425,
    %426 := v426,
    %427 := v427,
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
    %446 := v446,
    %447 := v447,
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
    %479 := v479]

/-- The original constructor's eighty packing instructions, without changing
any instruction or relying on arithmetic helper behavior. -/
theorem run_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb0 p) E 400 80 s = .value (result E, s) := by
  simp [runSlice, kernel.bb0, result, List.foldlM_cons, List.foldlM_nil,
    Instr.run, UnOp.compute, BinOp.compute, TernOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env]

def reads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%415), E.read (%431), E.read (%447), E.read (%463), E.read (%479)]

/-- All initially poisoned lanes are overwritten before the final shuffle. -/
theorem reads_result (E : ⟪kernel.Γ⟫) (a : SerialPoint) (k : Fin 5) :
    reads (result (input E a)) k = Ty.wrap (pack a k) := by
  fin_cases k <;> simp [reads, result, input, pack, lowWord, highWord,
    Operation.insertelement, Operation.trunc, Operation.lshr, Operation.and,
    Ty.poisoned, Ty.wrap, mlir_env, mlir_operation]

end Agave.Ed25519.Tables.Avx2Constructor.Packing
