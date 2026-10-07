import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceAlignment5

namespace Firedancer.Common.ScalarArithmetic.Registers
open InstCombine (LLVM)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem op_447 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 447) digest a b = LLVM.shl a b { nsw := false, nuw := false } := rfl

theorem align_447 (digest : BitVec 512) :
    (source_stage_expr 447) digest = r447 digest :=
  source_stage_congruence 447 digest

theorem op_448 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 448) digest a b = LLVM.and a b := rfl

theorem align_448 (digest : BitVec 512) :
    (source_stage_expr 448) digest = r448 digest :=
  source_stage_congruence 448 digest

theorem op_449 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 449) digest a b = LLVM.or a b := rfl

theorem align_449 (digest : BitVec 512) :
    (source_stage_expr 449) digest = r449 digest :=
  source_stage_congruence 449 digest

theorem op_450 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 450) digest a b = LLVM.shl a b { nsw := false, nuw := false } := rfl

theorem align_450 (digest : BitVec 512) :
    (source_stage_expr 450) digest = r450 digest :=
  source_stage_congruence 450 digest

theorem op_451 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 451) digest a b = LLVM.and a b := rfl

theorem align_451 (digest : BitVec 512) :
    (source_stage_expr 451) digest = r451 digest :=
  source_stage_congruence 451 digest

theorem op_452 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 452) digest a b = LLVM.or a b := rfl

theorem align_452 (digest : BitVec 512) :
    (source_stage_expr 452) digest = r452 digest :=
  source_stage_congruence 452 digest

theorem op_453 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 453) digest a b = LLVM.shl a b { nsw := false, nuw := false } := rfl

theorem align_453 (digest : BitVec 512) :
    (source_stage_expr 453) digest = r453 digest :=
  source_stage_congruence 453 digest

theorem op_454 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 454) digest a b = LLVM.or a b := rfl

theorem align_454 (digest : BitVec 512) :
    (source_stage_expr 454) digest = r454 digest :=
  source_stage_congruence 454 digest

theorem op_455 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 455) digest a b = LLVM.lshr a b := rfl

theorem align_455 (digest : BitVec 512) :
    (source_stage_expr 455) digest = r455 digest :=
  source_stage_congruence 455 digest

theorem op_456 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 456) digest a b = LLVM.and a b := rfl

theorem align_456 (digest : BitVec 512) :
    (source_stage_expr 456) digest = r456 digest :=
  source_stage_congruence 456 digest

theorem op_457 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 457) digest a b = LLVM.shl a b { nsw := false, nuw := false } := rfl

theorem align_457 (digest : BitVec 512) :
    (source_stage_expr 457) digest = r457 digest :=
  source_stage_congruence 457 digest

theorem op_458 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 458) digest a b = LLVM.and a b := rfl

theorem align_458 (digest : BitVec 512) :
    (source_stage_expr 458) digest = r458 digest :=
  source_stage_congruence 458 digest

theorem op_459 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 459) digest a b = LLVM.or a b := rfl

theorem align_459 (digest : BitVec 512) :
    (source_stage_expr 459) digest = r459 digest :=
  source_stage_congruence 459 digest

theorem op_460 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 460) digest a b = LLVM.shl a b { nsw := false, nuw := false } := rfl

theorem align_460 (digest : BitVec 512) :
    (source_stage_expr 460) digest = r460 digest :=
  source_stage_congruence 460 digest

theorem op_461 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 461) digest a b = LLVM.and a b := rfl

theorem align_461 (digest : BitVec 512) :
    (source_stage_expr 461) digest = r461 digest :=
  source_stage_congruence 461 digest

theorem op_462 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 462) digest a b = LLVM.or a b := rfl

theorem align_462 (digest : BitVec 512) :
    (source_stage_expr 462) digest = r462 digest :=
  source_stage_congruence 462 digest

theorem op_463 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 463) digest a b = LLVM.shl a b { nsw := false, nuw := false } := rfl

theorem align_463 (digest : BitVec 512) :
    (source_stage_expr 463) digest = r463 digest :=
  source_stage_congruence 463 digest

theorem op_464 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 464) digest a b = LLVM.or a b := rfl

theorem align_464 (digest : BitVec 512) :
    (source_stage_expr 464) digest = r464 digest :=
  source_stage_congruence 464 digest

theorem op_466 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 466) digest a b = LLVM.lshr a b := rfl

theorem align_466 (digest : BitVec 512) :
    (source_stage_expr 466) digest = r466 digest :=
  source_stage_congruence 466 digest

theorem op_467 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 467) digest a b = LLVM.and a b := rfl

theorem align_467 (digest : BitVec 512) :
    (source_stage_expr 467) digest = r467 digest :=
  source_stage_congruence 467 digest

theorem op_468 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 468) digest a b = LLVM.shl a b { nsw := true, nuw := false } := rfl

theorem align_468 (digest : BitVec 512) :
    (source_stage_expr 468) digest = r468 digest :=
  source_stage_congruence 468 digest

theorem op_469 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 469) digest a b = LLVM.and a b := rfl

theorem align_469 (digest : BitVec 512) :
    (source_stage_expr 469) digest = r469 digest :=
  source_stage_congruence 469 digest

theorem op_470 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 470) digest a b = LLVM.or a b := rfl

theorem align_470 (digest : BitVec 512) :
    (source_stage_expr 470) digest = r470 digest :=
  source_stage_congruence 470 digest

theorem op_471 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 471) digest a b = LLVM.shl a b { nsw := true, nuw := false } := rfl

theorem align_471 (digest : BitVec 512) :
    (source_stage_expr 471) digest = r471 digest :=
  source_stage_congruence 471 digest

theorem op_472 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 472) digest a b = LLVM.and a b := rfl

theorem align_472 (digest : BitVec 512) :
    (source_stage_expr 472) digest = r472 digest :=
  source_stage_congruence 472 digest

theorem op_473 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 473) digest a b = LLVM.or a b := rfl

theorem align_473 (digest : BitVec 512) :
    (source_stage_expr 473) digest = r473 digest :=
  source_stage_congruence 473 digest

theorem op_474 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 474) digest a b = LLVM.shl a b { nsw := false, nuw := false } := rfl

theorem align_474 (digest : BitVec 512) :
    (source_stage_expr 474) digest = r474 digest :=
  source_stage_congruence 474 digest

theorem op_475 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 475) digest a b = LLVM.or a b := rfl

theorem align_475 (digest : BitVec 512) :
    (source_stage_expr 475) digest = r475 digest :=
  source_stage_congruence 475 digest

theorem op_477 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 477) digest a b = LLVM.lshr a b := rfl

theorem align_477 (digest : BitVec 512) :
    (source_stage_expr 477) digest = r477 digest :=
  source_stage_congruence 477 digest

theorem op_478 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 478) digest a b = LLVM.and a b := rfl

theorem align_478 (digest : BitVec 512) :
    (source_stage_expr 478) digest = r478 digest :=
  source_stage_congruence 478 digest

theorem op_479 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 479) digest a b = LLVM.shl a b { nsw := true, nuw := false } := rfl

theorem align_479 (digest : BitVec 512) :
    (source_stage_expr 479) digest = r479 digest :=
  source_stage_congruence 479 digest

theorem op_480 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 480) digest a b = LLVM.and a b := rfl

theorem align_480 (digest : BitVec 512) :
    (source_stage_expr 480) digest = r480 digest :=
  source_stage_congruence 480 digest

theorem op_481 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 481) digest a b = LLVM.or a b := rfl

theorem align_481 (digest : BitVec 512) :
    (source_stage_expr 481) digest = r481 digest :=
  source_stage_congruence 481 digest

theorem op_482 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 482) digest a b = LLVM.shl a b { nsw := true, nuw := false } := rfl

theorem align_482 (digest : BitVec 512) :
    (source_stage_expr 482) digest = r482 digest :=
  source_stage_congruence 482 digest

theorem op_483 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 483) digest a b = LLVM.or a b := rfl

theorem align_483 (digest : BitVec 512) :
    (source_stage_expr 483) digest = r483 digest :=
  source_stage_congruence 483 digest

theorem sourceReduce_eq (digest : BitVec 512) : sourceReduce digest = reduce digest :=
  source_final_congruence digest

end Firedancer.Common.ScalarArithmetic.Registers
