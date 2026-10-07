import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceAlignment4

namespace Firedancer.Common.ScalarArithmetic.Registers
open InstCombine (LLVM)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem op_367 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 367) digest a b = LLVM.ashr a b := rfl

theorem align_367 (digest : BitVec 512) :
    (source_stage_expr 367) digest = r367 digest :=
  source_stage_congruence 367 digest

theorem op_368 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 368) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_368 (digest : BitVec 512) :
    (source_stage_expr 368) digest = r368 digest :=
  source_stage_congruence 368 digest

theorem op_369 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 369) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_369 (digest : BitVec 512) :
    (source_stage_expr 369) digest = r369 digest :=
  source_stage_congruence 369 digest

theorem op_370 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 370) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_370 (digest : BitVec 512) :
    (source_stage_expr 370) digest = r370 digest :=
  source_stage_congruence 370 digest

theorem op_371 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 371) digest a b = LLVM.and a b := rfl

theorem align_371 (digest : BitVec 512) :
    (source_stage_expr 371) digest = r371 digest :=
  source_stage_congruence 371 digest

theorem op_372 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 372) digest a b = LLVM.ashr a b := rfl

theorem align_372 (digest : BitVec 512) :
    (source_stage_expr 372) digest = r372 digest :=
  source_stage_congruence 372 digest

theorem op_373 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 373) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_373 (digest : BitVec 512) :
    (source_stage_expr 373) digest = r373 digest :=
  source_stage_congruence 373 digest

theorem op_374 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 374) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_374 (digest : BitVec 512) :
    (source_stage_expr 374) digest = r374 digest :=
  source_stage_congruence 374 digest

theorem op_375 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 375) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_375 (digest : BitVec 512) :
    (source_stage_expr 375) digest = r375 digest :=
  source_stage_congruence 375 digest

theorem op_376 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 376) digest a b = LLVM.and a b := rfl

theorem align_376 (digest : BitVec 512) :
    (source_stage_expr 376) digest = r376 digest :=
  source_stage_congruence 376 digest

theorem op_377 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 377) digest a b = LLVM.ashr a b := rfl

theorem align_377 (digest : BitVec 512) :
    (source_stage_expr 377) digest = r377 digest :=
  source_stage_congruence 377 digest

theorem op_378 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 378) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_378 (digest : BitVec 512) :
    (source_stage_expr 378) digest = r378 digest :=
  source_stage_congruence 378 digest

theorem op_379 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 379) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_379 (digest : BitVec 512) :
    (source_stage_expr 379) digest = r379 digest :=
  source_stage_congruence 379 digest

theorem op_380 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 380) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_380 (digest : BitVec 512) :
    (source_stage_expr 380) digest = r380 digest :=
  source_stage_congruence 380 digest

theorem op_381 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 381) digest a b = LLVM.and a b := rfl

theorem align_381 (digest : BitVec 512) :
    (source_stage_expr 381) digest = r381 digest :=
  source_stage_congruence 381 digest

theorem op_382 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 382) digest a b = LLVM.ashr a b := rfl

theorem align_382 (digest : BitVec 512) :
    (source_stage_expr 382) digest = r382 digest :=
  source_stage_congruence 382 digest

theorem op_383 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 383) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_383 (digest : BitVec 512) :
    (source_stage_expr 383) digest = r383 digest :=
  source_stage_congruence 383 digest

theorem op_384 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 384) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_384 (digest : BitVec 512) :
    (source_stage_expr 384) digest = r384 digest :=
  source_stage_congruence 384 digest

theorem op_385 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 385) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_385 (digest : BitVec 512) :
    (source_stage_expr 385) digest = r385 digest :=
  source_stage_congruence 385 digest

theorem op_386 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 386) digest a b = LLVM.and a b := rfl

theorem align_386 (digest : BitVec 512) :
    (source_stage_expr 386) digest = r386 digest :=
  source_stage_congruence 386 digest

theorem op_387 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 387) digest a b = LLVM.ashr a b := rfl

theorem align_387 (digest : BitVec 512) :
    (source_stage_expr 387) digest = r387 digest :=
  source_stage_congruence 387 digest

theorem op_388 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 388) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_388 (digest : BitVec 512) :
    (source_stage_expr 388) digest = r388 digest :=
  source_stage_congruence 388 digest

theorem op_389 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 389) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_389 (digest : BitVec 512) :
    (source_stage_expr 389) digest = r389 digest :=
  source_stage_congruence 389 digest

theorem op_390 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 390) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_390 (digest : BitVec 512) :
    (source_stage_expr 390) digest = r390 digest :=
  source_stage_congruence 390 digest

theorem op_391 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 391) digest a b = LLVM.and a b := rfl

theorem align_391 (digest : BitVec 512) :
    (source_stage_expr 391) digest = r391 digest :=
  source_stage_congruence 391 digest

theorem op_392 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 392) digest a b = LLVM.ashr a b := rfl

theorem align_392 (digest : BitVec 512) :
    (source_stage_expr 392) digest = r392 digest :=
  source_stage_congruence 392 digest

theorem op_393 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 393) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_393 (digest : BitVec 512) :
    (source_stage_expr 393) digest = r393 digest :=
  source_stage_congruence 393 digest

theorem op_394 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 394) digest a b = LLVM.and a b := rfl

theorem align_394 (digest : BitVec 512) :
    (source_stage_expr 394) digest = r394 digest :=
  source_stage_congruence 394 digest

theorem op_395 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 395) digest a b = LLVM.ashr a b := rfl

theorem align_395 (digest : BitVec 512) :
    (source_stage_expr 395) digest = r395 digest :=
  source_stage_congruence 395 digest

theorem op_396 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 396) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_396 (digest : BitVec 512) :
    (source_stage_expr 396) digest = r396 digest :=
  source_stage_congruence 396 digest

theorem op_397 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 397) digest a b = LLVM.and a b := rfl

theorem align_397 (digest : BitVec 512) :
    (source_stage_expr 397) digest = r397 digest :=
  source_stage_congruence 397 digest

theorem op_398 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 398) digest a b = LLVM.ashr a b := rfl

theorem align_398 (digest : BitVec 512) :
    (source_stage_expr 398) digest = r398 digest :=
  source_stage_congruence 398 digest

theorem op_399 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 399) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_399 (digest : BitVec 512) :
    (source_stage_expr 399) digest = r399 digest :=
  source_stage_congruence 399 digest

theorem op_400 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 400) digest a b = LLVM.and a b := rfl

theorem align_400 (digest : BitVec 512) :
    (source_stage_expr 400) digest = r400 digest :=
  source_stage_congruence 400 digest

theorem op_401 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 401) digest a b = LLVM.ashr a b := rfl

theorem align_401 (digest : BitVec 512) :
    (source_stage_expr 401) digest = r401 digest :=
  source_stage_congruence 401 digest

theorem op_402 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 402) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_402 (digest : BitVec 512) :
    (source_stage_expr 402) digest = r402 digest :=
  source_stage_congruence 402 digest

theorem op_403 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 403) digest a b = LLVM.and a b := rfl

theorem align_403 (digest : BitVec 512) :
    (source_stage_expr 403) digest = r403 digest :=
  source_stage_congruence 403 digest

theorem op_404 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 404) digest a b = LLVM.ashr a b := rfl

theorem align_404 (digest : BitVec 512) :
    (source_stage_expr 404) digest = r404 digest :=
  source_stage_congruence 404 digest

theorem op_405 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 405) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_405 (digest : BitVec 512) :
    (source_stage_expr 405) digest = r405 digest :=
  source_stage_congruence 405 digest

theorem op_406 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 406) digest a b = LLVM.and a b := rfl

theorem align_406 (digest : BitVec 512) :
    (source_stage_expr 406) digest = r406 digest :=
  source_stage_congruence 406 digest

theorem op_407 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 407) digest a b = LLVM.ashr a b := rfl

theorem align_407 (digest : BitVec 512) :
    (source_stage_expr 407) digest = r407 digest :=
  source_stage_congruence 407 digest

theorem op_408 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 408) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_408 (digest : BitVec 512) :
    (source_stage_expr 408) digest = r408 digest :=
  source_stage_congruence 408 digest

theorem op_409 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 409) digest a b = LLVM.and a b := rfl

theorem align_409 (digest : BitVec 512) :
    (source_stage_expr 409) digest = r409 digest :=
  source_stage_congruence 409 digest

theorem op_410 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 410) digest a b = LLVM.ashr a b := rfl

theorem align_410 (digest : BitVec 512) :
    (source_stage_expr 410) digest = r410 digest :=
  source_stage_congruence 410 digest

theorem op_411 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 411) digest a b = LLVM.and a b := rfl

theorem align_411 (digest : BitVec 512) :
    (source_stage_expr 411) digest = r411 digest :=
  source_stage_congruence 411 digest

theorem op_412 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 412) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_412 (digest : BitVec 512) :
    (source_stage_expr 412) digest = r412 digest :=
  source_stage_congruence 412 digest

theorem op_413 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 413) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_413 (digest : BitVec 512) :
    (source_stage_expr 413) digest = r413 digest :=
  source_stage_congruence 413 digest

theorem op_414 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 414) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_414 (digest : BitVec 512) :
    (source_stage_expr 414) digest = r414 digest :=
  source_stage_congruence 414 digest

theorem op_415 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 415) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_415 (digest : BitVec 512) :
    (source_stage_expr 415) digest = r415 digest :=
  source_stage_congruence 415 digest

theorem op_416 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 416) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_416 (digest : BitVec 512) :
    (source_stage_expr 416) digest = r416 digest :=
  source_stage_congruence 416 digest

theorem op_417 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 417) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_417 (digest : BitVec 512) :
    (source_stage_expr 417) digest = r417 digest :=
  source_stage_congruence 417 digest

theorem op_418 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 418) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_418 (digest : BitVec 512) :
    (source_stage_expr 418) digest = r418 digest :=
  source_stage_congruence 418 digest

theorem op_419 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 419) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_419 (digest : BitVec 512) :
    (source_stage_expr 419) digest = r419 digest :=
  source_stage_congruence 419 digest

theorem op_420 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 420) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_420 (digest : BitVec 512) :
    (source_stage_expr 420) digest = r420 digest :=
  source_stage_congruence 420 digest

theorem op_421 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 421) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_421 (digest : BitVec 512) :
    (source_stage_expr 421) digest = r421 digest :=
  source_stage_congruence 421 digest

theorem op_422 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 422) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_422 (digest : BitVec 512) :
    (source_stage_expr 422) digest = r422 digest :=
  source_stage_congruence 422 digest

theorem op_423 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 423) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_423 (digest : BitVec 512) :
    (source_stage_expr 423) digest = r423 digest :=
  source_stage_congruence 423 digest

theorem op_424 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 424) digest a b = LLVM.ashr a b := rfl

theorem align_424 (digest : BitVec 512) :
    (source_stage_expr 424) digest = r424 digest :=
  source_stage_congruence 424 digest

theorem op_425 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 425) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_425 (digest : BitVec 512) :
    (source_stage_expr 425) digest = r425 digest :=
  source_stage_congruence 425 digest

theorem op_426 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 426) digest a b = LLVM.and a b := rfl

theorem align_426 (digest : BitVec 512) :
    (source_stage_expr 426) digest = r426 digest :=
  source_stage_congruence 426 digest

theorem op_427 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 427) digest a b = LLVM.ashr a b := rfl

theorem align_427 (digest : BitVec 512) :
    (source_stage_expr 427) digest = r427 digest :=
  source_stage_congruence 427 digest

theorem op_428 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 428) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_428 (digest : BitVec 512) :
    (source_stage_expr 428) digest = r428 digest :=
  source_stage_congruence 428 digest

theorem op_429 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 429) digest a b = LLVM.ashr a b := rfl

theorem align_429 (digest : BitVec 512) :
    (source_stage_expr 429) digest = r429 digest :=
  source_stage_congruence 429 digest

theorem op_430 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 430) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_430 (digest : BitVec 512) :
    (source_stage_expr 430) digest = r430 digest :=
  source_stage_congruence 430 digest

theorem op_431 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 431) digest a b = LLVM.ashr a b := rfl

theorem align_431 (digest : BitVec 512) :
    (source_stage_expr 431) digest = r431 digest :=
  source_stage_congruence 431 digest

theorem op_432 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 432) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_432 (digest : BitVec 512) :
    (source_stage_expr 432) digest = r432 digest :=
  source_stage_congruence 432 digest

theorem op_433 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 433) digest a b = LLVM.ashr a b := rfl

theorem align_433 (digest : BitVec 512) :
    (source_stage_expr 433) digest = r433 digest :=
  source_stage_congruence 433 digest

theorem op_434 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 434) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_434 (digest : BitVec 512) :
    (source_stage_expr 434) digest = r434 digest :=
  source_stage_congruence 434 digest

theorem op_435 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 435) digest a b = LLVM.ashr a b := rfl

theorem align_435 (digest : BitVec 512) :
    (source_stage_expr 435) digest = r435 digest :=
  source_stage_congruence 435 digest

theorem op_436 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 436) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_436 (digest : BitVec 512) :
    (source_stage_expr 436) digest = r436 digest :=
  source_stage_congruence 436 digest

theorem op_437 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 437) digest a b = LLVM.ashr a b := rfl

theorem align_437 (digest : BitVec 512) :
    (source_stage_expr 437) digest = r437 digest :=
  source_stage_congruence 437 digest

theorem op_438 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 438) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_438 (digest : BitVec 512) :
    (source_stage_expr 438) digest = r438 digest :=
  source_stage_congruence 438 digest

theorem op_439 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 439) digest a b = LLVM.ashr a b := rfl

theorem align_439 (digest : BitVec 512) :
    (source_stage_expr 439) digest = r439 digest :=
  source_stage_congruence 439 digest

theorem op_440 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 440) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_440 (digest : BitVec 512) :
    (source_stage_expr 440) digest = r440 digest :=
  source_stage_congruence 440 digest

theorem op_441 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 441) digest a b = LLVM.ashr a b := rfl

theorem align_441 (digest : BitVec 512) :
    (source_stage_expr 441) digest = r441 digest :=
  source_stage_congruence 441 digest

theorem op_442 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 442) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_442 (digest : BitVec 512) :
    (source_stage_expr 442) digest = r442 digest :=
  source_stage_congruence 442 digest

theorem op_443 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 443) digest a b = LLVM.ashr a b := rfl

theorem align_443 (digest : BitVec 512) :
    (source_stage_expr 443) digest = r443 digest :=
  source_stage_congruence 443 digest

theorem op_444 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 444) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_444 (digest : BitVec 512) :
    (source_stage_expr 444) digest = r444 digest :=
  source_stage_congruence 444 digest

theorem op_445 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 445) digest a b = LLVM.ashr a b := rfl

theorem align_445 (digest : BitVec 512) :
    (source_stage_expr 445) digest = r445 digest :=
  source_stage_congruence 445 digest

theorem op_446 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 446) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_446 (digest : BitVec 512) :
    (source_stage_expr 446) digest = r446 digest :=
  source_stage_congruence 446 digest

end Firedancer.Common.ScalarArithmetic.Registers
