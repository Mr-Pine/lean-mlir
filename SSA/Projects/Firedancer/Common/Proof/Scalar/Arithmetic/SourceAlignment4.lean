import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceAlignment3

namespace Firedancer.Common.ScalarArithmetic.Registers
open InstCombine (LLVM)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem op_298 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 298) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_298 (digest : BitVec 512) :
    (source_stage_expr 298) digest = r298 digest :=
  source_stage_congruence 298 digest

theorem op_299 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 299) digest a b = LLVM.ashr a b := rfl

theorem align_299 (digest : BitVec 512) :
    (source_stage_expr 299) digest = r299 digest :=
  source_stage_congruence 299 digest

theorem op_300 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 300) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_300 (digest : BitVec 512) :
    (source_stage_expr 300) digest = r300 digest :=
  source_stage_congruence 300 digest

theorem op_301 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 301) digest a b = LLVM.and a b := rfl

theorem align_301 (digest : BitVec 512) :
    (source_stage_expr 301) digest = r301 digest :=
  source_stage_congruence 301 digest

theorem op_302 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 302) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_302 (digest : BitVec 512) :
    (source_stage_expr 302) digest = r302 digest :=
  source_stage_congruence 302 digest

theorem op_303 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 303) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_303 (digest : BitVec 512) :
    (source_stage_expr 303) digest = r303 digest :=
  source_stage_congruence 303 digest

theorem op_304 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 304) digest a b = LLVM.ashr a b := rfl

theorem align_304 (digest : BitVec 512) :
    (source_stage_expr 304) digest = r304 digest :=
  source_stage_congruence 304 digest

theorem op_305 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 305) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_305 (digest : BitVec 512) :
    (source_stage_expr 305) digest = r305 digest :=
  source_stage_congruence 305 digest

theorem op_306 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 306) digest a b = LLVM.and a b := rfl

theorem align_306 (digest : BitVec 512) :
    (source_stage_expr 306) digest = r306 digest :=
  source_stage_congruence 306 digest

theorem op_307 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 307) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_307 (digest : BitVec 512) :
    (source_stage_expr 307) digest = r307 digest :=
  source_stage_congruence 307 digest

theorem op_308 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 308) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_308 (digest : BitVec 512) :
    (source_stage_expr 308) digest = r308 digest :=
  source_stage_congruence 308 digest

theorem op_309 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 309) digest a b = LLVM.ashr a b := rfl

theorem align_309 (digest : BitVec 512) :
    (source_stage_expr 309) digest = r309 digest :=
  source_stage_congruence 309 digest

theorem op_310 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 310) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_310 (digest : BitVec 512) :
    (source_stage_expr 310) digest = r310 digest :=
  source_stage_congruence 310 digest

theorem op_311 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 311) digest a b = LLVM.and a b := rfl

theorem align_311 (digest : BitVec 512) :
    (source_stage_expr 311) digest = r311 digest :=
  source_stage_congruence 311 digest

theorem op_312 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 312) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_312 (digest : BitVec 512) :
    (source_stage_expr 312) digest = r312 digest :=
  source_stage_congruence 312 digest

theorem op_313 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 313) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_313 (digest : BitVec 512) :
    (source_stage_expr 313) digest = r313 digest :=
  source_stage_congruence 313 digest

theorem op_314 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 314) digest a b = LLVM.ashr a b := rfl

theorem align_314 (digest : BitVec 512) :
    (source_stage_expr 314) digest = r314 digest :=
  source_stage_congruence 314 digest

theorem op_315 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 315) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_315 (digest : BitVec 512) :
    (source_stage_expr 315) digest = r315 digest :=
  source_stage_congruence 315 digest

theorem op_316 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 316) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_316 (digest : BitVec 512) :
    (source_stage_expr 316) digest = r316 digest :=
  source_stage_congruence 316 digest

theorem op_317 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 317) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_317 (digest : BitVec 512) :
    (source_stage_expr 317) digest = r317 digest :=
  source_stage_congruence 317 digest

theorem op_318 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 318) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_318 (digest : BitVec 512) :
    (source_stage_expr 318) digest = r318 digest :=
  source_stage_congruence 318 digest

theorem op_319 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 319) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_319 (digest : BitVec 512) :
    (source_stage_expr 319) digest = r319 digest :=
  source_stage_congruence 319 digest

theorem op_320 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 320) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_320 (digest : BitVec 512) :
    (source_stage_expr 320) digest = r320 digest :=
  source_stage_congruence 320 digest

theorem op_321 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 321) digest a b = LLVM.and a b := rfl

theorem align_321 (digest : BitVec 512) :
    (source_stage_expr 321) digest = r321 digest :=
  source_stage_congruence 321 digest

theorem op_322 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 322) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_322 (digest : BitVec 512) :
    (source_stage_expr 322) digest = r322 digest :=
  source_stage_congruence 322 digest

theorem op_323 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 323) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_323 (digest : BitVec 512) :
    (source_stage_expr 323) digest = r323 digest :=
  source_stage_congruence 323 digest

theorem op_324 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 324) digest a b = LLVM.ashr a b := rfl

theorem align_324 (digest : BitVec 512) :
    (source_stage_expr 324) digest = r324 digest :=
  source_stage_congruence 324 digest

theorem op_325 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 325) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_325 (digest : BitVec 512) :
    (source_stage_expr 325) digest = r325 digest :=
  source_stage_congruence 325 digest

theorem op_326 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 326) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_326 (digest : BitVec 512) :
    (source_stage_expr 326) digest = r326 digest :=
  source_stage_congruence 326 digest

theorem op_327 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 327) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_327 (digest : BitVec 512) :
    (source_stage_expr 327) digest = r327 digest :=
  source_stage_congruence 327 digest

theorem op_328 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 328) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_328 (digest : BitVec 512) :
    (source_stage_expr 328) digest = r328 digest :=
  source_stage_congruence 328 digest

theorem op_329 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 329) digest a b = LLVM.and a b := rfl

theorem align_329 (digest : BitVec 512) :
    (source_stage_expr 329) digest = r329 digest :=
  source_stage_congruence 329 digest

theorem op_330 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 330) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_330 (digest : BitVec 512) :
    (source_stage_expr 330) digest = r330 digest :=
  source_stage_congruence 330 digest

theorem op_331 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 331) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_331 (digest : BitVec 512) :
    (source_stage_expr 331) digest = r331 digest :=
  source_stage_congruence 331 digest

theorem op_332 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 332) digest a b = LLVM.ashr a b := rfl

theorem align_332 (digest : BitVec 512) :
    (source_stage_expr 332) digest = r332 digest :=
  source_stage_congruence 332 digest

theorem op_333 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 333) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_333 (digest : BitVec 512) :
    (source_stage_expr 333) digest = r333 digest :=
  source_stage_congruence 333 digest

theorem op_334 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 334) digest a b = LLVM.and a b := rfl

theorem align_334 (digest : BitVec 512) :
    (source_stage_expr 334) digest = r334 digest :=
  source_stage_congruence 334 digest

theorem op_335 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 335) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_335 (digest : BitVec 512) :
    (source_stage_expr 335) digest = r335 digest :=
  source_stage_congruence 335 digest

theorem op_336 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 336) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_336 (digest : BitVec 512) :
    (source_stage_expr 336) digest = r336 digest :=
  source_stage_congruence 336 digest

theorem op_337 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 337) digest a b = LLVM.ashr a b := rfl

theorem align_337 (digest : BitVec 512) :
    (source_stage_expr 337) digest = r337 digest :=
  source_stage_congruence 337 digest

theorem op_338 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 338) digest a b = LLVM.and a b := rfl

theorem align_338 (digest : BitVec 512) :
    (source_stage_expr 338) digest = r338 digest :=
  source_stage_congruence 338 digest

theorem op_339 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 339) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_339 (digest : BitVec 512) :
    (source_stage_expr 339) digest = r339 digest :=
  source_stage_congruence 339 digest

theorem op_340 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 340) digest a b = LLVM.ashr a b := rfl

theorem align_340 (digest : BitVec 512) :
    (source_stage_expr 340) digest = r340 digest :=
  source_stage_congruence 340 digest

theorem op_341 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 341) digest a b = LLVM.and a b := rfl

theorem align_341 (digest : BitVec 512) :
    (source_stage_expr 341) digest = r341 digest :=
  source_stage_congruence 341 digest

theorem op_342 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 342) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_342 (digest : BitVec 512) :
    (source_stage_expr 342) digest = r342 digest :=
  source_stage_congruence 342 digest

theorem op_343 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 343) digest a b = LLVM.ashr a b := rfl

theorem align_343 (digest : BitVec 512) :
    (source_stage_expr 343) digest = r343 digest :=
  source_stage_congruence 343 digest

theorem op_344 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 344) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_344 (digest : BitVec 512) :
    (source_stage_expr 344) digest = r344 digest :=
  source_stage_congruence 344 digest

theorem op_345 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 345) digest a b = LLVM.and a b := rfl

theorem align_345 (digest : BitVec 512) :
    (source_stage_expr 345) digest = r345 digest :=
  source_stage_congruence 345 digest

theorem op_346 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 346) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_346 (digest : BitVec 512) :
    (source_stage_expr 346) digest = r346 digest :=
  source_stage_congruence 346 digest

theorem op_347 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 347) digest a b = LLVM.ashr a b := rfl

theorem align_347 (digest : BitVec 512) :
    (source_stage_expr 347) digest = r347 digest :=
  source_stage_congruence 347 digest

theorem op_348 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 348) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_348 (digest : BitVec 512) :
    (source_stage_expr 348) digest = r348 digest :=
  source_stage_congruence 348 digest

theorem op_349 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 349) digest a b = LLVM.and a b := rfl

theorem align_349 (digest : BitVec 512) :
    (source_stage_expr 349) digest = r349 digest :=
  source_stage_congruence 349 digest

theorem op_350 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 350) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_350 (digest : BitVec 512) :
    (source_stage_expr 350) digest = r350 digest :=
  source_stage_congruence 350 digest

theorem op_351 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 351) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_351 (digest : BitVec 512) :
    (source_stage_expr 351) digest = r351 digest :=
  source_stage_congruence 351 digest

theorem op_352 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 352) digest a b = LLVM.ashr a b := rfl

theorem align_352 (digest : BitVec 512) :
    (source_stage_expr 352) digest = r352 digest :=
  source_stage_congruence 352 digest

theorem op_353 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 353) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_353 (digest : BitVec 512) :
    (source_stage_expr 353) digest = r353 digest :=
  source_stage_congruence 353 digest

theorem op_354 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 354) digest a b = LLVM.and a b := rfl

theorem align_354 (digest : BitVec 512) :
    (source_stage_expr 354) digest = r354 digest :=
  source_stage_congruence 354 digest

theorem op_355 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 355) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_355 (digest : BitVec 512) :
    (source_stage_expr 355) digest = r355 digest :=
  source_stage_congruence 355 digest

theorem op_356 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 356) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_356 (digest : BitVec 512) :
    (source_stage_expr 356) digest = r356 digest :=
  source_stage_congruence 356 digest

theorem op_357 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 357) digest a b = LLVM.ashr a b := rfl

theorem align_357 (digest : BitVec 512) :
    (source_stage_expr 357) digest = r357 digest :=
  source_stage_congruence 357 digest

theorem op_358 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 358) digest a b = LLVM.and a b := rfl

theorem align_358 (digest : BitVec 512) :
    (source_stage_expr 358) digest = r358 digest :=
  source_stage_congruence 358 digest

theorem op_359 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 359) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_359 (digest : BitVec 512) :
    (source_stage_expr 359) digest = r359 digest :=
  source_stage_congruence 359 digest

theorem op_360 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 360) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_360 (digest : BitVec 512) :
    (source_stage_expr 360) digest = r360 digest :=
  source_stage_congruence 360 digest

theorem op_361 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 361) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_361 (digest : BitVec 512) :
    (source_stage_expr 361) digest = r361 digest :=
  source_stage_congruence 361 digest

theorem op_362 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 362) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_362 (digest : BitVec 512) :
    (source_stage_expr 362) digest = r362 digest :=
  source_stage_congruence 362 digest

theorem op_363 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 363) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_363 (digest : BitVec 512) :
    (source_stage_expr 363) digest = r363 digest :=
  source_stage_congruence 363 digest

theorem op_364 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 364) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_364 (digest : BitVec 512) :
    (source_stage_expr 364) digest = r364 digest :=
  source_stage_congruence 364 digest

theorem op_365 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 365) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_365 (digest : BitVec 512) :
    (source_stage_expr 365) digest = r365 digest :=
  source_stage_congruence 365 digest

theorem op_366 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 366) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_366 (digest : BitVec 512) :
    (source_stage_expr 366) digest = r366 digest :=
  source_stage_congruence 366 digest

end Firedancer.Common.ScalarArithmetic.Registers
