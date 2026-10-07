import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairReady
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkTail

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure BulkPairLoopConstants (E : Env program.Γ) (cache : Pointer) : Prop where
  zero : E.read (%2) = .value 0#64
  tailStart : E.read (%15) = .value 64#64
  tailLimit : E.read (%17) = .value 80#64
  mask : E.read (%44) = .value 15#64
  cachePtr : E.read (%82) = .value cache
  shift : E.read (%66) = .value 7#64

theorem BulkPairLoopConstants.of_frame {E E' : Env program.Γ} {cache : Pointer}
    (h : BulkPairLoopConstants E cache) (hf : RegFrame 448 581 E E') :
    BulkPairLoopConstants E' cache := by
  constructor
  · exact (hf.read (%2)).trans h.zero
  · exact (hf.read (%15)).trans h.tailStart
  · exact (hf.read (%17)).trans h.tailLimit
  · exact (hf.read (%44)).trans h.mask
  · exact (hf.read (%82)).trans h.cachePtr
  · exact (hf.read (%66)).trans h.shift

def bulkGroupResetEnv (E : Env program.Γ) (cache : Pointer) (g : Nat) : Env program.Γ :=
  bulkGroupPairEnv (bulkGroupSetupEnv (bulkGroupNextEnv (bulkGroupBodyEnv E g)) cache (g+1))

theorem bulk_group_reset_frame (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    RegFrame 448 581 E (bulkGroupResetEnv E cache g) := by
  unfold bulkGroupResetEnv bulkGroupPairEnv bulkGroupSetupEnv bulkGroupNextEnv bulkGroupBodyEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem bulkGroupBodyEnv_local_frame (E : Env program.Γ) (g : Nat) :
    RegFrame 448 449 E (bulkGroupBodyEnv E g) := by
  unfold bulkGroupBodyEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem bulkGroupNextEnv_local_frame (E : Env program.Γ)  :
    RegFrame 450 467 E (bulkGroupNextEnv E) := by
  unfold bulkGroupNextEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem bulkGroupSetupEnv_local_frame (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    RegFrame 468 469 E (bulkGroupSetupEnv E cache g) := by
  unfold bulkGroupSetupEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem bulkGroupPairEnv_local_frame (E : Env program.Γ)  :
    RegFrame 470 487 E (bulkGroupPairEnv E) := by
  unfold bulkGroupPairEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem bulk_group_pair_read_470 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%470) = E.read (%450) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_450 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%450) = E.read (%571) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_470 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%470) = E.read (%571) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_470,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%450),
    bulk_group_next_read_450,
    (bulkGroupBodyEnv_local_frame E g).read (%571)]

private theorem bulk_group_pair_read_471 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%471) = E.read (%2) := by
  simp [bulkGroupPairEnv, mlir_env]

theorem bulk_group_reset_read_471 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%471) = E.read (%2) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_471,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%2),
    (bulkGroupNextEnv_local_frame _).read (%2),
    (bulkGroupBodyEnv_local_frame E g).read (%2)]

private theorem bulk_group_pair_read_472 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%472) = E.read (%452) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_452 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%452) = E.read (%477) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_472 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%472) = E.read (%477) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_472,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%452),
    bulk_group_next_read_452,
    (bulkGroupBodyEnv_local_frame E g).read (%477)]

private theorem bulk_group_pair_read_473 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%473) = E.read (%453) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_453 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%453) = E.read (%472) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_473 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%473) = E.read (%472) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_473,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%453),
    bulk_group_next_read_453,
    (bulkGroupBodyEnv_local_frame E g).read (%472)]

private theorem bulk_group_pair_read_474 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%474) = E.read (%454) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_454 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%454) = E.read (%479) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_474 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%474) = E.read (%479) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_474,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%454),
    bulk_group_next_read_454,
    (bulkGroupBodyEnv_local_frame E g).read (%479)]

private theorem bulk_group_pair_read_475 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%475) = E.read (%455) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_455 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%455) = E.read (%474) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_475 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%475) = E.read (%474) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_475,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%455),
    bulk_group_next_read_455,
    (bulkGroupBodyEnv_local_frame E g).read (%474)]

private theorem bulk_group_pair_read_476 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%476) = E.read (%456) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_456 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%456) = E.read (%514) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_476 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%476) = E.read (%514) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_476,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%456),
    bulk_group_next_read_456,
    (bulkGroupBodyEnv_local_frame E g).read (%514)]

private theorem bulk_group_pair_read_477 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%477) = E.read (%457) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_457 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%457) = E.read (%478) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_477 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%477) = E.read (%478) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_477,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%457),
    bulk_group_next_read_457,
    (bulkGroupBodyEnv_local_frame E g).read (%478)]

private theorem bulk_group_pair_read_478 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%478) = E.read (%458) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_458 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%458) = E.read (%475) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_478 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%478) = E.read (%475) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_478,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%458),
    bulk_group_next_read_458,
    (bulkGroupBodyEnv_local_frame E g).read (%475)]

private theorem bulk_group_pair_read_479 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%479) = E.read (%459) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_459 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%459) = E.read (%476) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_479 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%479) = E.read (%476) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_479,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%459),
    bulk_group_next_read_459,
    (bulkGroupBodyEnv_local_frame E g).read (%476)]

private theorem bulk_group_pair_read_480 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%480) = E.read (%460) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_460 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%460) = E.read (%483) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_480 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%480) = E.read (%483) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_480,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%460),
    bulk_group_next_read_460,
    (bulkGroupBodyEnv_local_frame E g).read (%483)]

private theorem bulk_group_pair_read_481 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%481) = E.read (%461) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_461 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%461) = E.read (%566) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_481 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%481) = E.read (%566) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_481,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%461),
    bulk_group_next_read_461,
    (bulkGroupBodyEnv_local_frame E g).read (%566)]

private theorem bulk_group_pair_read_482 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%482) = E.read (%462) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_462 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%462) = E.read (%481) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_482 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%482) = E.read (%481) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_482,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%462),
    bulk_group_next_read_462,
    (bulkGroupBodyEnv_local_frame E g).read (%481)]

private theorem bulk_group_pair_read_483 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%483) = E.read (%463) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_463 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%463) = E.read (%541) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_483 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%483) = E.read (%541) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_483,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%463),
    bulk_group_next_read_463,
    (bulkGroupBodyEnv_local_frame E g).read (%541)]

private theorem bulk_group_pair_read_484 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%484) = E.read (%464) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_464 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%464) = E.read (%565) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_484 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%484) = E.read (%565) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_484,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%464),
    bulk_group_next_read_464,
    (bulkGroupBodyEnv_local_frame E g).read (%565)]

private theorem bulk_group_pair_read_485 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%485) = E.read (%465) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_465 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%465) = E.read (%540) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_485 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%485) = E.read (%540) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_485,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%465),
    bulk_group_next_read_465,
    (bulkGroupBodyEnv_local_frame E g).read (%540)]

private theorem bulk_group_pair_read_486 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%486) = E.read (%466) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_466 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%466) = E.read (%484) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_486 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%486) = E.read (%484) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_486,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%466),
    bulk_group_next_read_466,
    (bulkGroupBodyEnv_local_frame E g).read (%484)]

private theorem bulk_group_pair_read_487 (E : Env program.Γ) :
    (bulkGroupPairEnv E).read (%487) = E.read (%467) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulk_group_next_read_467 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%467) = E.read (%485) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_487 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%487) = E.read (%485) := by
  unfold bulkGroupResetEnv
  rw [bulk_group_pair_read_487,
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%467),
    bulk_group_next_read_467,
    (bulkGroupBodyEnv_local_frame E g).read (%485)]

theorem bulk_group_reset_read_469 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%469) =
      .value (cache.add (BitVec.ofNat 64 (128*(g+1)))) := by
  unfold bulkGroupResetEnv
  rw [(bulkGroupPairEnv_local_frame _).read (%469)]
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulk_group_next_read_451 (E : Env program.Γ) :
    (bulkGroupNextEnv E).read (%451) = E.read (%448) := by
  simp [bulkGroupNextEnv, mlir_env]

theorem bulk_group_reset_read_451 (E : Env program.Γ) (cache : Pointer) (g : Nat) :
    (bulkGroupResetEnv E cache g).read (%451) = .value (BitVec.ofNat 64 (g+1)) := by
  unfold bulkGroupResetEnv
  rw [(bulkGroupPairEnv_local_frame _).read (%451),
    (bulkGroupSetupEnv_local_frame _ cache (g+1)).read (%451), bulk_group_next_read_451]
  simp [bulkGroupBodyEnv, mlir_env]

theorem bulk_group_reset_ready (E : Env program.Γ) (scratch oldGroup cache k : Pointer)
    (r j g : Nat) (q u : Window) (s : Spec.State)
    (h : BulkPairReady (bulkPairNextEnv E) scratch oldGroup k r j q u s)
    (hz : E.read (%2) = .value 0#64) :
    BulkPairReady (bulkGroupResetEnv E cache g) scratch
      (cache.add (BitVec.ofNat 64 (128*(g+1)))) k r 0 q u s := by
  have hf := bulk_group_reset_frame E cache g
  have hfn := bulkPairNextEnv_frame E
  constructor
  · constructor
    · exact (hf.read (%24)).trans ((hfn.read (%24)).symm.trans h.schedule.constantPtr)
    · rw [bulk_group_reset_read_470]
      simpa [bulkPairNextEnv, mlir_env] using h.schedule.nextIndex
    · simpa only [bulk_group_reset_read_471] using hz
    · exact (hf.read (%1)).trans ((hfn.read (%1)).symm.trans h.schedule.one)
    · exact (hf.read (%68)).trans ((hfn.read (%68)).symm.trans h.schedule.c1)
    · exact (hf.read (%69)).trans ((hfn.read (%69)).symm.trans h.schedule.c7)
    · exact (hf.read (%70)).trans ((hfn.read (%70)).symm.trans h.schedule.c56)
    · exact (hf.read (%71)).trans ((hfn.read (%71)).symm.trans h.schedule.c8)
    · exact (hf.read (%72)).trans ((hfn.read (%72)).symm.trans h.schedule.c63)
    · exact (hf.read (%73)).trans ((hfn.read (%73)).symm.trans h.schedule.c6)
    · exact (hf.read (%74)).trans ((hfn.read (%74)).symm.trans h.schedule.c3)
    · exact (hf.read (%75)).trans ((hfn.read (%75)).symm.trans h.schedule.c19)
    · exact (hf.read (%76)).trans ((hfn.read (%76)).symm.trans h.schedule.c45)
    · exact (hf.read (%77)).trans ((hfn.read (%77)).symm.trans h.schedule.c61)
  · constructor
    · rw [bulk_group_reset_read_473]
      simpa [bulkPairNextEnv, mlir_env] using h.window.p0
    · rw [bulk_group_reset_read_472]
      simpa [bulkPairNextEnv, mlir_env] using h.window.p1
    · rw [bulk_group_reset_read_477]
      simpa [bulkPairNextEnv, mlir_env] using h.window.p2
    · rw [bulk_group_reset_read_478]
      simpa [bulkPairNextEnv, mlir_env] using h.window.p3
    · rw [bulk_group_reset_read_475]
      simpa [bulkPairNextEnv, mlir_env] using h.window.p4
    · rw [bulk_group_reset_read_474]
      simpa [bulkPairNextEnv, mlir_env] using h.window.p5
    · rw [bulk_group_reset_read_479]
      simpa [bulkPairNextEnv, mlir_env] using h.window.p6
    · rw [bulk_group_reset_read_476]
      simpa [bulkPairNextEnv, mlir_env] using h.window.p7
  · constructor
    · exact (hf.read (%83)).trans ((hfn.read (%83)).symm.trans h.scalar.scratchPtr)
    · simpa only [bulk_group_reset_read_471] using hz
    · rw [bulk_group_reset_read_484]
      simpa [bulkPairNextEnv, mlir_env] using h.scalar.a
    · rw [bulk_group_reset_read_485]
      simpa [bulkPairNextEnv, mlir_env] using h.scalar.b
    · rw [bulk_group_reset_read_486]
      simpa [bulkPairNextEnv, mlir_env] using h.scalar.c
    · rw [bulk_group_reset_read_487]
      simpa [bulkPairNextEnv, mlir_env] using h.scalar.d
    · rw [bulk_group_reset_read_481]
      simpa [bulkPairNextEnv, mlir_env] using h.scalar.e
    · rw [bulk_group_reset_read_483]
      simpa [bulkPairNextEnv, mlir_env] using h.scalar.f
    · rw [bulk_group_reset_read_482]
      simpa [bulkPairNextEnv, mlir_env] using h.scalar.g
    · rw [bulk_group_reset_read_480]
      simpa [bulkPairNextEnv, mlir_env] using h.scalar.h
    · exact (hf.read (%3)).trans ((hfn.read (%3)).symm.trans h.scalar.eight)
    · exact (hf.read (%35)).trans ((hfn.read (%35)).symm.trans h.scalar.shift)
    · exact (hf.read (%36)).trans ((hfn.read (%36)).symm.trans h.scalar.rot14)
    · exact (hf.read (%37)).trans ((hfn.read (%37)).symm.trans h.scalar.rot18)
    · exact (hf.read (%38)).trans ((hfn.read (%38)).symm.trans h.scalar.rot41)
    · exact (hf.read (%39)).trans ((hfn.read (%39)).symm.trans h.scalar.rot28)
    · exact (hf.read (%40)).trans ((hfn.read (%40)).symm.trans h.scalar.rot34)
    · exact (hf.read (%41)).trans ((hfn.read (%41)).symm.trans h.scalar.rot39)
  · exact (hf.read (%42)).trans ((hfn.read (%42)).symm.trans h.two)
  · exact bulk_group_reset_read_469 E cache g

theorem bulk_group_reset_counter (E : Env program.Γ) (cache : Pointer) (g : Nat)
    (h : BulkGroupReady E g) : BulkGroupReady (bulkGroupResetEnv E cache g) (g+1) := by
  have hf := bulk_group_reset_frame E cache g
  exact ⟨bulk_group_reset_read_451 E cache g, (hf.read (%1)).trans h.one,
    (hf.read (%78)).trans h.limit⟩

theorem bulk_group_tail_ready (E : Env program.Γ) (scratch cacheGroup cache k : Pointer)
    (r j : Nat) (q u : Window) (s : Spec.State)
    (h : BulkPairReady (bulkPairNextEnv E) scratch cacheGroup k r j q u s)
    (hc : BulkPairLoopConstants E cache) :
    BulkTailReady (bulkGroupTailEnv (bulkGroupBodyEnv E 4)) scratch 64 s := by
  have hs := h.final_of_next
  have hp : E.read (%83) = .value scratch := by
    simpa [bulkPairNextEnv, mlir_env] using h.scalar.scratchPtr
  have hone : E.read (%1) = .value 1#64 := by
    simpa [bulkPairNextEnv, mlir_env] using h.schedule.one
  have h36 : E.read (%36) = .value 50#64 := by
    simpa [bulkPairNextEnv, mlir_env] using h.scalar.rot14
  have h37 : E.read (%37) = .value 46#64 := by
    simpa [bulkPairNextEnv, mlir_env] using h.scalar.rot18
  have h38 : E.read (%38) = .value 23#64 := by
    simpa [bulkPairNextEnv, mlir_env] using h.scalar.rot41
  have h39 : E.read (%39) = .value 36#64 := by
    simpa [bulkPairNextEnv, mlir_env] using h.scalar.rot28
  have h40 : E.read (%40) = .value 30#64 := by
    simpa [bulkPairNextEnv, mlir_env] using h.scalar.rot34
  have h41 : E.read (%41) = .value 25#64 := by
    simpa [bulkPairNextEnv, mlir_env] using h.scalar.rot39
  constructor <;> simp [bulkGroupTailEnv, bulkGroupBodyEnv, mlir_env, hp, hone,
    hs.a, hs.b, hs.c, hs.d, hs.e, hs.f, hs.g, hs.h,
    hc.tailStart, hc.tailLimit, hc.mask, h36, h37, h38, h39, h40, h41]

theorem bulk_group_tail_frame (E : Env program.Γ) :
    RegFrame 448 581 E (bulkGroupTailEnv (bulkGroupBodyEnv E 4)) := by
  unfold bulkGroupTailEnv bulkGroupBodyEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

end Agave.Ed25519.SHA512.Execution.Avx2
