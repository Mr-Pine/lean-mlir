import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairSchedule
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairSecond

/-! Exact terminators and group setup for the bulk bb10/bb11/bb12 nest. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

@[simp] theorem bulk_pair_params10 : program.blockParams 10 =
    .nil := rfl

@[simp] theorem bulk_pair_params11 : program.blockParams 11 =
    .cons (%450) (.cons (%451) (.cons (%452) (.cons (%453) (.cons (%454) (.cons (%455) (.cons (%456) (.cons (%457) (.cons (%458) (.cons (%459) (.cons (%460) (.cons (%461) (.cons (%462) (.cons (%463) (.cons (%464) (.cons (%465) (.cons (%466) (.cons (%467) (.nil)))))))))))))))))) := rfl

@[simp] theorem bulk_pair_params12 : program.blockParams 12 =
    .cons (%470) (.cons (%471) (.cons (%472) (.cons (%473) (.cons (%474) (.cons (%475) (.cons (%476) (.cons (%477) (.cons (%478) (.cons (%479) (.cons (%480) (.cons (%481) (.cons (%482) (.cons (%483) (.cons (%484) (.cons (%485) (.cons (%486) (.cons (%487) (.nil)))))))))))))))))) := rfl

@[simp] theorem bulk_pair_params13 : program.blockParams 13 =
    .cons (%573) (.cons (%574) (.cons (%575) (.cons (%576) (.cons (%577) (.cons (%578) (.cons (%579) (.cons (%580) (.cons (%581) (.nil))))))))) := rfl

def bulkPairNextEnv (E : Env program.Γ) : Env program.Γ :=
  E[%470 := E.read (%571),
    %471 := E.read (%488),
    %472 := E.read (%477),
    %473 := E.read (%472),
    %474 := E.read (%479),
    %475 := E.read (%474),
    %476 := E.read (%514),
    %477 := E.read (%478),
    %478 := E.read (%475),
    %479 := E.read (%476),
    %480 := E.read (%483),
    %481 := E.read (%566),
    %482 := E.read (%481),
    %483 := E.read (%541),
    %484 := E.read (%565),
    %485 := E.read (%540),
    %486 := E.read (%484),
    %487 := E.read (%485)]

def bulkGroupNextEnv (E : Env program.Γ) : Env program.Γ :=
  E[%450 := E.read (%571),
    %451 := E.read (%448),
    %452 := E.read (%477),
    %453 := E.read (%472),
    %454 := E.read (%479),
    %455 := E.read (%474),
    %456 := E.read (%514),
    %457 := E.read (%478),
    %458 := E.read (%475),
    %459 := E.read (%476),
    %460 := E.read (%483),
    %461 := E.read (%566),
    %462 := E.read (%481),
    %463 := E.read (%541),
    %464 := E.read (%565),
    %465 := E.read (%540),
    %466 := E.read (%484),
    %467 := E.read (%485)]

def bulkGroupTailEnv (E : Env program.Γ) : Env program.Γ :=
  E[%573 := E.read (%15),
    %574 := E.read (%483),
    %575 := E.read (%566),
    %576 := E.read (%481),
    %577 := E.read (%541),
    %578 := E.read (%565),
    %579 := E.read (%540),
    %580 := E.read (%484),
    %581 := E.read (%485)]

def bulkGroupPairEnv (E : Env program.Γ) : Env program.Γ :=
  E[%470 := E.read (%450),
    %471 := E.read (%2),
    %472 := E.read (%452),
    %473 := E.read (%453),
    %474 := E.read (%454),
    %475 := E.read (%455),
    %476 := E.read (%456),
    %477 := E.read (%457),
    %478 := E.read (%458),
    %479 := E.read (%459),
    %480 := E.read (%460),
    %481 := E.read (%461),
    %482 := E.read (%462),
    %483 := E.read (%463),
    %484 := E.read (%464),
    %485 := E.read (%465),
    %486 := E.read (%466),
    %487 := E.read (%467)]

theorem bulk_pair_terminator_backedge (E : Env program.Γ) (mem : GlobalState)
    (h : E.read (%572) = .value 0#1) :
    program.bb12.exit.run program.blockParams E mem =
      .value ((bulkPairNextEnv E, .inr 12), mem) := by
  simp [program.bb12, Exit.run, Jump.run, h, bulkPairNextEnv,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_pair_terminator_exit (E : Env program.Γ) (mem : GlobalState)
    (h : E.read (%572) = .value 1#1) :
    program.bb12.exit.run program.blockParams E mem =
      .value ((E, .inr 10), mem) := by
  simp [program.bb12, Exit.run, Jump.run, h,
    Regs.read_nil, Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulkPairNextEnv_window (E : Env program.Γ) (q u : Window)
    (h : BulkPairWindowReady E q u)
    (hnew : E.read (%514) = bulkPairVec (avxWindowPair q) (avxWindowPair u)) :
    BulkPairWindowReady (bulkPairNextEnv E) (avxWindowStep q) (avxWindowStep u) := by
  constructor <;> simp [bulkPairNextEnv, avxWindowStep, bulkPairVec, mlir_env,
    h.p1, h.p2, h.p3, h.p4, h.p5, h.p6, h.p7, hnew]

theorem bulkPairNextEnv_scalar (E : Env program.Γ) (s : Spec.State)
    (h : BulkPairSecondFinalReady E s) :
    (bulkPairNextEnv E).read (%484) = .value s.a ∧
    (bulkPairNextEnv E).read (%485) = .value s.b ∧
    (bulkPairNextEnv E).read (%486) = .value s.c ∧
    (bulkPairNextEnv E).read (%487) = .value s.d ∧
    (bulkPairNextEnv E).read (%481) = .value s.e ∧
    (bulkPairNextEnv E).read (%483) = .value s.f ∧
    (bulkPairNextEnv E).read (%482) = .value s.g ∧
    (bulkPairNextEnv E).read (%480) = .value s.h := by
  simp [bulkPairNextEnv, mlir_env, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h]

/-- Bulk groups are numbered 1..4, since group 0 is the initial cache fill. -/
structure BulkGroupReady (E : Env program.Γ) (g : Nat) : Prop where
  counter : E.read (%451) = .value (BitVec.ofNat 64 g)
  one : E.read (%1) = .value 1#64
  limit : E.read (%78) = .value 5#64

def bulkGroupBodyEnv (E : Env program.Γ) (g : Nat) : Env program.Γ :=
  E[%448 := .value (BitVec.ofNat 64 (g+1)),
    %449 := .value (BitVec.ofBool (decide (g+1=5)))]

theorem bulk_group_body (E : Env program.Γ) (mem : GlobalState) (g : Nat)
    (hg : g < 5) (h : BulkGroupReady E g) :
    List.foldlM Instr.run E program.bb10.body mem =
      .value (bulkGroupBodyEnv E g, mem) := by
  have hadd : Operation.add {nsw := true, nuw := true}
      (.value (BitVec.ofNat 64 g)) (.value 1#64) =
      .value (BitVec.ofNat 64 (g+1)) := by
    interval_cases g <;> decide
  have heq : (BitVec.ofNat 64 (g+1) == 5#64) = decide (g+1=5) := by
    interval_cases g <;> decide
  simp [program.bb10, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bulkGroupBodyEnv, h.counter, h.one, h.limit, hadd, heq, Operation.icmp,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_group_backedge (E : Env program.Γ) (mem : GlobalState) (g : Nat)
    (hg : g < 4) (h : BulkGroupReady E g) :
    program.bb10.run program.blockParams E mem =
      .value ((bulkGroupNextEnv (bulkGroupBodyEnv E g), .inr 11), mem) := by
  have hne : g+1 ≠ 5 := by omega
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulk_group_body E mem g (by omega) h, PoisonOr.value_bind]
  simp [program.bb10, Exit.run, Jump.run, bulkGroupBodyEnv, bulkGroupNextEnv, hne,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_group_exit (E : Env program.Γ) (mem : GlobalState)
    (h : BulkGroupReady E 4) :
    program.bb10.run program.blockParams E mem =
      .value ((bulkGroupTailEnv (bulkGroupBodyEnv E 4), .inr 13), mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulk_group_body E mem 4 (by decide) h, PoisonOr.value_bind]
  simp [program.bb10, Exit.run, Jump.run, bulkGroupBodyEnv, bulkGroupTailEnv,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

def bulkGroupSetupEnv (E : Env program.Γ) (cache : Pointer) (g : Nat) : Env program.Γ :=
  E[%468 := .value (BitVec.ofNat 64 (128*g)),
    %469 := .value (cache.add (BitVec.ofNat 64 (128*g)))]

/-- bb11 computes the destination of the next sixteen second-block words. -/
theorem bulk_group_setup_body (E : Env program.Γ) (mem : GlobalState)
    (cache : Pointer) (g : Nat) (hg : g < 5)
    (hc : SmallRange mem.mem cache 640)
    (hp : E.read (%82) = .value cache)
    (hcount : E.read (%451) = .value (BitVec.ofNat 64 g))
    (hshift : E.read (%66) = .value 7#64) :
    List.foldlM Instr.run E program.bb11.body mem =
      .value (bulkGroupSetupEnv E cache g, mem) := by
  have hsh : Operation.shl {nsw := true, nuw := true}
      (.value (BitVec.ofNat 64 g)) (.value 7#64) =
      .value (BitVec.ofNat 64 (128*g)) := by
    interval_cases g <;> decide
  have hidx : Operation.gepInboundsIndex 1 (.value (BitVec.ofNat 64 (128*g))) =
      .value (Int.ofNat (128*g)) := by
    interval_cases g <;> decide
  have hgep := hc.gep (k := 128*g) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  simp [program.bb11, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bulkGroupSetupEnv, hp, hcount, hshift, hsh, hidx, hgep,
    GepIndex.inboundsOffset, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_group_setup_run (E : Env program.Γ) (mem : GlobalState)
    (cache : Pointer) (g : Nat) (hg : g < 5)
    (hc : SmallRange mem.mem cache 640)
    (hp : E.read (%82) = .value cache)
    (hcount : E.read (%451) = .value (BitVec.ofNat 64 g))
    (hshift : E.read (%66) = .value 7#64) :
    program.bb11.run program.blockParams E mem =
      .value ((bulkGroupPairEnv (bulkGroupSetupEnv E cache g), .inr 12), mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulk_group_setup_body E mem cache g hg hc hp hcount hshift, PoisonOr.value_bind]
  simp [program.bb11, Exit.run, Jump.run, bulkGroupPairEnv,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.SHA512.Execution.Avx2
