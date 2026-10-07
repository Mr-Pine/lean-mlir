import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkSecondBody

/-! Imported bb15 loop edges, including the final edge entering bb16. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

@[simp] theorem bulkSecond_params15 : program.blockParams 15 =
    .cons (%618) (.cons (%619) (.cons (%620) (.cons (%621) (.cons (%622)
      (.cons (%623) (.cons (%624) (.cons (%625) (.cons (%626) .nil)))))))) := rfl

@[simp] theorem bulkSecond_params16 : program.blockParams 16 = .nil := rfl

theorem bulkSecond_next_ready (E : Env program.Γ) (cache : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) (h : BulkSecondReady E cache r s) :
    BulkSecondReady
      (bulkSecondNextEnv (bulkSecondBodyEnv E cache r s kw) (r + 1) (tailRound s kw))
      cache (r + 1) (tailRound s kw) := by
  constructor <;> simp [bulkSecondNextEnv, bulkSecondBodyEnv, mlir_env,
    h.cache, h.eight, h.limit, h.rot14, h.rot18, h.rot41, h.rot28, h.rot34, h.rot39]

theorem bulkSecond_final_ready (E : Env program.Γ) (cache : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) (h : BulkSecondReady E cache r s) :
    BulkSecondFinalReady (bulkSecondBodyEnv E cache r s kw) (tailRound s kw) := by
  constructor <;> simp [bulkSecondBodyEnv, tailRound, bigSigma0, bigSigma1, mlir_env,
    h.a, h.b, h.c, h.e, h.f, h.g]

theorem bulkSecond_backedge (E : Env program.Γ) (mem : GlobalState) (cache : Pointer)
    (r : Nat) (s : Spec.State) (words : List Word) (hhi : r < 79)
    (h : BulkSecondReady E cache r s)
    (hs : BulkSecondSchedule mem.mem cache words) :
    program.bb15.run program.blockParams E mem =
      .value ((bulkSecondNextEnv (bulkSecondBodyEnv E cache r s
          (constants.toList.getD r 0 + words.getD r 0)) (r + 1)
          (tailRound s (constants.toList.getD r 0 + words.getD r 0)), .inr 15), mem) := by
  have hr : r + 1 ≠ 80 := by omega
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulkSecond_body E mem cache r s words (by omega) h hs, PoisonOr.value_bind]
  simp [program.bb15, Exit.run, Jump.run, bulkSecondBodyEnv,
    bulkSecondNextEnv, tailRound, bigSigma0, bigSigma1, hr,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    h.a, h.b, h.c, h.e, h.f, h.g,
    EffectM.pure_eq, mlir_env, mlir_effect]

/-- Round 79 enters bb16 with no successor parameters and unchanged memory. -/
theorem bulkSecond_exit (E : Env program.Γ) (mem : GlobalState) (cache : Pointer)
    (s : Spec.State) (words : List Word)
    (h : BulkSecondReady E cache 79 s)
    (hs : BulkSecondSchedule mem.mem cache words) :
    program.bb15.run program.blockParams E mem =
      .value ((bulkSecondBodyEnv E cache 79 s
          (constants.toList.getD 79 0 + words.getD 79 0), .inr 16), mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulkSecond_body E mem cache 79 s words (by decide) h hs, PoisonOr.value_bind]
  simp [program.bb15, Exit.run, Jump.run, bulkSecondBodyEnv,
    Regs.read_nil, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.SHA512.Execution.Avx2
