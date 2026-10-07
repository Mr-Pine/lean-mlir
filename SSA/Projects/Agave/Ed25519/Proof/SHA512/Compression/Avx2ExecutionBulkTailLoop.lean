import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkTail

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

@[simp] theorem bulkTail_params13 : program.blockParams 13 =
    .cons (%573) (.cons (%574) (.cons (%575) (.cons (%576) (.cons (%577)
      (.cons (%578) (.cons (%579) (.cons (%580) (.cons (%581) .nil)))))))) := rfl

@[simp] theorem bulkTail_params14 : program.blockParams 14 = .nil := rfl

/-- Register interpretation consumed by the imported bb14 feed-forward code. -/
structure BulkTailFinalReady (E : Env program.Γ) (s : Spec.State) : Prop where
  a : E.read (%607) = .value s.a
  b : E.read (%578) = .value s.b
  c : E.read (%579) = .value s.c
  d : E.read (%580) = .value s.d
  e : E.read (%608) = .value s.e
  f : E.read (%575) = .value s.f
  g : E.read (%577) = .value s.g
  h : E.read (%576) = .value s.h

theorem bulkTail_next_ready (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) (h : BulkTailReady E scratch r s) :
    BulkTailReady (bulkTailNextEnv (bulkTailBodyEnv E scratch r s kw) (r + 1) (tailRound s kw))
      scratch (r + 1) (tailRound s kw) := by
  constructor <;> simp [bulkTailNextEnv, bulkTailBodyEnv, mlir_env,
    h.scratch, h.one, h.limit, h.rot14, h.rot18, h.rot41, h.rot28, h.rot34,
    h.rot39, h.mask]

theorem bulkTail_final_ready (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) (h : BulkTailReady E scratch r s) :
    BulkTailFinalReady (bulkTailBodyEnv E scratch r s kw) (tailRound s kw) := by
  constructor <;> simp [bulkTailBodyEnv, tailRound, bigSigma0, bigSigma1, mlir_env,
    h.a, h.b, h.c, h.e, h.f, h.g]

/-- Exact body and terminator, including the actual backedge parameter map. -/
theorem bulkTail_backedge (E : Env program.Γ) (mem : GlobalState) (scratch : Pointer)
    (r : Nat) (s : Spec.State) (words : List Word)
    (hlo : 64 ≤ r) (hhi : r < 79)
    (h : BulkTailReady E scratch r s) (hs : TailSchedule mem.mem scratch words) :
    program.bb13.run program.blockParams E mem =
      .value ((bulkTailNextEnv (bulkTailBodyEnv E scratch r s
          (constants.toList.getD r 0 + words.getD r 0)) (r + 1)
          (tailRound s (constants.toList.getD r 0 + words.getD r 0)), .inr 13), mem) := by
  have hr : r + 1 ≠ 80 := by omega
  simp only [BasicBlock.run, EffectM.bind_eq, bulkTail_body E mem scratch r s words hlo
    (by omega) h hs, PoisonOr.value_bind]
  simp [program.bb13, Exit.run, Jump.run, bulkTailBodyEnv,
    bulkTailNextEnv, tailRound, bigSigma0, bigSigma1, hr,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    h.a, h.b, h.c, h.e, h.f, h.g,
    EffectM.pure_eq, mlir_env, mlir_effect]

/-- Round 79 follows the imported exit to bb14 without rewriting header parameters. -/
theorem bulkTail_exit (E : Env program.Γ) (mem : GlobalState) (scratch : Pointer)
    (s : Spec.State) (words : List Word)
    (h : BulkTailReady E scratch 79 s) (hs : TailSchedule mem.mem scratch words) :
    program.bb13.run program.blockParams E mem =
      .value ((bulkTailBodyEnv E scratch 79 s
          (constants.toList.getD 79 0 + words.getD 79 0), .inr 14), mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq, bulkTail_body E mem scratch 79 s words
    (by decide) (by decide) h hs, PoisonOr.value_bind]
  simp [program.bb13, Exit.run, Jump.run, bulkTailBodyEnv,
    Regs.read_nil, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulkTail_backedge_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch : Pointer) (r : Nat) (s : Spec.State) (words : List Word)
    (hlo : 64 ≤ r) (hhi : r < 79)
    (h : BulkTailReady E scratch r s) (hs : TailSchedule mem.mem scratch words) :
    (program g).runFrom E 13 mem =
      (program g).runFrom
        (bulkTailNextEnv (bulkTailBodyEnv E scratch r s
          (constants.toList.getD r 0 + words.getD r 0)) (r + 1)
          (tailRound s (constants.toList.getD r 0 + words.getD r 0))) 13 mem := by
  rw [Func.runFrom_eq]
  change (program.bb13.run program.blockParams E mem >>= fun x =>
    (program g).continue x.1.1 x.1.2 x.2) = _
  rw [bulkTail_backedge E mem scratch r s words hlo hhi h hs]
  rfl

theorem bulkTail_exit_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch : Pointer) (s : Spec.State) (words : List Word)
    (h : BulkTailReady E scratch 79 s) (hs : TailSchedule mem.mem scratch words) :
    (program g).runFrom E 13 mem =
      (program g).runFrom (bulkTailBodyEnv E scratch 79 s
        (constants.toList.getD 79 0 + words.getD 79 0)) 14 mem := by
  rw [Func.runFrom_eq]
  change (program.bb13.run program.blockParams E mem >>= fun x =>
    (program g).continue x.1.1 x.1.2 x.2) = _
  rw [bulkTail_exit E mem scratch s words h hs]
  rfl

end Agave.Ed25519.SHA512.Execution.Avx2
