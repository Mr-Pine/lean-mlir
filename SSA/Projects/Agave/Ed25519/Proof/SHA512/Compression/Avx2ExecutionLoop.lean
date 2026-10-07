import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2Execution

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

@[simp] theorem tail_params6 : program.blockParams 6 =
    .cons (%272) (.cons (%273) (.cons (%274) (.cons (%275) (.cons (%276)
      (.cons (%277) (.cons (%278) (.cons (%279) (.cons (%280) .nil)))))))) := rfl

@[simp] theorem tail_params7 : program.blockParams 7 = .nil := rfl

/-- Register interpretation consumed by the imported bb7 feed-forward code. -/
structure TailFinalReady (E : Env program.Γ) (s : Spec.State) : Prop where
  a : E.read (%306) = .value s.a
  b : E.read (%277) = .value s.b
  c : E.read (%278) = .value s.c
  d : E.read (%279) = .value s.d
  e : E.read (%307) = .value s.e
  f : E.read (%274) = .value s.f
  g : E.read (%276) = .value s.g
  h : E.read (%275) = .value s.h

theorem tail_next_ready (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) (h : TailReady E scratch r s) :
    TailReady (tailNextEnv (tailBodyEnv E scratch r s kw) (r + 1) (tailRound s kw))
      scratch (r + 1) (tailRound s kw) := by
  constructor <;> simp [tailNextEnv, tailBodyEnv, mlir_env,
    h.scratch, h.one, h.limit, h.rot14, h.rot18, h.rot41, h.rot28, h.rot34,
    h.rot39, h.mask]

theorem tail_final_ready (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) (h : TailReady E scratch r s) :
    TailFinalReady (tailBodyEnv E scratch r s kw) (tailRound s kw) := by
  constructor <;> simp [tailBodyEnv, tailRound, bigSigma0, bigSigma1, mlir_env,
    h.a, h.b, h.c, h.e, h.f, h.g]

/-- Exact body and terminator, including the actual backedge parameter map. -/
theorem tail_backedge (E : Env program.Γ) (mem : GlobalState) (scratch : Pointer)
    (r : Nat) (s : Spec.State) (words : List Word)
    (hlo : 64 ≤ r) (hhi : r < 79)
    (h : TailReady E scratch r s) (hs : TailSchedule mem.mem scratch words) :
    program.bb6.run program.blockParams E mem =
      .value ((tailNextEnv (tailBodyEnv E scratch r s
          (constants.toList.getD r 0 + words.getD r 0)) (r + 1)
          (tailRound s (constants.toList.getD r 0 + words.getD r 0)), .inr 6), mem) := by
  have hr : r + 1 ≠ 80 := by omega
  simp only [BasicBlock.run, EffectM.bind_eq, tail_body E mem scratch r s words hlo
    (by omega) h hs, PoisonOr.value_bind]
  simp [program.bb6, Exit.run, Jump.run, tailBodyEnv,
    tailNextEnv, tailRound, bigSigma0, bigSigma1, hr,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    h.a, h.b, h.c, h.e, h.f, h.g,
    EffectM.pure_eq, mlir_env, mlir_effect]

/-- Round 79 follows the imported exit to bb7 without rewriting header parameters. -/
theorem tail_exit (E : Env program.Γ) (mem : GlobalState) (scratch : Pointer)
    (s : Spec.State) (words : List Word)
    (h : TailReady E scratch 79 s) (hs : TailSchedule mem.mem scratch words) :
    program.bb6.run program.blockParams E mem =
      .value ((tailBodyEnv E scratch 79 s
          (constants.toList.getD 79 0 + words.getD 79 0), .inr 7), mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq, tail_body E mem scratch 79 s words
    (by decide) (by decide) h hs, PoisonOr.value_bind]
  simp [program.bb6, Exit.run, Jump.run, tailBodyEnv,
    Regs.read_nil, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem tail_backedge_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch : Pointer) (r : Nat) (s : Spec.State) (words : List Word)
    (hlo : 64 ≤ r) (hhi : r < 79)
    (h : TailReady E scratch r s) (hs : TailSchedule mem.mem scratch words) :
    (program g).runFrom E 6 mem =
      (program g).runFrom
        (tailNextEnv (tailBodyEnv E scratch r s
          (constants.toList.getD r 0 + words.getD r 0)) (r + 1)
          (tailRound s (constants.toList.getD r 0 + words.getD r 0))) 6 mem := by
  rw [Func.runFrom_eq]
  change (program.bb6.run program.blockParams E mem >>= fun x =>
    (program g).continue x.1.1 x.1.2 x.2) = _
  rw [tail_backedge E mem scratch r s words hlo hhi h hs]
  rfl

theorem tail_exit_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch : Pointer) (s : Spec.State) (words : List Word)
    (h : TailReady E scratch 79 s) (hs : TailSchedule mem.mem scratch words) :
    (program g).runFrom E 6 mem =
      (program g).runFrom (tailBodyEnv E scratch 79 s
        (constants.toList.getD 79 0 + words.getD 79 0)) 7 mem := by
  rw [Func.runFrom_eq]
  change (program.bb6.run program.blockParams E mem >>= fun x =>
    (program g).continue x.1.1 x.1.2 x.2) = _
  rw [tail_exit E mem scratch s words h hs]
  rfl

end Agave.Ed25519.SHA512.Execution.Avx2
