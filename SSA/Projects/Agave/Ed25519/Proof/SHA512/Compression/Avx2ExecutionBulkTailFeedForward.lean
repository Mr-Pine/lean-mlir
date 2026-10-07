import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkTailTrace

/-! The actual bb14 feed-forward remains in registers. It preserves all
memory, saves the first compressed state in %610..617, and simultaneously
initializes the second block's bb15 working state at byte offset zero. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- Chaining words retained across the first block's round loop. -/
structure BulkTailFeedForwardReady (E : Env program.Γ) (initial : Spec.State) : Prop where
  a : E.read (%357) = .value initial.a
  b : E.read (%356) = .value initial.b
  c : E.read (%355) = .value initial.c
  d : E.read (%354) = .value initial.d
  e : E.read (%353) = .value initial.e
  f : E.read (%352) = .value initial.f
  g : E.read (%351) = .value initial.g
  h : E.read (%350) = .value initial.h
  zero : E.read (%2) = .value 0#64

/-- The saved chaining state consumed by bb16 after the second block. -/
structure BulkTailFeedForwardFinalReady (E : Env program.Γ) (s : Spec.State) : Prop where
  a : E.read (%610) = .value s.a
  b : E.read (%611) = .value s.b
  c : E.read (%612) = .value s.c
  d : E.read (%613) = .value s.d
  e : E.read (%614) = .value s.e
  f : E.read (%615) = .value s.f
  g : E.read (%616) = .value s.g
  h : E.read (%617) = .value s.h

/-- Exact eight bb14 destinations in source order. -/
def bulkTailFeedForwardEnv (E : Env program.Γ) (initial final : Spec.State) : Env program.Γ :=
  E[%610 := .value (final.a + initial.a), %611 := .value (final.b + initial.b),
    %612 := .value (final.c + initial.c), %613 := .value (final.d + initial.d),
    %614 := .value (final.e + initial.e), %615 := .value (final.f + initial.f),
    %616 := .value (final.g + initial.g), %617 := .value (final.h + initial.h)]

/-- The exact bb14 branch argument assignment to bb15. -/
def bulkTailFeedForwardNextEnv (E : Env program.Γ) (initial final : Spec.State) : Env program.Γ :=
  let s := Spec.feedForward initial final
  (bulkTailFeedForwardEnv E initial final)[%618 := .value 0#64,
    %619 := .value s.h, %620 := .value s.e, %621 := .value s.g,
    %622 := .value s.f, %623 := .value s.a, %624 := .value s.b,
    %625 := .value s.c, %626 := .value s.d]

@[simp] theorem bulkTail_params15 : program.blockParams 15 =
    .cons (%618) (.cons (%619) (.cons (%620) (.cons (%621) (.cons (%622)
      (.cons (%623) (.cons (%624) (.cons (%625) (.cons (%626) .nil)))))))) := rfl

theorem BulkTailFeedForwardReady.of_frame {E E' : Env program.Γ} {initial : Spec.State}
    (h : BulkTailFeedForwardReady E initial) (hf : BulkTailFrame E E') :
    BulkTailFeedForwardReady E' initial := by
  constructor
  · exact (hf.read (%357)).trans h.a
  · exact (hf.read (%356)).trans h.b
  · exact (hf.read (%355)).trans h.c
  · exact (hf.read (%354)).trans h.d
  · exact (hf.read (%353)).trans h.e
  · exact (hf.read (%352)).trans h.f
  · exact (hf.read (%351)).trans h.g
  · exact (hf.read (%350)).trans h.h
  · exact (hf.read (%2)).trans h.zero

theorem bulkTailFeedForwardNextEnv_frame (E : Env program.Γ) (initial final : Spec.State) :
    RegFrame 610 626 E (bulkTailFeedForwardNextEnv E initial final) := by
  unfold bulkTailFeedForwardNextEnv bulkTailFeedForwardEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem bulkTailFeedForward_final_ready (E : Env program.Γ) (initial final : Spec.State) :
    BulkTailFeedForwardFinalReady (bulkTailFeedForwardNextEnv E initial final)
      (Spec.feedForward initial final) := by
  constructor <;>
    simp [bulkTailFeedForwardNextEnv, bulkTailFeedForwardEnv, Spec.feedForward,
      BitVec.add_comm, mlir_env]

/-- Successful execution of all eight feed-forward additions, with unchanged
GlobalState and without any memory premise. -/
theorem bulkTailFeedForward_body (E : Env program.Γ) (mem : GlobalState)
    (initial final : Spec.State) (h : BulkTailFeedForwardReady E initial)
    (hf : BulkTailFinalReady E final) :
    List.foldlM Instr.run E program.bb14.body mem =
      .value (bulkTailFeedForwardEnv E initial final, mem) := by
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb14, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bulkTailFeedForwardEnv, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h,
    hf.a, hf.b, hf.c, hf.d, hf.e, hf.f, hf.g, hf.h, hadd, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

/-- The imported bb14 edge initializes bb15 with the first block's standard
feed-forward state; all modeled memory and allocation state are unchanged. -/
theorem bulkTailFeedForward_block (E : Env program.Γ) (mem : GlobalState)
    (initial final : Spec.State) (h : BulkTailFeedForwardReady E initial)
    (hf : BulkTailFinalReady E final) :
    program.bb14.run program.blockParams E mem =
      .value ((bulkTailFeedForwardNextEnv E initial final, .inr 15), mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulkTailFeedForward_body E mem initial final h hf, PoisonOr.value_bind]
  simp [program.bb14, Exit.run, Jump.run, bulkTailFeedForwardEnv,
    bulkTailFeedForwardNextEnv, h.zero, Spec.feedForward, BitVec.add_comm,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulkTailFeedForward_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (initial final : Spec.State) (h : BulkTailFeedForwardReady E initial)
    (hf : BulkTailFinalReady E final) :
    (program g).runFrom E 14 mem =
      (program g).runFrom (bulkTailFeedForwardNextEnv E initial final) 15 mem := by
  rw [Func.runFrom_eq]
  change (program.bb14.run program.blockParams E mem >>= fun x =>
    (program g).continue x.1.1 x.1.2 x.2) = _
  rw [bulkTailFeedForward_block E mem initial final h hf]
  rfl

/-- The first block's concrete last sixteen rounds and feed-forward form a
17-edge trace into bb15, preserving memory and every register outside 573..626. -/
theorem bulkTail_feedForward (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch : Pointer) (initial : Spec.State) (block : Agave.Ed25519.Bridge.Challenge.Bytes)
    (hs : TailSchedule mem.mem scratch (schedule block))
    (ht : BulkTailReady E scratch 64 (roundsFrom initial (schedule block) 0 64))
    (hf : BulkTailFeedForwardReady E initial) :
    ∃ E', ExecTrace (program g) 17 E 13 mem E' 15 mem ∧
      BulkTailFeedForwardFinalReady E' (compressBlock initial block) ∧
      RegFrame 573 626 E E' := by
  obtain ⟨E₁, htrace, hfinal, hframe⟩ :=
    bulkTail_sixteen_from_prefix g mem scratch (schedule block) E initial hs ht
  refine ⟨bulkTailFeedForwardNextEnv E₁ initial (roundsFrom initial (schedule block) 0 80),
    htrace.trans (ExecTrace.single
      (bulkTailFeedForward_block E₁ mem initial _ (hf.of_frame hframe) hfinal)),
    bulkTailFeedForward_final_ready E₁ initial _, ?_⟩
  exact (hframe.enlarge (by decide) (by decide)).trans
    ((bulkTailFeedForwardNextEnv_frame E₁ initial _).enlarge (by decide) (by decide))

end Agave.Ed25519.SHA512.Execution.Avx2
