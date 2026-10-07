import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkStore
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairFrame

/-! The exact second feed-forward and pair-loop backedge of bb16. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- Chaining state and cursor/count at the real two-block header. -/
structure BulkOuterReady (E : Env program.Γ) (s : Spec.State)
    (index pairs : BitVec 64) : Prop where
  a : E.read (%357) = .value s.a
  b : E.read (%356) = .value s.b
  c : E.read (%355) = .value s.c
  d : E.read (%354) = .value s.d
  e : E.read (%353) = .value s.e
  f : E.read (%352) = .value s.f
  g : E.read (%351) = .value s.g
  h : E.read (%350) = .value s.h
  index : E.read (%358) = .value index
  pairs : E.read (%359) = .value pairs

/-- First-block feed-forward and the second block's final working state. -/
structure BulkAdvanceReady (E : Env program.Γ) (first final : Spec.State)
    (index pairs : BitVec 64) : Prop where
  firstA : E.read (%610) = .value first.a
  firstB : E.read (%611) = .value first.b
  firstC : E.read (%612) = .value first.c
  firstD : E.read (%613) = .value first.d
  firstE : E.read (%614) = .value first.e
  firstF : E.read (%615) = .value first.f
  firstG : E.read (%616) = .value first.g
  firstH : E.read (%617) = .value first.h
  finalA : E.read (%651) = .value final.a
  finalB : E.read (%623) = .value final.b
  finalC : E.read (%624) = .value final.c
  finalD : E.read (%625) = .value final.d
  finalE : E.read (%652) = .value final.e
  finalF : E.read (%620) = .value final.f
  finalG : E.read (%622) = .value final.g
  finalH : E.read (%621) = .value final.h
  index : E.read (%358) = .value index
  pairs : E.read (%359) = .value pairs
  two : E.read (%42) = .value 2#64
  minusOne : E.read (%80) = .value 18446744073709551615#64
  zero : E.read (%2) = .value 0#64

def bulkAdvanceEnv (E : Env program.Γ) (s : Spec.State)
    (index pairs : BitVec 64) : Env program.Γ :=
  E[%654 := .value s.a,
    %655 := .value s.b,
    %656 := .value s.c,
    %657 := .value s.d,
    %658 := .value s.e,
    %659 := .value s.f,
    %660 := .value s.g,
    %661 := .value s.h,
    %662 := .value (index + 2#64),
    %663 := .value (pairs + 18446744073709551615#64),
    %664 := .value (BitVec.ofBool (pairs + 18446744073709551615#64 == 0#64))]

def bulkNextEnv (E : Env program.Γ) : Env program.Γ :=
  E[%350 := E.read (%661), %351 := E.read (%660), %352 := E.read (%659), %353 := E.read (%658), %354 := E.read (%657), %355 := E.read (%656), %356 := E.read (%655), %357 := E.read (%654),
    %358 := E.read (%662), %359 := E.read (%663)]

@[simp] theorem bulk_params9 : program.blockParams 9 =
  .cons (%350) (.cons (%351) (.cons (%352) (.cons (%353) (.cons (%354) (.cons (%355) (.cons (%356) (.cons (%357) (.cons (%358) (.cons (%359) (.nil)))))))))) := rfl

@[simp] theorem bulk_params17 : program.blockParams 17 = .nil := rfl

theorem bulk_advance_body (E : Env program.Γ) (mem : GlobalState)
    (first final : Spec.State) (index pairs : BitVec 64)
    (h : BulkAdvanceReady E first final index pairs) :
    List.foldlM Instr.run E program.bb16.body mem =
      .value (bulkAdvanceEnv E (Spec.feedForward first final) index pairs, mem) := by
  simp [program.bb16, List.foldlM_cons, List.foldlM_nil, Instr.run, bulkAdvanceEnv,
    Spec.feedForward, BinOp.compute, Operation.add, Operation.icmp, BitVec.add_comm,
    h.firstA, h.firstB, h.firstC, h.firstD,
    h.firstE, h.firstF, h.firstG, h.firstH,
    h.finalA, h.finalB, h.finalC, h.finalD,
    h.finalE, h.finalF, h.finalG, h.finalH,
    h.index, h.pairs, h.two, h.minusOne, h.zero,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_advance_exit (E : Env program.Γ) (mem : GlobalState)
    (first final : Spec.State) (index : BitVec 64)
    (h : BulkAdvanceReady E first final index 1#64) :
    program.bb16.run program.blockParams E mem =
      .value ((bulkAdvanceEnv E (Spec.feedForward first final) index 1#64, .inr 17), mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq, bulk_advance_body E mem first final index 1#64 h,
    PoisonOr.value_bind]
  simp [program.bb16, bulkAdvanceEnv, Exit.run, Jump.run, Regs.read_nil,
    Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_advance_backedge (E : Env program.Γ) (mem : GlobalState)
    (first final : Spec.State) (index pairs : BitVec 64)
    (h : BulkAdvanceReady E first final index pairs)
    (hmore : pairs + 18446744073709551615#64 ≠ 0#64) :
    program.bb16.run program.blockParams E mem =
      .value ((bulkNextEnv (bulkAdvanceEnv E (Spec.feedForward first final) index pairs),
        .inr 9), mem) := by
  have hn : (pairs + 18446744073709551615#64 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hmore
  simp only [BasicBlock.run, EffectM.bind_eq, bulk_advance_body E mem first final index pairs h,
    PoisonOr.value_bind]
  simp [program.bb16, bulkAdvanceEnv, bulkNextEnv, hn, Exit.run, Jump.run,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_advance_ready (E : Env program.Γ) (s : Spec.State) (index pairs : BitVec 64) :
    BulkOuterReady (bulkNextEnv (bulkAdvanceEnv E s index pairs)) s
      (index + 2#64) (pairs + 18446744073709551615#64) := by
  constructor <;> simp [bulkNextEnv, bulkAdvanceEnv, mlir_env]

theorem bulkAdvanceEnv_frame (E : Env program.Γ) (s : Spec.State) (index pairs : BitVec 64) :
    RegFrame 654 664 E (bulkAdvanceEnv E s index pairs) := by
  unfold bulkAdvanceEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem bulkNextEnv_frame (E : Env program.Γ) :
    RegFrame 350 359 E (bulkNextEnv E) := by
  unfold bulkNextEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

/-- All eight chain pointers survive the body; its eight results are precisely
the final chaining value to be stored by bb17. -/
theorem bulk_advance_store_ready (E : Env program.Γ) (chain : Pointer)
    (s : Spec.State) (index pairs : BitVec 64) (h : BulkChainPointers E chain) :
    BulkStoreReady (bulkAdvanceEnv E s index pairs) chain s := by
  have hf := bulkAdvanceEnv_frame E s index pairs
  constructor
  · exact (hf.read (%arg0)).trans h.ptr
  · exact (hf.read (%335)).trans h.p1
  · exact (hf.read (%336)).trans h.p2
  · exact (hf.read (%337)).trans h.p3
  · exact (hf.read (%338)).trans h.p4
  · exact (hf.read (%339)).trans h.p5
  · exact (hf.read (%340)).trans h.p6
  · exact (hf.read (%341)).trans h.p7
  · simp [bulkAdvanceEnv, mlir_env]
  · simp [bulkAdvanceEnv, mlir_env]
  · simp [bulkAdvanceEnv, mlir_env]
  · simp [bulkAdvanceEnv, mlir_env]
  · simp [bulkAdvanceEnv, mlir_env]
  · simp [bulkAdvanceEnv, mlir_env]
  · simp [bulkAdvanceEnv, mlir_env]
  · simp [bulkAdvanceEnv, mlir_env]

end Agave.Ed25519.SHA512.Execution.Avx2
