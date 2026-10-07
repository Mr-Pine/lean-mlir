import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityPhases
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.Linked
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekBytePrimitives

/-! Close both actual byte-comparison phases with the independently imported
32-byte helper. Their only premises are live serialized buffers and the
call-site register values; the comparison result and read-only frame follow. -/
namespace Agave.Ed25519.SmallOrder.Execution.EqualityPhases
open LeanMLIR.RIR Verifier.Execution.PointConstantTimeEq
open Verifier.Execution.Dalek (ReadBytes ReadOnlyFrame args2 choiceByte)
set_option maxRecDepth 16000

theorem compareX_exact (p : Primitives) : compareX p =
    [.call p.bytesConstantTimeEq (.cons (%50) (.cons (%49) .nil))
      (.cons (%361) .nil),
     .lifetimeEnd (%49) 32, .lifetimeEnd (%50) 32] := rfl

theorem compareX_run (p : Primitives) (E : Env program.Γ)
    (s t : GlobalState) (left right : Pointer) (result : BitVec 8)
    (hl : E.read (%50) = .value left) (hr : E.read (%49) = .value right)
    (hc : p.bytesConstantTimeEq (args2 left right) s =
      .value (.cons (.value result) .nil, t)) :
    List.foldlM Instr.run E (compareX p) s =
      .value (E[%361 := .value result], t) := by
  simp only [args2] at hc
  simp [compareX_exact, List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    args2, hl, hr, hc]

/-- Concrete exact-helper specialization, including private allocation effects. -/
theorem linked_compareX_run (E : Env program.Γ) (s : GlobalState)
    (left right : Pointer) (a b : BitVec 256) (hwf : s.WF)
    (hl : E.read (%50) = .value left) (hr : E.read (%49) = .value right)
    (ha : ReadBytes s left 32 a) (hb : ReadBytes s right 32 b) :
    ∃ t, List.foldlM Instr.run E (compareX equalityPrimitives) s =
      .value (E[%361 := .value (choiceByte (decide (a = b)))], t) ∧
      ReadOnlyFrame s t := by
  obtain ⟨t, hc, hf⟩ := Verifier.Execution.Dalek.BytePrimitives.bytesEq_contract
    left right s a b hwf ha hb
  refine ⟨t, ?_, hf⟩
  apply compareX_run equalityPrimitives E s t left right _ hl hr
  simpa [equalityPrimitives, choiceByte] using hc

theorem compareY_exact (p : Primitives) : compareY p =
    [.call p.bytesConstantTimeEq (.cons (%48) (.cons (%47) .nil))
      (.cons (%668) .nil),
     .lifetimeEnd (%47) 32, .lifetimeEnd (%48) 32] := rfl

theorem compareY_run (p : Primitives) (E : Env program.Γ)
    (s t : GlobalState) (left right : Pointer) (result : BitVec 8)
    (hl : E.read (%48) = .value left) (hr : E.read (%47) = .value right)
    (hc : p.bytesConstantTimeEq (args2 left right) s =
      .value (.cons (.value result) .nil, t)) :
    List.foldlM Instr.run E (compareY p) s =
      .value (E[%668 := .value result], t) := by
  simp only [args2] at hc
  simp [compareY_exact, List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    args2, hl, hr, hc]

/-- Concrete exact-helper specialization, including private allocation effects. -/
theorem linked_compareY_run (E : Env program.Γ) (s : GlobalState)
    (left right : Pointer) (a b : BitVec 256) (hwf : s.WF)
    (hl : E.read (%48) = .value left) (hr : E.read (%47) = .value right)
    (ha : ReadBytes s left 32 a) (hb : ReadBytes s right 32 b) :
    ∃ t, List.foldlM Instr.run E (compareY equalityPrimitives) s =
      .value (E[%668 := .value (choiceByte (decide (a = b)))], t) ∧
      ReadOnlyFrame s t := by
  obtain ⟨t, hc, hf⟩ := Verifier.Execution.Dalek.BytePrimitives.bytesEq_contract
    left right s a b hwf ha hb
  refine ⟨t, ?_, hf⟩
  apply compareY_run equalityPrimitives E s t left right _ hl hr
  simpa [equalityPrimitives, choiceByte] using hc

end Agave.Ed25519.SmallOrder.Execution.EqualityPhases
