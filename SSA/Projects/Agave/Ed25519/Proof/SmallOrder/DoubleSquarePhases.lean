import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoublePhases
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.Linked
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareExecution

/-! Exact four square-call slices of the direct imported projective double.
Each executes the actual pow2k(1) body using its established kernel theorem.
No square arithmetic or whole-double call result is assumed. -/
namespace Agave.Ed25519.SmallOrder.Execution.DoublePhases
open LeanMLIR.RIR Verifier.Execution.SmallOrderProjectiveDouble
open SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000

theorem squareX_exact (p : Primitives) : squareX p =
    [.call p.pow2k (.cons (%30) (.cons (%arg1) (.cons (%0) .nil))) .nil] := rfl

theorem squareX_run (E : Env program.Γ) (s : GlobalState) (r a : Pointer)
    (hwf : s.WF) (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hdr : E.read (%30) = .value r) (har : E.read (%arg1) = .value a)
    (hone : E.read (%0) = .value 1#32) :
    List.foldlM Instr.run E (squareX doublePrimitives) s =
      .value (E, {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))}) := by
  have hc := SerialPoint.Execution.square_call r a s hwf hr ha
  change Encoding.Decompress.Execution.Pow2k.program.call
    (.cons (.value r) (.cons (.value a) (.cons (.value 1#32) .nil))) s = _ at hc
  simp [squareX_exact, List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    doublePrimitives, hdr, har, hone, hc]

theorem squareY_exact (p : Primitives) : squareY p =
    [.call p.pow2k (.cons (%29) (.cons (%31) (.cons (%0) .nil))) .nil] := rfl

theorem squareY_run (E : Env program.Γ) (s : GlobalState) (r a : Pointer)
    (hwf : s.WF) (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hdr : E.read (%29) = .value r) (har : E.read (%31) = .value a)
    (hone : E.read (%0) = .value 1#32) :
    List.foldlM Instr.run E (squareY doublePrimitives) s =
      .value (E, {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))}) := by
  have hc := SerialPoint.Execution.square_call r a s hwf hr ha
  change Encoding.Decompress.Execution.Pow2k.program.call
    (.cons (.value r) (.cons (.value a) (.cons (.value 1#32) .nil))) s = _ at hc
  simp [squareY_exact, List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    doublePrimitives, hdr, har, hone, hc]

theorem squareZ_exact (p : Primitives) : squareZ p =
    [.call p.pow2k (.cons (%28) (.cons (%32) (.cons (%0) .nil))) .nil] := rfl

theorem squareZ_run (E : Env program.Γ) (s : GlobalState) (r a : Pointer)
    (hwf : s.WF) (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hdr : E.read (%28) = .value r) (har : E.read (%32) = .value a)
    (hone : E.read (%0) = .value 1#32) :
    List.foldlM Instr.run E (squareZ doublePrimitives) s =
      .value (E, {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))}) := by
  have hc := SerialPoint.Execution.square_call r a s hwf hr ha
  change Encoding.Decompress.Execution.Pow2k.program.call
    (.cons (.value r) (.cons (.value a) (.cons (.value 1#32) .nil))) s = _ at hc
  simp [squareZ_exact, List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    doublePrimitives, hdr, har, hone, hc]

theorem squareSum_exact (p : Primitives) : squareSum p =
    [.call p.pow2k (.cons (%26) (.cons (%27) (.cons (%0) .nil))) .nil] := rfl

theorem squareSum_run (E : Env program.Γ) (s : GlobalState) (r a : Pointer)
    (hwf : s.WF) (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hdr : E.read (%26) = .value r) (har : E.read (%27) = .value a)
    (hone : E.read (%0) = .value 1#32) :
    List.foldlM Instr.run E (squareSum doublePrimitives) s =
      .value (E, {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))}) := by
  have hc := SerialPoint.Execution.square_call r a s hwf hr ha
  change Encoding.Decompress.Execution.Pow2k.program.call
    (.cons (.value r) (.cons (.value a) (.cons (.value 1#32) .nil))) s = _ at hc
  simp [squareSum_exact, List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    doublePrimitives, hdr, har, hone, hc]

end Agave.Ed25519.SmallOrder.Execution.DoublePhases
