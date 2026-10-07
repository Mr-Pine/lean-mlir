import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Cutpoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytes
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BytesEq
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Field
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! Exact one-instruction segments for the interleaved sqrt_ratio_i calls.
Every call is bound to its imported implementation. Registers and complete
post-states are explicit; there are no primitive-result hypotheses. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
attribute [local irreducible] SerialFieldMul.machine ToBytes.machine

def advance (s : GlobalState) (n : Nat) : GlobalState :=
  {s with alloc := ⟨s.alloc.nextFreeBlock + n⟩}

def serialize (s : GlobalState) (out input : Pointer) : GlobalState :=
  {s with mem := ToBytes.storeBytes s.mem out (ToBytes.machine (readLimbs s input))}

def multiply (s : GlobalState) (out a b : Pointer) : GlobalState :=
  {s with mem := storeLimbs s.mem out (machine (readLimbs s a) (readLimbs s b))}

def comparison (s : GlobalState) (a b : Pointer) : BitVec 8 :=
  if s.mem.readAt a 256 = s.mem.readAt b 256 then 1#8 else 0#8

theorem advance_wf (s : GlobalState) (n : Nat) (hwf : s.WF) : (advance s n).WF :=
  hwf.add_blocks

theorem segment_append (f : Func) (block : Fin f.n) (first n m : Nat)
    (E : ⟪f.Γ⟫) :
    Cutpoint.segment f block first (n + m) E = (do
      let F ← Cutpoint.segment f block first n E
      Cutpoint.segment f block (first + n) m F) := by
  unfold Cutpoint.segment
  rw [List.take_add, List.foldlM_append]
  simp only [List.drop_drop]

theorem toBytes_306 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out input : Pointer) (hwf : s.WF)
    (hout : SmallRange s.mem out 32) (hin : SmallRange s.mem input 40)
    (h0 : E.read (%66) = .value out) (h1 : E.read (%arg1) = .value input) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 306 1 E s =
      .value (E, serialize s out input) := by
  have hc := ToBytes.program_call out input s hwf hout hin
  simp only [ToBytes.program.args] at hc
  change ((do
    let returnedValues ← sqrtRatioPrimitives.toBytes
      (.cons (E.read (%66)) (.cons (E.read (%arg1)) .nil))
    pure (E.writeMany .nil returnedValues)) >>= pure) s = _
  simp only [h0, h1, sqrtRatioPrimitives, EffectM.bind_eq, EffectM.pure_eq]
  rw [hc]
  rfl

theorem bytesEq_307 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (a b : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32)
    (h0 : E.read (%67) = .value a) (h1 : E.read (%66) = .value b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 307 1 E s =
      .value (E[%236 := .value (comparison s a b)], advance s 33) := by
  have hc := BytesEq.program_exact a b s hwf ha hb
  simp only [BytesEq.program.args] at hc
  change ((do
    let returnedValues ← sqrtRatioPrimitives.bytesEq
      (.cons (E.read (%67)) (.cons (E.read (%66)) .nil))
    pure (E.writeMany (.cons (%236) .nil) returnedValues)) >>= pure) s = _
  simp only [h0, h1, sqrtRatioPrimitives, EffectM.bind_eq, EffectM.pure_eq]
  rw [hc]
  rfl

theorem bytesEq_569 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (a b : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32)
    (h0 : E.read (%65) = .value a) (h1 : E.read (%64) = .value b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 569 1 E s =
      .value (E[%430 := .value (comparison s a b)], advance s 33) := by
  have hc := BytesEq.program_exact a b s hwf ha hb
  simp only [BytesEq.program.args] at hc
  change ((do
    let returnedValues ← sqrtRatioPrimitives.bytesEq
      (.cons (E.read (%65)) (.cons (E.read (%64)) .nil))
    pure (E.writeMany (.cons (%430) .nil) returnedValues)) >>= pure) s = _
  simp only [h0, h1, sqrtRatioPrimitives, EffectM.bind_eq, EffectM.pure_eq]
  rw [hc]
  rfl

theorem bytesEq_947 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (a b : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32)
    (h0 : E.read (%63) = .value a) (h1 : E.read (%62) = .value b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 947 1 E s =
      .value (E[%731 := .value (comparison s a b)], advance s 33) := by
  have hc := BytesEq.program_exact a b s hwf ha hb
  simp only [BytesEq.program.args] at hc
  change ((do
    let returnedValues ← sqrtRatioPrimitives.bytesEq
      (.cons (E.read (%63)) (.cons (E.read (%62)) .nil))
    pure (E.writeMany (.cons (%731) .nil) returnedValues)) >>= pure) s = _
  simp only [h0, h1, sqrtRatioPrimitives, EffectM.bind_eq, EffectM.pure_eq]
  rw [hc]
  rfl

theorem mul_576 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out a b : Pointer) (hwf : s.WF)
    (ho : SmallRange s.mem out 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%73) = .value out) (h1 : E.read (%72) = .value a)
    (h2 : E.read (%52) = .value b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 576 1 E s =
      .value (E, multiply s out a b) := by
  have hc := SerialFieldMul.kernel_call out a b s hwf ho ha hb
  simp only [SerialFieldMul.kernel.args] at hc
  change ((do
    let returnedValues ← sqrtRatioPrimitives.mul
      (.cons (E.read (%73)) (.cons (E.read (%72)) (.cons (E.read (%52)) .nil)))
    pure (E.writeMany .nil returnedValues)) >>= pure) s = _
  simp only [h0, h1, h2, sqrtRatioPrimitives, EffectM.bind_eq, EffectM.pure_eq]
  rw [hc]
  rfl

theorem mul_953 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out a b : Pointer) (hwf : s.WF)
    (ho : SmallRange s.mem out 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%71) = .value out) (h1 : E.read (%52) = .value a)
    (h2 : E.read (%79) = .value b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 953 1 E s =
      .value (E, multiply s out a b) := by
  have hc := SerialFieldMul.kernel_call out a b s hwf ho ha hb
  simp only [SerialFieldMul.kernel.args] at hc
  change ((do
    let returnedValues ← sqrtRatioPrimitives.mul
      (.cons (E.read (%71)) (.cons (E.read (%52)) (.cons (E.read (%79)) .nil)))
    pure (E.writeMany .nil returnedValues)) >>= pure) s = _
  simp only [h0, h1, h2, sqrtRatioPrimitives, EffectM.bind_eq, EffectM.pure_eq]
  rw [hc]
  rfl

theorem blackBox_955 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (byte : BitVec 8) (hwf : s.WF)
    (h0 : E.read (%732) = .value byte) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 955 1 E s =
      .value (E[%733 := .value byte], advance s 1) := by
  have hc := BlackBox.program_call byte s hwf
  simp only [BlackBox.program.args] at hc
  change ((do
    let returnedValues ← sqrtRatioPrimitives.blackBoxByte (.cons (E.read (%732)) .nil)
    pure (E.writeMany (.cons (%733) .nil) returnedValues)) >>= pure) s = _
  simp only [h0, sqrtRatioPrimitives, EffectM.bind_eq, EffectM.pure_eq]
  rw [hc]
  rfl

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers
