import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecodeCalls
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501Calls
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioCalls
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ByteHelpersAudit
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareExecution

/-! Concrete call-cut specializations. These discharge every multiplication,
single square, serialization, byte comparison, and black_box invocation against
the already proved imported helper bodies. No callee-correctness hypothesis is
left in these cut points. Larger pow2k counts, pow22501, and sqrt composition
are separate proof obligations. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 8192

/-- Exact `Decode` invocation of `pow2k` at bb0:73. -/
theorem decode_pow2k_0_73 (g : Decode.Globals) (sqrtGlobals : SqrtRatio.Globals) (E : ⟪Decode.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (h0 : E.read (%34) = .value r)
    (h1 : E.read (%35) = .value a)
    (h2 : E.read (%0) = .value 1#32)
    : Cutpoint.resume (Decode.program (decodePrimitives sqrtGlobals) g) 0 73 E s =
      Cutpoint.resume (Decode.program (decodePrimitives sqrtGlobals) g) 0 74 E
        {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))} := by
  apply Decode.call_0_73 (decodePrimitives sqrtGlobals) g E s _ r a 1#32 h0 h1 h2
  simpa only [decodePrimitives, Pow2k.program.args] using (SerialPoint.Execution.square_call r a s hwf hr ha)

/-- Exact `Decode` invocation of `mul` at bb0:105. -/
theorem decode_mul_0_105 (g : Decode.Globals) (sqrtGlobals : SqrtRatio.Globals) (E : ⟪Decode.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%31) = .value r)
    (h1 : E.read (%34) = .value a)
    (h2 : E.read (%17) = .value b)
    : Cutpoint.resume (Decode.program (decodePrimitives sqrtGlobals) g) 0 105 E s =
      Cutpoint.resume (Decode.program (decodePrimitives sqrtGlobals) g) 0 106 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Decode.call_0_105 (decodePrimitives sqrtGlobals) g E s _ r a b h0 h1 h2
  simpa only [decodePrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Decode` invocation of `blackBoxByte` at bb1:8. -/
theorem decode_blackBoxByte_1_8 (g : Decode.Globals) (sqrtGlobals : SqrtRatio.Globals) (E : ⟪Decode.program.Γ⟫)
    (s : GlobalState) (byte : BitVec 8) (hwf : s.WF)
    (h0 : E.read (%99) = .value byte)
    : Cutpoint.resume (Decode.program (decodePrimitives sqrtGlobals) g) 1 8 E s =
      Cutpoint.resume (Decode.program (decodePrimitives sqrtGlobals) g) 1 9 (E[%100 := .value byte])
        {s with alloc := (s.alloca 1).alloc} := by
  apply Decode.call_1_8 (decodePrimitives sqrtGlobals) g E s _ byte byte h0
  simpa only [decodePrimitives, BlackBox.program.args] using (BlackBox.program_call byte s hwf)

/-- Exact `Decode` invocation of `mul` at bb1:49. -/
theorem decode_mul_1_49 (g : Decode.Globals) (sqrtGlobals : SqrtRatio.Globals) (E : ⟪Decode.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%136) = .value r)
    (h1 : E.read (%39) = .value a)
    (h2 : E.read (%38) = .value b)
    : Cutpoint.resume (Decode.program (decodePrimitives sqrtGlobals) g) 1 49 E s =
      Cutpoint.resume (Decode.program (decodePrimitives sqrtGlobals) g) 1 50 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Decode.call_1_49 (decodePrimitives sqrtGlobals) g E s _ r a b h0 h1 h2
  simpa only [decodePrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `pow2k` at bb0:28. -/
theorem pow22501_pow2k_0_28 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (h0 : E.read (%26) = .value r)
    (h1 : E.read (%arg1) = .value a)
    (h2 : E.read (%0) = .value 1#32)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 28 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 29 E
        {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))} := by
  apply Pow22501.call_0_28 pow22501Primitives E s _ r a 1#32 h0 h1 h2
  simpa only [pow22501Primitives, Pow2k.program.args] using (SerialPoint.Execution.square_call r a s hwf hr ha)

/-- Exact `Pow22501` invocation of `pow2k` at bb0:31. -/
theorem pow22501_pow2k_0_31 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (h0 : E.read (%24) = .value r)
    (h1 : E.read (%26) = .value a)
    (h2 : E.read (%0) = .value 1#32)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 31 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 32 E
        {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))} := by
  apply Pow22501.call_0_31 pow22501Primitives E s _ r a 1#32 h0 h1 h2
  simpa only [pow22501Primitives, Pow2k.program.args] using (SerialPoint.Execution.square_call r a s hwf hr ha)

/-- Exact `Pow22501` invocation of `pow2k` at bb0:32. -/
theorem pow22501_pow2k_0_32 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (h0 : E.read (%25) = .value r)
    (h1 : E.read (%24) = .value a)
    (h2 : E.read (%0) = .value 1#32)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 32 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 33 E
        {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))} := by
  apply Pow22501.call_0_32 pow22501Primitives E s _ r a 1#32 h0 h1 h2
  simpa only [pow22501Primitives, Pow2k.program.args] using (SerialPoint.Execution.square_call r a s hwf hr ha)

/-- Exact `Pow22501` invocation of `mul` at bb0:35. -/
theorem pow22501_mul_0_35 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%23) = .value r)
    (h1 : E.read (%arg1) = .value a)
    (h2 : E.read (%25) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 35 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 36 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_35 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `mul` at bb0:37. -/
theorem pow22501_mul_0_37 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%22) = .value r)
    (h1 : E.read (%26) = .value a)
    (h2 : E.read (%23) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 37 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 38 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_37 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `pow2k` at bb0:39. -/
theorem pow22501_pow2k_0_39 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (h0 : E.read (%21) = .value r)
    (h1 : E.read (%22) = .value a)
    (h2 : E.read (%0) = .value 1#32)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 39 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 40 E
        {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))} := by
  apply Pow22501.call_0_39 pow22501Primitives E s _ r a 1#32 h0 h1 h2
  simpa only [pow22501Primitives, Pow2k.program.args] using (SerialPoint.Execution.square_call r a s hwf hr ha)

/-- Exact `Pow22501` invocation of `mul` at bb0:41. -/
theorem pow22501_mul_0_41 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%20) = .value r)
    (h1 : E.read (%23) = .value a)
    (h2 : E.read (%21) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 41 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 42 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_41 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `mul` at bb0:45. -/
theorem pow22501_mul_0_45 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%18) = .value r)
    (h1 : E.read (%19) = .value a)
    (h2 : E.read (%20) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 45 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 46 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_45 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `mul` at bb0:49. -/
theorem pow22501_mul_0_49 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%16) = .value r)
    (h1 : E.read (%17) = .value a)
    (h2 : E.read (%18) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 49 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 50 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_49 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `mul` at bb0:53. -/
theorem pow22501_mul_0_53 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%14) = .value r)
    (h1 : E.read (%15) = .value a)
    (h2 : E.read (%16) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 53 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 54 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_53 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `mul` at bb0:57. -/
theorem pow22501_mul_0_57 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%12) = .value r)
    (h1 : E.read (%13) = .value a)
    (h2 : E.read (%18) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 57 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 58 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_57 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `mul` at bb0:61. -/
theorem pow22501_mul_0_61 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%10) = .value r)
    (h1 : E.read (%11) = .value a)
    (h2 : E.read (%12) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 61 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 62 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_61 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `mul` at bb0:65. -/
theorem pow22501_mul_0_65 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%8) = .value r)
    (h1 : E.read (%9) = .value a)
    (h2 : E.read (%10) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 65 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 66 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_65 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `Pow22501` invocation of `mul` at bb0:68. -/
theorem pow22501_mul_0_68 (E : ⟪Pow22501.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%arg0) = .value r)
    (h1 : E.read (%7) = .value a)
    (h2 : E.read (%12) = .value b)
    : Cutpoint.resume (Pow22501.program pow22501Primitives) 0 68 E s =
      Cutpoint.resume (Pow22501.program pow22501Primitives) 0 69 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply Pow22501.call_0_68 pow22501Primitives E s _ r a b h0 h1 h2
  simpa only [pow22501Primitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `pow2k` at bb0:86. -/
theorem sqrtratio_pow2k_0_86 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (h0 : E.read (%82) = .value r)
    (h1 : E.read (%arg2) = .value a)
    (h2 : E.read (%0) = .value 1#32)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 86 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 87 E
        {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))} := by
  apply SqrtRatio.call_0_86 sqrtRatioPrimitives g E s _ r a 1#32 h0 h1 h2
  simpa only [sqrtRatioPrimitives, Pow2k.program.args] using (SerialPoint.Execution.square_call r a s hwf hr ha)

/-- Exact `SqrtRatio` invocation of `mul` at bb0:87. -/
theorem sqrtratio_mul_0_87 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%83) = .value r)
    (h1 : E.read (%82) = .value a)
    (h2 : E.read (%arg2) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 87 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 88 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply SqrtRatio.call_0_87 sqrtRatioPrimitives g E s _ r a b h0 h1 h2
  simpa only [sqrtRatioPrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `pow2k` at bb0:91. -/
theorem sqrtratio_pow2k_0_91 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (h0 : E.read (%80) = .value r)
    (h1 : E.read (%83) = .value a)
    (h2 : E.read (%0) = .value 1#32)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 91 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 92 E
        {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))} := by
  apply SqrtRatio.call_0_91 sqrtRatioPrimitives g E s _ r a 1#32 h0 h1 h2
  simpa only [sqrtRatioPrimitives, Pow2k.program.args] using (SerialPoint.Execution.square_call r a s hwf hr ha)

/-- Exact `SqrtRatio` invocation of `mul` at bb0:92. -/
theorem sqrtratio_mul_0_92 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%81) = .value r)
    (h1 : E.read (%80) = .value a)
    (h2 : E.read (%arg2) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 92 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 93 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply SqrtRatio.call_0_92 sqrtRatioPrimitives g E s _ r a b h0 h1 h2
  simpa only [sqrtRatioPrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `mul` at bb0:95. -/
theorem sqrtratio_mul_0_95 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%78) = .value r)
    (h1 : E.read (%arg1) = .value a)
    (h2 : E.read (%83) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 95 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 96 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply SqrtRatio.call_0_95 sqrtRatioPrimitives g E s _ r a b h0 h1 h2
  simpa only [sqrtRatioPrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `mul` at bb0:98. -/
theorem sqrtratio_mul_0_98 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%76) = .value r)
    (h1 : E.read (%arg1) = .value a)
    (h2 : E.read (%81) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 98 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 99 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply SqrtRatio.call_0_98 sqrtRatioPrimitives g E s _ r a b h0 h1 h2
  simpa only [sqrtRatioPrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `mul` at bb0:106. -/
theorem sqrtratio_mul_0_106 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%77) = .value r)
    (h1 : E.read (%76) = .value a)
    (h2 : E.read (%68) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 106 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 107 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply SqrtRatio.call_0_106 sqrtRatioPrimitives g E s _ r a b h0 h1 h2
  simpa only [sqrtRatioPrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `mul` at bb0:109. -/
theorem sqrtratio_mul_0_109 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%79) = .value r)
    (h1 : E.read (%78) = .value a)
    (h2 : E.read (%77) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 109 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 110 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply SqrtRatio.call_0_109 sqrtRatioPrimitives g E s _ r a b h0 h1 h2
  simpa only [sqrtRatioPrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `pow2k` at bb0:115. -/
theorem sqrtratio_pow2k_0_115 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (h0 : E.read (%74) = .value r)
    (h1 : E.read (%79) = .value a)
    (h2 : E.read (%0) = .value 1#32)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 115 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 116 E
        {s with mem := storeLimbs s.mem r (SerialPoint.squareMachine (readLimbs s a))} := by
  apply SqrtRatio.call_0_115 sqrtRatioPrimitives g E s _ r a 1#32 h0 h1 h2
  simpa only [sqrtRatioPrimitives, Pow2k.program.args] using (SerialPoint.Execution.square_call r a s hwf hr ha)

/-- Exact `SqrtRatio` invocation of `mul` at bb0:116. -/
theorem sqrtratio_mul_0_116 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%75) = .value r)
    (h1 : E.read (%arg2) = .value a)
    (h2 : E.read (%74) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 116 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 117 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply SqrtRatio.call_0_116 sqrtRatioPrimitives g E s _ r a b h0 h1 h2
  simpa only [sqrtRatioPrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `toBytes` at bb0:306. -/
theorem sqrtratio_toBytes_0_306 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 32) (ha : SmallRange s.mem a 40)
    (h0 : E.read (%66) = .value r)
    (h1 : E.read (%arg1) = .value a)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 306 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 307 E
        {s with mem := ToBytes.storeBytes s.mem r (ToBytes.machine (readLimbs s a))} := by
  apply SqrtRatio.call_0_306 sqrtRatioPrimitives g E s _ r a h0 h1
  simpa only [sqrtRatioPrimitives, ToBytes.program.args] using (ToBytes.program_call r a s hwf hr ha)

/-- Exact `SqrtRatio` invocation of `bytesEq` at bb0:307. -/
theorem sqrtratio_bytesEq_0_307 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (a b : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32)
    (h0 : E.read (%67) = .value a)
    (h1 : E.read (%66) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 307 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 308 (E[%236 := .value (if s.mem.readAt a 256 = s.mem.readAt b 256 then 1#8 else 0#8)])
        {s with alloc := ⟨s.alloc.nextFreeBlock + 33⟩} := by
  apply SqrtRatio.call_0_307 sqrtRatioPrimitives g E s _ a b (if s.mem.readAt a 256 = s.mem.readAt b 256 then 1#8 else 0#8) h0 h1
  simpa only [sqrtRatioPrimitives, BytesEq.program.args, BitVec.ofNat_eq_ofNat] using
    (BytesEq.program_exact a b s hwf ha hb)

/-- Exact `SqrtRatio` invocation of `bytesEq` at bb0:569. -/
theorem sqrtratio_bytesEq_0_569 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (a b : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32)
    (h0 : E.read (%65) = .value a)
    (h1 : E.read (%64) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 569 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 570 (E[%430 := .value (if s.mem.readAt a 256 = s.mem.readAt b 256 then 1#8 else 0#8)])
        {s with alloc := ⟨s.alloc.nextFreeBlock + 33⟩} := by
  apply SqrtRatio.call_0_569 sqrtRatioPrimitives g E s _ a b (if s.mem.readAt a 256 = s.mem.readAt b 256 then 1#8 else 0#8) h0 h1
  simpa only [sqrtRatioPrimitives, BytesEq.program.args, BitVec.ofNat_eq_ofNat] using
    (BytesEq.program_exact a b s hwf ha hb)

/-- Exact `SqrtRatio` invocation of `mul` at bb0:576. -/
theorem sqrtratio_mul_0_576 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%73) = .value r)
    (h1 : E.read (%72) = .value a)
    (h2 : E.read (%52) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 576 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 577 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply SqrtRatio.call_0_576 sqrtRatioPrimitives g E s _ r a b h0 h1 h2
  simpa only [sqrtRatioPrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `bytesEq` at bb0:947. -/
theorem sqrtratio_bytesEq_0_947 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (a b : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32)
    (h0 : E.read (%63) = .value a)
    (h1 : E.read (%62) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 947 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 948 (E[%731 := .value (if s.mem.readAt a 256 = s.mem.readAt b 256 then 1#8 else 0#8)])
        {s with alloc := ⟨s.alloc.nextFreeBlock + 33⟩} := by
  apply SqrtRatio.call_0_947 sqrtRatioPrimitives g E s _ a b (if s.mem.readAt a 256 = s.mem.readAt b 256 then 1#8 else 0#8) h0 h1
  simpa only [sqrtRatioPrimitives, BytesEq.program.args, BitVec.ofNat_eq_ofNat] using
    (BytesEq.program_exact a b s hwf ha hb)

/-- Exact `SqrtRatio` invocation of `mul` at bb0:953. -/
theorem sqrtratio_mul_0_953 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (h0 : E.read (%71) = .value r)
    (h1 : E.read (%52) = .value a)
    (h2 : E.read (%79) = .value b)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 953 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 954 E
        {s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b))} := by
  apply SqrtRatio.call_0_953 sqrtRatioPrimitives g E s _ r a b h0 h1 h2
  simpa only [sqrtRatioPrimitives, SerialFieldMul.kernel.args] using (SerialFieldMul.kernel_call r a b s hwf hr ha hb)

/-- Exact `SqrtRatio` invocation of `blackBoxByte` at bb0:955. -/
theorem sqrtratio_blackBoxByte_0_955 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (byte : BitVec 8) (hwf : s.WF)
    (h0 : E.read (%732) = .value byte)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 955 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 956 (E[%733 := .value byte])
        {s with alloc := (s.alloca 1).alloc} := by
  apply SqrtRatio.call_0_955 sqrtRatioPrimitives g E s _ byte byte h0
  simpa only [sqrtRatioPrimitives, BlackBox.program.args] using (BlackBox.program_call byte s hwf)

/-- Exact `SqrtRatio` invocation of `blackBoxByte` at bb0:1028. -/
theorem sqrtratio_blackBoxByte_0_1028 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (byte : BitVec 8) (hwf : s.WF)
    (h0 : E.read (%805) = .value byte)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 1028 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 1029 (E[%806 := .value byte])
        {s with alloc := (s.alloca 1).alloc} := by
  apply SqrtRatio.call_0_1028 sqrtRatioPrimitives g E s _ byte byte h0
  simpa only [sqrtRatioPrimitives, BlackBox.program.args] using (BlackBox.program_call byte s hwf)

/-- Exact `SqrtRatio` invocation of `blackBoxByte` at bb0:1048. -/
theorem sqrtratio_blackBoxByte_0_1048 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (byte : BitVec 8) (hwf : s.WF)
    (h0 : E.read (%822) = .value byte)
    : Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 1048 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 1049 (E[%823 := .value byte])
        {s with alloc := (s.alloca 1).alloc} := by
  apply SqrtRatio.call_0_1048 sqrtRatioPrimitives g E s _ byte byte h0
  simpa only [sqrtRatioPrimitives, BlackBox.program.args] using (BlackBox.program_call byte s hwf)

end Agave.Ed25519.Encoding.Decompress.Execution
