import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Values
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2k

/-! Concrete lower helper endpoints used by the compressor. Multiplication,
five squarings, and the subtle byte identity use imported program proofs. The
remaining pow22501 pointer-call contract is explicitly restricted to that
one helper; its exponentiation mathematics is already proved elsewhere. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul (readLimbs storeLimbs unsigned)

theorem linked_mul_call (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40) (hb : SmallRange s.mem b 40)
    (hA : SerialFieldMul.Bounded (unsigned (readLimbs s a)))
    (hB : SerialFieldMul.Bounded (unsigned (readLimbs s b))) :
    ∃ output : Field.Serial,
      linkedPrimitives.mul (.cons (.value r) (.cons (.value a) (.cons (.value b) .nil))) s =
        .value (.nil, {s with mem := storeLimbs s.mem r output}) ∧
      wordValue output = wordValue (readLimbs s a) * wordValue (readLimbs s b) ∧
      SerialPoint.Tight (unsigned output) := by
  obtain ⟨output, hcall, hvalue, htight⟩ :=
    Decompress.Execution.mul_call r a b s hwf hr ha hb hA hB
  refine ⟨output, hcall, ?_, htight⟩
  simpa only [Decompress.Execution.wordValue_eq_serialValue, wordValue] using hvalue

theorem linked_pow2k5_call (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hA : SerialPoint.Tight (unsigned (readLimbs s a))) :
    ∃ output : Field.Serial,
      linkedPrimitives.pow2k
        (.cons (.value r) (.cons (.value a) (.cons (.value 5#32) .nil))) s =
        .value (.nil, {s with mem := storeLimbs s.mem r output}) ∧
      wordValue output = wordValue (readLimbs s a) ^ (2 ^ 5) ∧
      SerialPoint.Tight (unsigned output) := by
  obtain ⟨output, hcall, hvalue, htight⟩ :=
    Decompress.Execution.Pow2k.program_call_field 5 (by decide) (by decide) r a s hwf hr ha hA
  refine ⟨output, hcall, ?_, htight⟩
  simpa only [Decompress.Execution.wordValue_eq_serialValue, wordValue] using hvalue

theorem linked_blackBox_call (byte : BitVec 8) (s : GlobalState) (hwf : s.WF) :
    linkedPrimitives.blackBoxByte (.cons (.value byte) .nil) s =
      .value (.cons (.value byte) .nil, {s with alloc := (s.alloca 1).alloc}) :=
  Decompress.Execution.BlackBox.program_call byte s hwf

/-- Residual pointer execution of the imported pow22501 helper. It returns
two five-limb field values in adjacent slots, may advance allocation state,
and erases its own scratch memory. Nothing about point compression appears
in this contract. -/
def Pow22501PrimitiveContract
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (out input : Pointer) (s : GlobalState), s.WF →
    SmallRange s.mem out 80 → SmallRange s.mem input 40 →
    SerialPoint.Tight (unsigned (readLimbs s input)) →
    ∃ (after : GlobalState) (first second : Field.Serial),
      call (.cons (.value out) (.cons (.value input) .nil)) s = .value (.nil, after) ∧
      after.mem = storeLimbs (storeLimbs s.mem out first) (out.add 40) second ∧
      after.WF ∧ s.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock ∧
      wordValue first = (Decompress.pow22501 (wordValue (readLimbs s input))).1 ∧
      wordValue second = (Decompress.pow22501 (wordValue (readLimbs s input))).2 ∧
      SerialPoint.Tight (unsigned first) ∧ SerialPoint.Tight (unsigned second)

end Agave.Ed25519.Encoding.Compress.Execution
