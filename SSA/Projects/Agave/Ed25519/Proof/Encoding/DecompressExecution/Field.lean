import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressMath
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Contract
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Arithmetic

/-! Field-value and caller-bound interfaces for decompression execution.
The multiplication theorem uses the proved actual RIR kernel and writes its
actual five output limbs. The parser bound is proved for every 256-bit input.
-/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

abbrev Words := Fin 5 → BitVec 64

def wordValue (a : Words) : K := SerialPoint.value (SerialFieldMul.unsigned a)

theorem wordValue_eq_serialValue (a : Words) :
    wordValue a = (Field.serialValue a : K) := by
  have h := Encoding.value_eq_decode51 (SerialFieldMul.unsigned a)
  change (SerialFieldMul.decode (SerialFieldMul.unsigned a) : K) = _
  exact congrArg (fun n : Nat => (n : K)) h

/-- No canonicality or curve-membership assumption is needed to establish the
field kernel's input bounds at the parser boundary. -/
theorem fromBytesWord_tight (bytes : BitVec 256) :
    SerialPoint.Tight (SerialFieldMul.unsigned (fromBytesWord bytes)) := by
  intro i
  have h := Encoding.fromBytes_tight bytes.toNat i
  rw [← fromBytesWord_toNat] at h
  have : (fromBytesWord bytes i).toNat < 2 ^ 51 := h
  change (fromBytesWord bytes i).toNat < 2 ^ 52
  omega

theorem fromBytesWord_value (bytes : BitVec 256) :
    wordValue (fromBytesWord bytes) = y bytes := by
  rw [wordValue_eq_serialValue, fromBytesWord_field]

theorem machine_value (a b : Words)
    (ha : SerialFieldMul.Bounded (SerialFieldMul.unsigned a))
    (hb : SerialFieldMul.Bounded (SerialFieldMul.unsigned b)) :
    wordValue (SerialFieldMul.machine a b) = wordValue a * wordValue b := by
  unfold wordValue
  rw [SerialFieldMul.machine_unsigned a b ha hb, SerialPoint.mul_value]
  rfl

theorem machine_tight (a b : Words)
    (ha : SerialFieldMul.Bounded (SerialFieldMul.unsigned a))
    (hb : SerialFieldMul.Bounded (SerialFieldMul.unsigned b)) :
    SerialPoint.Tight (SerialFieldMul.unsigned (SerialFieldMul.machine a b)) := by
  rw [SerialFieldMul.machine_unsigned a b ha hb]
  obtain ⟨hother, hone, _⟩ := SerialFieldMul.mul_output_bounds _ _ ha hb
  intro i
  by_cases hi : i = 1
  · subst i
    norm_num [SerialFieldMul.radix] at hone ⊢
    omega
  · have h := hother i hi
    norm_num [SerialFieldMul.radix] at h ⊢
    omega

/-- Concrete multiplication execution in the decompression field, preserving
all memory except the five output stores and reestablishing the tight bound.
Only allocated ranges, state freshness, and the source limb bounds are assumed. -/
theorem mul_call (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40) (hb : SmallRange s.mem b 40)
    (hA : SerialFieldMul.Bounded (SerialFieldMul.unsigned (SerialFieldMul.readLimbs s a)))
    (hB : SerialFieldMul.Bounded (SerialFieldMul.unsigned (SerialFieldMul.readLimbs s b))) :
    ∃ output : Words,
      SerialFieldMul.kernel.call
          (SerialFieldMul.kernel.args (.value r) (.value a) (.value b)) s =
        .value (.nil, {s with mem := SerialFieldMul.storeLimbs s.mem r output}) ∧
      wordValue output = wordValue (SerialFieldMul.readLimbs s a) *
        wordValue (SerialFieldMul.readLimbs s b) ∧
      SerialPoint.Tight (SerialFieldMul.unsigned output) := by
  refine ⟨SerialFieldMul.machine (SerialFieldMul.readLimbs s a)
    (SerialFieldMul.readLimbs s b), SerialFieldMul.kernel_call r a b s hwf hr ha hb, ?_, ?_⟩
  · exact machine_value _ _ hA hB
  · exact machine_tight _ _ hA hB

end Agave.Ed25519.Encoding.Decompress.Execution
