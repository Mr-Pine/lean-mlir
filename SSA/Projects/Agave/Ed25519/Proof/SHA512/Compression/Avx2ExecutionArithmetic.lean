import SSA.Projects.Agave.Ed25519.Proof.SHA512.RotationArithmetic
import SSA.Projects.RIR.Semantics.Operations.Scalar
import SSA.Projects.RIR.Semantics.Operations.InboundsGep

/-! Pure arithmetic facts for the scalar tail of the AVX2 SHA-512 compressor. -/
namespace Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic

open LeanMLIR.RIR

theorem majority_source (a b c : Spec.Word) :
    ((c ^^^ b) &&& a) ^^^ (c &&& b) = Spec.majority a b c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Spec.majority, BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

theorem fshl50_rotateRight (x : Spec.Word) :
    Operation.fshl (.value x) (.value x) (.value 50#64) =
      .value (x.rotateRight 14) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (Spec.rotateRight14_fshl x)

theorem fshl46_rotateRight (x : Spec.Word) :
    Operation.fshl (.value x) (.value x) (.value 46#64) =
      .value (x.rotateRight 18) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (Spec.rotateRight18_fshl x)

theorem fshl23_rotateRight (x : Spec.Word) :
    Operation.fshl (.value x) (.value x) (.value 23#64) =
      .value (x.rotateRight 41) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (Spec.rotateRight41_fshl x)

theorem fshl36_rotateRight (x : Spec.Word) :
    Operation.fshl (.value x) (.value x) (.value 36#64) =
      .value (x.rotateRight 28) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (Spec.rotateRight28_fshl x)

theorem fshl30_rotateRight (x : Spec.Word) :
    Operation.fshl (.value x) (.value x) (.value 30#64) =
      .value (x.rotateRight 34) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (Spec.rotateRight34_fshl x)

theorem fshl25_rotateRight (x : Spec.Word) :
    Operation.fshl (.value x) (.value x) (.value 25#64) =
      .value (x.rotateRight 39) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (Spec.rotateRight39_fshl x)

theorem tail_index_add (r : Nat) (hlo : 64 ≤ r) (hhi : r < 80) :
    Operation.add {nsw := true, nuw := true}
      (.value (BitVec.ofNat 64 r)) (.value 1#64) =
      .value (BitVec.ofNat 64 (r + 1)) := by
  interval_cases r <;> decide

theorem tail_index_mask (r : Nat) (hlo : 64 ≤ r) (hhi : r < 80) :
    BitVec.ofNat 64 r &&& 15#64 = BitVec.ofNat 64 (r - 64) := by
  interval_cases r <;> decide

theorem tail_index_mask_toInt (r : Nat) (hlo : 64 ≤ r) (hhi : r < 80) :
    (BitVec.ofNat 64 r &&& 15#64).toInt = Int.ofNat (r - 64) := by
  interval_cases r <;> decide

theorem tail_index_gep (r : Nat) (hlo : 64 ≤ r) (hhi : r < 80) :
    Operation.gepInboundsIndex 8 (.value (BitVec.ofNat 64 r &&& 15#64)) =
      .value (Int.ofNat (8 * (r - 64))) := by
  interval_cases r <;> decide

theorem tail_index_eq80 (r : Nat) (hhi : r < 80) :
    (BitVec.ofNat 64 (r + 1) == 80#64) = decide (r + 1 = 80) := by
  interval_cases r <;> decide

end Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
