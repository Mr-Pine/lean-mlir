import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Execution
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Algebra

/-!
# Byte-control composition with the concrete algebraic tables

The instruction network is executed for every inclusive ladder round. Its
nonpoison result is derived from the NAF construction, including at index zero
for the all-zero input. This connects byte signs and the compiler's guarded
lookup indices to the proved concrete-table algebraic endpoint.

The final theorem intentionally names this layer `byte_control`: the full
memory-bearing compiler CFG and its external pointer calls remain a separate
execution obligation. It is not a theorem about `Func.call` of either backend.
-/
namespace Agave.Ed25519.DoubleBase.Execution

open LeanMLIR.RIR PointArithmetic Tables

/-- The descending compiler control path, keeping poison observable. -/
def ladderBranches (a b : Nat → BitVec 8) : Nat → PoisonOr (List PointOp)
  | 0 => roundBranches (a 0) (b 0)
  | n + 1 => do
      let high ← roundBranches (a (n + 1)) (b (n + 1))
      let low ← ladderBranches a b n
      return high ++ low

theorem ladderBranches_naf (a b n : Nat) :
    ladderBranches (nafByte 5 a) (nafByte 8 b) n =
      .value (ladder (nafDigits 5 a) (nafDigits 8 b) n) := by
  induction n with
  | zero => exact roundBranches_naf a b 0
  | succ n ih =>
      simp only [ladderBranches, roundBranches_naf, ih, PoisonOr.value_bind,
        PoisonOr.pure_def, ladder]

/-- The initial scan reads the same integer digits from their byte encoding.
Only the first 256 entries are needed, exactly as in the compiler's scan. -/
theorem byte_scan_naf (a b : Nat) :
    startIndex (fun i => (nafByte 5 a i).toInt) (fun i => (nafByte 8 b i).toInt) 255 =
      startIndex (nafDigits 5 a) (nafDigits 8 b) 255 := by
  exact startIndex_congr _ _ _ _ _
    (fun i _ => nafByte_toInt 5 (Or.inl rfl) a i)
    (fun i _ => nafByte_toInt 8 (Or.inr rfl) b i)

def byteSchedule (a b : Nat) : PoisonOr (List PointOp) :=
  ladderBranches (nafByte 5 a) (nafByte 8 b)
    (startIndex (fun i => (nafByte 5 a i).toInt) (fun i => (nafByte 8 b i).toInt) 255)

theorem byteSchedule_naf (a b : Nat) :
    byteSchedule a b = .value (schedule (nafDigits 5 a) (nafDigits 8 b)) := by
  rw [byteSchedule, byte_scan_naf, ladderBranches_naf]
  rfl

def serialByteControl (a : Nat) (A : Extended F) (b : Nat) : PoisonOr (Extended F) := do
  let ops ← byteSchedule a b
  return projectiveAsExtended
    (ops.foldl (serialStep _root_.Ed25519.d (finiteTable (serialDoubleBaseTable A))) identityPoint)

def avx2ByteControl (a : Nat) (A : Extended F) (b : Nat) : PoisonOr (Extended F) := do
  let ops ← byteSchedule a b
  return ops.foldl (avx2Step (finiteTable (avx2DoubleBaseTable A))) identityPoint

theorem serialByteControl_eq (a b : Nat) (A : Extended F) :
    serialByteControl a A b = .value (serialMath a A b) := by
  simp only [serialByteControl, byteSchedule_naf, PoisonOr.value_bind,
    PoisonOr.pure_def, serialMath, run_eq_fold, schedule]

theorem avx2ByteControl_eq (a b : Nat) (A : Extended F) :
    avx2ByteControl a A b = .value (avx2Math a A b) := by
  simp only [avx2ByteControl, byteSchedule_naf, PoisonOr.value_bind,
    PoisonOr.pure_def, avx2Math, run_eq_fold, schedule]

/-- Byte-level guarded control produces matching compressed affine points for
every scalar and input coordinate tuple. Intermediate digit/table-index safety
is derived; neither nonpoison execution nor any lookup invariant is assumed. -/
theorem double_base_byte_control_compress_eq {Bytes : Type} (encode : F × F → Bytes)
    (a b : Nat) (A : Extended F) :
    (compressWith encode <$> avx2ByteControl a A b) =
      (compressWith encode <$> serialByteControl a A b) := by
  rw [avx2ByteControl_eq, serialByteControl_eq]
  exact congrArg PoisonOr.value (double_base_math_compress_eq encode a b A)

end Agave.Ed25519.DoubleBase.Execution
