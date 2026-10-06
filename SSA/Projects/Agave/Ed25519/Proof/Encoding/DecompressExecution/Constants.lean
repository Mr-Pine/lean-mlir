import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Globals
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Field

/-! Exact emitted constant bytes and their mathematical field interpretation. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR

def curveDLimbs : Words := fun i => curveD.bytes.extractLsb' (64 * i.val) 64

def sqrtM1Limbs : Words := fun i => sqrtM1.bytes.extractLsb' (64 * i.val) 64

theorem curveD_limbs : curveDLimbs =
    ![929955233495203, 466365720129213, 1662059464998953,
      2033849074728123, 1442794654840575] := by
  funext i
  fin_cases i <;> decide +kernel

theorem sqrtM1_limbs : sqrtM1Limbs =
    ![1718705420411056, 234908883556509, 2233514472574048,
      2117202627021982, 765476049583133] := by
  funext i
  fin_cases i <;> decide +kernel

theorem curveD_value : wordValue curveDLimbs = _root_.Ed25519.d := by decide +kernel

theorem sqrtM1_value : wordValue sqrtM1Limbs = _root_.sqrtm1 := by decide +kernel

theorem curveD_tight : SerialPoint.Tight (SerialFieldMul.unsigned curveDLimbs) := by
  intro i
  fin_cases i <;> decide +kernel

theorem sqrtM1_tight : SerialPoint.Tight (SerialFieldMul.unsigned sqrtM1Limbs) := by
  intro i
  fin_cases i <;> decide +kernel

/-- The actual memory reads of the emitted D initializer yield its five limbs. -/
theorem curveD_read (s : GlobalState) (id : BlockId)
    (h : curveD.Present id s.mem) :
    SerialFieldMul.readLimbs s (curveD.address id) = curveDLimbs := by
  unfold ByteGlobal.Present at h
  funext i
  fin_cases i <;>
    simp [SerialFieldMul.readLimbs, curveDLimbs, MemoryState.readAt,
      ByteGlobal.address, Pointer.add, Pointer.offsetInBits, h]

/-- The same readback contract for the exact emitted square root of -1. -/
theorem sqrtM1_read (s : GlobalState) (id : BlockId)
    (h : sqrtM1.Present id s.mem) :
    SerialFieldMul.readLimbs s (sqrtM1.address id) = sqrtM1Limbs := by
  unfold ByteGlobal.Present at h
  funext i
  fin_cases i <;>
    simp [SerialFieldMul.readLimbs, sqrtM1Limbs, MemoryState.readAt,
      ByteGlobal.address, Pointer.add, Pointer.offsetInBits, h]

end Agave.Ed25519.Encoding.Decompress.Execution
