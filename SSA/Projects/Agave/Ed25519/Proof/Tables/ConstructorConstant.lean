import SSA.Projects.Agave.Ed25519.Proof.Tables.ConstructorGlobals
import SSA.Projects.Agave.Ed25519.Proof.NAF.Memory
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Execution
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Correctness
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Arithmetic
import SSA.Projects.Firedancer.Curve

/-! The serial constructor's 2d constant is obtained from the pinned LLVM
initializer. Its five actual memory reads, limb bounds and curve-field value
are proved here, rather than assumed by the point/table call boundary. -/
namespace Agave.Ed25519.Tables
open LeanMLIR.RIR
open NAF.Memory (Buffer)

def serialD2Words (i : Fin 5) : BitVec 64 := serialD2Bytes.extractLsb' (64 * i.val) 64

def serialD2Limbs : SerialFieldMul.Limbs := SerialFieldMul.unsigned serialD2Words

theorem serialD2_tight : SerialPoint.Tight serialD2Limbs := by
  unfold SerialPoint.Tight
  decide +kernel

theorem serialD2_value : SerialPoint.value serialD2Limbs =
    (2 * _root_.Ed25519.d : ZMod _root_.p) := by
  change (SerialFieldMul.decode serialD2Limbs : ZMod _root_.p) = 2 * _root_.Ed25519.d
  decide +kernel

theorem serialD2_buffer {id : BlockId} {mem : MemoryState}
    (h : serialD2Global.Present id mem) :
    Buffer mem (serialD2Global.address id) 40 := by
  exact ⟨⟨40, serialD2Bytes⟩, h, by decide, by simp [ByteGlobal.address]⟩

theorem serialD2_read_words (s : GlobalState) (id : BlockId)
    (h : serialD2Global.Present id s.mem) :
    SerialFieldMul.readLimbs s (serialD2Global.address id) = serialD2Words := by
  funext i
  exact NAF.Memory.read_word (serialD2_buffer h) serialD2Bytes h.readAt i

/-- The caller supplies presence of the exact immutable source initializer;
its arithmetic meaning and input bounds are consequences. -/
theorem serialD2_read_contract (s : GlobalState) (id : BlockId)
    (h : serialD2Global.Present id s.mem) :
    Buffer s.mem (serialD2Global.address id) 40 ∧
      SerialPoint.Tight (SerialFieldMul.unsigned
        (SerialFieldMul.readLimbs s (serialD2Global.address id))) ∧
      SerialPoint.value (SerialFieldMul.unsigned
        (SerialFieldMul.readLimbs s (serialD2Global.address id))) =
          (2 * _root_.Ed25519.d : ZMod _root_.p) := by
  rw [serialD2_read_words s id h]
  exact ⟨serialD2_buffer h, serialD2_tight, serialD2_value⟩

end Agave.Ed25519.Tables
