import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSetupPrefix
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLadderState

/-! Static serial base-table words at the setup-to-ladder boundary. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readField readPoint readCached readAffineCached)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Every actual initializer limb satisfies the helper's input bound. -/
theorem serialBaseWord_bounded : ∀ (k : Fin 64) (c : Fin 3) (i : Fin 5),
    Tables.serialBaseWord k c i < 2^54 := by
  decide +kernel

def serialBaseLimbs (k : Fin 64) : SerialPoint.LimbPoint :=
  ⟨Tables.serialBaseWord k 1, Tables.serialBaseWord k 0, fun _ => 0, Tables.serialBaseWord k 2⟩

theorem serialBaseLimbs_bounded (k : Fin 64) : SerialPoint.PointBounded (serialBaseLimbs k) := by
  refine ⟨serialBaseWord_bounded k 1, serialBaseWord_bounded k 0, ?_, serialBaseWord_bounded k 2⟩
  intro i
  change 0 < 2^54
  decide

theorem serialBase_readField (s : GlobalState) (id : BlockId)
    (h : Tables.serialBaseGlobal.Present id s.mem) (k : Fin 64) (c : Fin 3) :
    readField s (((Tables.serialBaseGlobal.address id).add (BitVec.ofNat 64 (120*k.val))).add
      (BitVec.ofNat 64 (40*c.val))) = Tables.serialBaseWord k c := by
  funext i
  change (s.mem.readAt _ 64).toNat = _
  simpa only [Pointer.add_add, ← BitVec.ofNat_add] using Tables.Memory.serial_base_word h k c i

theorem serialBase_readAffineCached (s : GlobalState) (id : BlockId)
    (h : Tables.serialBaseGlobal.Present id s.mem) (k : Fin 64) :
    readAffineCached s ((Tables.serialBaseGlobal.address id).add (BitVec.ofNat 64 (120*k.val))) =
      serialBaseLimbs k := by
  apply PointArithmetic.Extended.ext
  · exact serialBase_readField s id h k 1
  · have hy := serialBase_readField s id h k 0
    change readField s (((Tables.serialBaseGlobal.address id).add
      (BitVec.ofNat 64 (120*k.val))).add 0#64) = Tables.serialBaseWord k 0 at hy
    change readField s ((Tables.serialBaseGlobal.address id).add
      (BitVec.ofNat 64 (120*k.val))) = Tables.serialBaseWord k 0
    simpa only [Pointer.add_zero] using hy
  · rfl
  · exact serialBase_readField s id h k 2

private theorem setup_value_eq_sum (f : SerialFieldMul.Limbs) :
    SerialPoint.value f = ∑ i : Fin 5, (f i : Tables.F) * 2^(51*i.val) := by
  simp [SerialPoint.value, SerialFieldMul.decode, SerialFieldMul.radix, Fin.sum_univ_succ]
  ring_nf
  rfl

theorem serialBaseLimbs_value (k : Fin 64) :
    SerialPoint.affineCacheValue (serialBaseLimbs k) = Tables.serialBaseCache k := by
  apply PointArithmetic.Extended.ext
  · exact setup_value_eq_sum _
  · exact setup_value_eq_sum _
  · rfl
  · exact setup_value_eq_sum _

/-- Bounded cache limbs and odd-multiple meaning follow from the imported bytes. -/
theorem serialBase_cache_ready (s : GlobalState) (id : BlockId)
    (h : Tables.serialBaseGlobal.Present id s.mem) (k : Fin 64) :
    SerialPoint.PointBounded (readAffineCached s
      ((Tables.serialBaseGlobal.address id).add (BitVec.ofNat 64 (120*k.val)))) ∧
    ∃ Q, Tables.Represents Q ((2*k.val+1) • Tables.baseGroup) ∧
      SerialPoint.affineCacheValue (readAffineCached s
        ((Tables.serialBaseGlobal.address id).add (BitVec.ofNat 64 (120*k.val)))) =
          PointArithmetic.serialCache _root_.Ed25519.d Q := by
  rw [serialBase_readAffineCached s id h k]
  exact ⟨serialBaseLimbs_bounded k, Tables.serialBasePoint k,
    Tables.serialBasePoint_represents k, (serialBaseLimbs_value k).trans (Tables.serialBaseCache_correct k)⟩

end Agave.Ed25519.DoubleBase.RIR
