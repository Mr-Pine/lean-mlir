import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.BaseCacheWords
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.BaseCacheMemory

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR
open Avx2PointAdd (pointReduced pointValue)
open Avx2PointAdd.Phases
open Avx2FieldMul.Execution (readBlocks inputNat unpackBlocks)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {id : BlockId} {m : MemoryState}

/-- Decode all physical lane positions of the actual loaded immutable row. -/
theorem baseGlobal_packedPoint (h : Tables.avx2BaseGlobal.Present id m) (k : Fin 64) :
    packedPoint m (tableRow (Tables.avx2BaseGlobal.address id) k) = baseCachePoint k := by
  ext limb <;> fin_cases limb <;>
    simp [packedPoint, baseCachePoint, baseCacheLimbs, inputNat, unpackBlocks]
  · exact baseGlobal_readBlocks_lane h k 0 0
  · exact baseGlobal_readBlocks_lane h k 0 2
  · exact baseGlobal_readBlocks_lane h k 1 0
  · exact baseGlobal_readBlocks_lane h k 1 2
  · exact baseGlobal_readBlocks_lane h k 2 0
  · exact baseGlobal_readBlocks_lane h k 2 2
  · exact baseGlobal_readBlocks_lane h k 3 0
  · exact baseGlobal_readBlocks_lane h k 3 2
  · exact baseGlobal_readBlocks_lane h k 4 0
  · exact baseGlobal_readBlocks_lane h k 4 2
  · exact baseGlobal_readBlocks_lane h k 0 1
  · exact baseGlobal_readBlocks_lane h k 0 3
  · exact baseGlobal_readBlocks_lane h k 1 1
  · exact baseGlobal_readBlocks_lane h k 1 3
  · exact baseGlobal_readBlocks_lane h k 2 1
  · exact baseGlobal_readBlocks_lane h k 2 3
  · exact baseGlobal_readBlocks_lane h k 3 1
  · exact baseGlobal_readBlocks_lane h k 3 3
  · exact baseGlobal_readBlocks_lane h k 4 1
  · exact baseGlobal_readBlocks_lane h k 4 3
  · exact baseGlobal_readBlocks_lane h k 0 4
  · exact baseGlobal_readBlocks_lane h k 0 6
  · exact baseGlobal_readBlocks_lane h k 1 4
  · exact baseGlobal_readBlocks_lane h k 1 6
  · exact baseGlobal_readBlocks_lane h k 2 4
  · exact baseGlobal_readBlocks_lane h k 2 6
  · exact baseGlobal_readBlocks_lane h k 3 4
  · exact baseGlobal_readBlocks_lane h k 3 6
  · exact baseGlobal_readBlocks_lane h k 4 4
  · exact baseGlobal_readBlocks_lane h k 4 6
  · exact baseGlobal_readBlocks_lane h k 0 5
  · exact baseGlobal_readBlocks_lane h k 0 7
  · exact baseGlobal_readBlocks_lane h k 1 5
  · exact baseGlobal_readBlocks_lane h k 1 7
  · exact baseGlobal_readBlocks_lane h k 2 5
  · exact baseGlobal_readBlocks_lane h k 2 7
  · exact baseGlobal_readBlocks_lane h k 3 5
  · exact baseGlobal_readBlocks_lane h k 3 7
  · exact baseGlobal_readBlocks_lane h k 4 5
  · exact baseGlobal_readBlocks_lane h k 4 7

/-- The real row's five vector loads recover exactly the bounded packed cache. -/
theorem baseGlobal_readBlocks (h : Tables.avx2BaseGlobal.Present id m) (k : Fin 64) :
    readBlocks m (tableRow (Tables.avx2BaseGlobal.address id) k) = packPoint (baseCachePoint k) := by
  rw [← packPoint_readPoint]
  exact congrArg packPoint (baseGlobal_packedPoint h k)

theorem baseGlobal_pointReduced (h : Tables.avx2BaseGlobal.Present id m) (k : Fin 64) :
    pointReduced (packedPoint m (tableRow (Tables.avx2BaseGlobal.address id) k)) := by
  rw [baseGlobal_packedPoint h k]
  exact baseCachePoint_reduced k

theorem baseGlobal_pointValue (h : Tables.avx2BaseGlobal.Present id m) (k : Fin 64) :
    pointValue (packedPoint m (tableRow (Tables.avx2BaseGlobal.address id) k)) =
      PointArithmetic.avx2Cache (Tables.avx2BasePoint k) := by
  rw [baseGlobal_packedPoint h k]
  exact baseCachePoint_value k

theorem baseCache_of_present (h : Tables.avx2BaseGlobal.Present id s.mem) :
    BaseCache (Tables.avx2BaseGlobal.address id) s := by
  refine ⟨Tables.Memory.avx2_base_buffer h, ?_⟩
  intro k
  exact ⟨baseCachePoint k, baseCachePoint_reduced k,
    baseGlobal_readBlocks h k, baseCachePoint_value k⟩

/-- Only the actual loaded global and its source address are required. -/
theorem baseCache_of_globalsReady (h : GlobalsReady g s) : BaseCache g.address2 s := by
  have hp : g.address2 = Tables.avx2BaseGlobal.address g.address2.id := by
    rcases hp : g.address2 with ⟨gid, offset⟩
    have ho : offset = 0 := by simpa only [hp] using h.baseAddress
    simpa only [ByteGlobal.address] using congrArg (Pointer.mk gid) ho
  rw [hp]
  exact baseCache_of_present h.basePresent

/-- The bounded row selected at any iteration remains a complete live object. -/
theorem BaseCache.row_live (h : BaseCache base s) (k : Fin 64) :
    Reduce64.Execution.SmallRange s.mem (tableRow base k) 160 :=
  tableRow_live h.1 k (by have := k.isLt; omega)

/-- Recover the reduced witness directly from the current memory reader. -/
theorem BaseCache.row_correct (h : BaseCache base s) (k : Fin 64) :
    pointReduced (packedPoint s.mem (tableRow base k)) ∧
    readBlocks s.mem (tableRow base k) = packPoint (packedPoint s.mem (tableRow base k)) ∧
    pointValue (packedPoint s.mem (tableRow base k)) =
      PointArithmetic.avx2Cache (Tables.avx2BasePoint k) := by
  obtain ⟨C, hc, hr, hv⟩ := h.2 k
  have he : packedPoint s.mem (tableRow base k) = C :=
    readPoint_of_packed (pointReduced_wide hc) _ _ hr
  rw [he]
  exact ⟨hc, hr, hv⟩

end Agave.Ed25519.DoubleBase.ExecutionAvx2
