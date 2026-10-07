import SSA.Projects.Agave.Ed25519.Proof.Tables.Memory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMultiplication
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhasePipeline
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR
open Avx2PointAdd (Point pointReduced pointValue)
open Avx2PointAdd.Phases
open Avx2FieldMul.Execution (readBlocks)
open Reduce64.Execution (SmallRange)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {id : BlockId} {m : MemoryState}

/-- Every bounded static-table row has actual reduced cached bytes. This is a
current-state invariant, with no assumption about any ladder execution. -/
def BaseCache (base : Pointer) (s : GlobalState) : Prop :=
  SmallRange s.mem base 10240 ∧ ∀ k : Fin 64,
    ∃ C : Point, pointReduced C ∧ readBlocks s.mem (tableRow base k) = packPoint C ∧
      pointValue C = PointArithmetic.avx2Cache (Tables.avx2BasePoint k)

/-- A SIMD lane read is the matching 32-bit scalar read inside the same live row. -/
theorem readBlocks_lane (h : SmallRange m ptr 160) (i : Fin 5) (j : Fin 8) :
    (readBlocks m ptr i)[j.val] =
      m.readAt (ptr.add (BitVec.ofNat 64 (32 * i.val + 4 * j.val))) 32 := by
  have hi : 32 * i.val + 32 ≤ 160 := by have := i.isLt; omega
  have hj : 4 * j.val < 2^64 := by have := j.isLt; omega
  have hw : 4 * j.val + 4 ≤ 32 := by have := j.isLt; omega
  have hs := smallRange_slice h (32 * i.val) 32 hi
  have hr := MemoryState.readAt_add_of_readAt hs.fits
    (hs.no_wrap (k := 4 * j.val) (by omega)) (w := 32)
    (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]; omega) rfl
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj] at hr
  have hscale : 4 * j.val * 8 = j.val * 32 := by omega
  rw [hscale] at hr
  simpa only [readBlocks, Vector.getElem_ofFn, Ty.extractVecElem,
    Pointer.add_add, ← BitVec.ofNat_add] using hr.symm

theorem baseGlobal_readBlocks_lane
    (h : Tables.avx2BaseGlobal.Present id m) (k : Fin 64) (i : Fin 5) (j : Fin 8) :
    ((readBlocks m (tableRow (Tables.avx2BaseGlobal.address id) k) i)[j.val]).toNat =
      Tables.avx2BaseWord k i j := by
  have hk : 160 * k.val + 160 ≤ 10240 := by have := k.isLt; omega
  rw [readBlocks_lane (tableRow_live (Tables.Memory.avx2_base_buffer h) k hk)]
  simpa only [tableRow, Pointer.add_add, ← BitVec.ofNat_add, Nat.add_assoc] using
    Tables.Memory.avx2_base_word h k i j

/-- Preserve the static-row invariant using only allocation-local read equality
and transport of live ranges. Prefix and exact arithmetic store frames supply these. -/
theorem BaseCache.of_reads (h : BaseCache base before)
    (hlive : ∀ p bytes, SmallRange before.mem p bytes → SmallRange after.mem p bytes)
    (hread : ∀ p width, p.id = base.id →
      after.mem.readAt p width = before.mem.readAt p width) : BaseCache base after := by
  refine ⟨hlive base 10240 h.1, ?_⟩
  intro k
  obtain ⟨C, hc, hr, hv⟩ := h.2 k
  refine ⟨C, hc, ?_, hv⟩
  have hb : readBlocks after.mem (tableRow base k) =
      readBlocks before.mem (tableRow base k) := by
    funext i
    unfold readBlocks
    rw [hread _ 256 (by rfl)]
  exact hb.trans hr

theorem BaseCache.of_pointAddFrame (h : BaseCache base before)
    (hf : OutputFrame q before after)
    (hseparate : ∀ k, (q.written k).id ≠ base.id) : BaseCache base after := by
  apply h.of_reads hf.live
  intro p width hp
  exact hf.read p width (by simpa only [hp] using hseparate)

end Agave.Ed25519.DoubleBase.ExecutionAvx2
