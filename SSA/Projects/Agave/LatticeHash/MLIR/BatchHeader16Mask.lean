/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeader16

namespace AgaveLatticeHash.MLIR.BatchHeader16Mask
open LeanMLIR SLLVM
open InstCombine (LLVM)
open BatchHeader16

/-- One half of the byte mask, with the compiler's poison and freeze semantics. -/
def halfBytes (lengths offsets step : Vector (LLVM.IntW 64) 8) : Vector (LLVM.IntW 8) 8 :=
  (vzext 8 (vicmp .ugt lengths
    (Vector.ofFn fun i => LLVM.add offsets[i] step[i]))).map LLVM.freeze

private def joinBytes (lo hi filler : Vector (LLVM.IntW 8) 8) :=
  LLVM.Ty.shufflevector (e := .bitvec (.concrete 8))
    [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31]
    (LLVM.Ty.shufflevector (e := .bitvec (.concrete 8))
      [0, 1, 2, 3, 4, 5, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1] lo filler)
    (LLVM.Ty.shufflevector (e := .bitvec (.concrete 8))
      [-1, -1, -1, -1, -1, -1, -1, -1, 0, 1, 2, 3, 4, 5, 6, 7] hi filler)

private theorem shuffleLane {l : Nat} (mask : List Int)
    (a b : Vector (LLVM.IntW 8) l) (i : Nat) (hi : i < mask.length) :
    (LLVM.Ty.shufflevector (e := .bitvec (.concrete 8)) mask a b)[i] =
      (let m := mask.getD i (-1)
       if m < 0 then .poison
       else if h : m.toNat < l then a[m.toNat]
       else if h : m.toNat - l < l then b[m.toNat - l] else .poison) := by
  simp only [LLVM.Ty.shufflevector, Vector.getElem_ofFn]
  rfl

set_option maxHeartbeats 800000 in
private theorem joinBytes_eq (lo hi filler : Vector (LLVM.IntW 8) 8) :
    joinBytes lo hi filler = lo ++ hi := by
  apply Vector.ext
  intro i h
  change i < 16 at h
  interval_cases i <;>
    simp only [joinBytes] <;>
    repeat' (rw [shuffleLane]; simp only [↓reduceIte, ↓reduceDIte,
      List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT, Int.reduceToNat,
      Nat.reduceLT, Nat.reduceSub, List.length_cons, List.length_nil, Nat.reduceAdd])
  all_goals rw [Vector.getElem_append]; rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The generated shuffle network selects precisely the low and high masks;
none of the poison filler lanes reach the frozen result. -/
theorem active_bytes (V : Input16.Valuation) :
    (show Vector (LLVM.IntW 8) 16 from values16 V ⟨33, rfl⟩) =
      halfBytes (V ⟨28, rfl⟩) (V ⟨24, rfl⟩) (V ⟨119, rfl⟩) ++
      halfBytes (V ⟨26, rfl⟩) (V ⟨25, rfl⟩) (V ⟨119, rfl⟩) := by
  simp only [values16, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
    Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]
  simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]
  change vfreeze (joinBytes _ _ _) = _
  rw [joinBytes_eq]
  simp only [vfreeze, Vector.map_append, halfBytes]
  rfl

/-- Fully defined inputs make each mask byte exactly zero or one. Addition
here retains the LLVM unsigned bit-vector wrap semantics. -/
theorem halfBytes_lane (lengths offsets step : Vector (BitVec 64) 8) (i : Fin 8) :
    (halfBytes (lengths.map PoisonOr.value) (offsets.map PoisonOr.value)
      (step.map PoisonOr.value))[i.val] =
    PoisonOr.value (if (offsets[i] + step[i]).ult lengths[i] then 1#8 else 0#8) := by
  simp only [halfBytes, vzext, vicmp, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn]
  change LLVM.freeze (LLVM.zext 8
    (LLVM.icmp .ugt (.value lengths[i])
      (LLVM.add (.value offsets[i]) (.value step[i])))) = _
  have hadd : LLVM.add (.value offsets[i]) (.value step[i]) =
      .value (offsets[i] + step[i]) := by
    simp [LLVM.add, LLVM.add?]
  rw [hadd]
  cases h : (offsets[i] + step[i]).ult lengths[i] <;>
    simp only [Fin.getElem_fin] at h <;>
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.zext, LLVM.zext?, LLVM.freeze, h]

end AgaveLatticeHash.MLIR.BatchHeader16Mask
