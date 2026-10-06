import SSA.Projects.Agave.LatticeHash.MLIR.BatchReductionCore

set_option maxRecDepth 10000
set_option maxHeartbeats 200000
namespace AgaveLatticeHash.MLIR.BatchReduction
open LeanMLIR SLLVM
open InstCombine (LLVM)

private theorem addEight (a0 a1 a2 a3 a4 a5 a6 a7 : Vector (BitVec 16) 16) :
    addHalves (addHalves (addHalves (addHalves (addHalves (addHalves
      (addHalves (a1.map PoisonOr.value) (a0.map PoisonOr.value))
      (a2.map PoisonOr.value)) (a3.map PoisonOr.value)) (a4.map PoisonOr.value))
      (a5.map PoisonOr.value)) (a6.map PoisonOr.value)) (a7.map PoisonOr.value) =
    (Vector.ofFn fun i : Fin 16 => a1[i] + a0[i] + a2[i] + a3[i] + a4[i] + a5[i] + a6[i] + a7[i]).map PoisonOr.value := by
  let add (a b : Vector (BitVec 16) 16) := Vector.ofFn fun i : Fin 16 => a[i] + b[i]
  let s1 := add a1 a0
  let s2 := add s1 a2
  let s3 := add s2 a3
  let s4 := add s3 a4
  let s5 := add s4 a5
  let s6 := add s5 a6
  let s7 := add s6 a7
  have h1 := addHalves_defined a1 a0
  have h2 := (congrArg (fun v => addHalves v (a2.map PoisonOr.value)) h1).trans (addHalves_defined s1 a2)
  have h3 := (congrArg (fun v => addHalves v (a3.map PoisonOr.value)) h2).trans (addHalves_defined s2 a3)
  have h4 := (congrArg (fun v => addHalves v (a4.map PoisonOr.value)) h3).trans (addHalves_defined s3 a4)
  have h5 := (congrArg (fun v => addHalves v (a5.map PoisonOr.value)) h4).trans (addHalves_defined s4 a5)
  have h6 := (congrArg (fun v => addHalves v (a6.map PoisonOr.value)) h5).trans (addHalves_defined s5 a6)
  have h7 := (congrArg (fun v => addHalves v (a7.map PoisonOr.value)) h6).trans (addHalves_defined s6 a7)
  refine h7.trans ?_
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin,
    s6, s5, s4, s3, s2, s1, add]

private def sumRowsValues (rows : Vector Words8 8) : Vector (BitVec 16) 16 :=
  Vector.ofFn fun i => sum8 fun row => (halves32 rows[row])[i]

private theorem sumRows8_map (rows : Vector Words8 8) :
    sumRows8 (rows.map (fun row => row.map PoisonOr.value)) =
      (sumRowsValues rows).map PoisonOr.value := by
  let input := rows.map (fun row => row.map PoisonOr.value)
  have hc (j : Fin 8) : castHalves input[j] = (halves32 rows[j]).map PoisonOr.value := by
    simp only [input, Fin.getElem_fin, Vector.getElem_map]
    exact castHalves_defined _
  have h1 := congrArg₂ addHalves (hc 1) (hc 0)
  have h2 := congrArg₂ addHalves h1 (hc 2)
  have h3 := congrArg₂ addHalves h2 (hc 3)
  have h4 := congrArg₂ addHalves h3 (hc 4)
  have h5 := congrArg₂ addHalves h4 (hc 5)
  have h6 := congrArg₂ addHalves h5 (hc 6)
  have h7 := congrArg₂ addHalves h6 (hc 7)
  refine h7.trans ((addEight (halves32 rows[0]) (halves32 rows[1])
    (halves32 rows[2]) (halves32 rows[3]) (halves32 rows[4]) (halves32 rows[5])
    (halves32 rows[6]) (halves32 rows[7])).trans ?_)
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, sumRowsValues, sum8]
  apply congrArg PoisonOr.value
  rw [BitVec.add_comm ((halves32 rows[1])[i]) ((halves32 rows[0])[i])]
  rfl

theorem sumRows8_defined (cols : Columns8) :
    sumRows8 ((transposedWords cols).map (fun row => row.map PoisonOr.value)) =
      (columnSum cols).map PoisonOr.value := by
  rw [sumRows8_map]
  apply congrArg (fun v : Vector (BitVec 16) 16 => v.map PoisonOr.value)
  apply Vector.ext
  intro i hi
  simp only [sumRowsValues, columnSum, Vector.getElem_ofFn, sum8,
    halves32, transposedWords, Fin.getElem_fin]

/-- The emitted shuffle/bitcast/add network computes all sixteen independent
wrapping half-word sums, with no assumption on the input values. -/
theorem reduce8_defined (cols : Columns8) :
    reduce8 (cols[0].map PoisonOr.value) (cols[1].map PoisonOr.value)
      (cols[2].map PoisonOr.value) (cols[3].map PoisonOr.value)
      (cols[4].map PoisonOr.value) (cols[5].map PoisonOr.value)
      (cols[6].map PoisonOr.value) (cols[7].map PoisonOr.value) =
      (columnSum cols).map PoisonOr.value := by
  rw [reduce8_transpose, transpose_defined, sumRows8_defined]

/-- Agreement with the existing LtHash reduction specification. -/
theorem sum8_halfWord_laneSum (row : Fin 8 → BitVec 32) (half : Fin 2) :
    sum8 (fun lane => AgaveLattice.halfWord (row lane) half) =
      AgaveLattice.halfWord (AgaveLattice.laneSum 8 (by omega) row) half := by
  unfold AgaveLattice.laneSum
  rw [AgaveLattice.halfWord_fold]
  simp [sum8, List.finRange_succ]

/-- Each stored half-word matches the prior LtHash lane-reduction model. -/
theorem columnSum_laneSum (cols : Columns8) (word : Fin 8) (half : Fin 2) :
    (columnSum cols)[2 * word.val + half.val]'(by omega) =
      AgaveLattice.halfWord
        (AgaveLattice.laneSum 8 (by omega) (fun lane => cols[word][lane])) half := by
  have hdiv : (2 * word.val + half.val) / 2 = word.val := by omega
  have hmod : (2 * word.val + half.val) % 2 = half.val := by omega
  simpa only [columnSum, Vector.getElem_ofFn, hdiv, hmod, AgaveLattice.halfWord,
    Fin.getElem_fin] using sum8_halfWord_laneSum (fun lane => cols[word][lane]) half

end AgaveLatticeHash.MLIR.BatchReduction
