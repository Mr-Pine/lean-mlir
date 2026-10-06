import SSA.Projects.Agave.LatticeHash.MLIR.BatchReduction16Core
set_option maxRecDepth 10000
set_option maxHeartbeats 400000
namespace AgaveLatticeHash.MLIR.BatchReduction16
open LeanMLIR SLLVM
open InstCombine (LLVM)

private theorem addSixteen (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Vector (BitVec 16) 32) :
    addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (addHalves (a1.map PoisonOr.value) (a0.map PoisonOr.value)) (a2.map PoisonOr.value)) (a3.map PoisonOr.value)) (a4.map PoisonOr.value)) (a5.map PoisonOr.value)) (a6.map PoisonOr.value)) (a7.map PoisonOr.value)) (a8.map PoisonOr.value)) (a9.map PoisonOr.value)) (a10.map PoisonOr.value)) (a11.map PoisonOr.value)) (a12.map PoisonOr.value)) (a13.map PoisonOr.value)) (a14.map PoisonOr.value)) (a15.map PoisonOr.value) =
    (Vector.ofFn fun i : Fin 32 => a1[i] + a0[i] + a2[i] + a3[i] + a4[i] + a5[i] + a6[i] + a7[i] + a8[i] + a9[i] + a10[i] + a11[i] + a12[i] + a13[i] + a14[i] + a15[i]).map PoisonOr.value := by
  let add (a b : Vector (BitVec 16) 32) := Vector.ofFn fun i : Fin 32 => a[i] + b[i]
  let s1 := add a1 a0
  let s2 := add s1 a2
  let s3 := add s2 a3
  let s4 := add s3 a4
  let s5 := add s4 a5
  let s6 := add s5 a6
  let s7 := add s6 a7
  let s8 := add s7 a8
  let s9 := add s8 a9
  let s10 := add s9 a10
  let s11 := add s10 a11
  let s12 := add s11 a12
  let s13 := add s12 a13
  let s14 := add s13 a14
  let s15 := add s14 a15
  have h1 := addHalves_defined a1 a0
  have h2 := (congrArg (fun v => addHalves v (a2.map PoisonOr.value)) h1).trans (addHalves_defined s1 a2)
  have h3 := (congrArg (fun v => addHalves v (a3.map PoisonOr.value)) h2).trans (addHalves_defined s2 a3)
  have h4 := (congrArg (fun v => addHalves v (a4.map PoisonOr.value)) h3).trans (addHalves_defined s3 a4)
  have h5 := (congrArg (fun v => addHalves v (a5.map PoisonOr.value)) h4).trans (addHalves_defined s4 a5)
  have h6 := (congrArg (fun v => addHalves v (a6.map PoisonOr.value)) h5).trans (addHalves_defined s5 a6)
  have h7 := (congrArg (fun v => addHalves v (a7.map PoisonOr.value)) h6).trans (addHalves_defined s6 a7)
  have h8 := (congrArg (fun v => addHalves v (a8.map PoisonOr.value)) h7).trans (addHalves_defined s7 a8)
  have h9 := (congrArg (fun v => addHalves v (a9.map PoisonOr.value)) h8).trans (addHalves_defined s8 a9)
  have h10 := (congrArg (fun v => addHalves v (a10.map PoisonOr.value)) h9).trans (addHalves_defined s9 a10)
  have h11 := (congrArg (fun v => addHalves v (a11.map PoisonOr.value)) h10).trans (addHalves_defined s10 a11)
  have h12 := (congrArg (fun v => addHalves v (a12.map PoisonOr.value)) h11).trans (addHalves_defined s11 a12)
  have h13 := (congrArg (fun v => addHalves v (a13.map PoisonOr.value)) h12).trans (addHalves_defined s12 a13)
  have h14 := (congrArg (fun v => addHalves v (a14.map PoisonOr.value)) h13).trans (addHalves_defined s13 a14)
  have h15 := (congrArg (fun v => addHalves v (a15.map PoisonOr.value)) h14).trans (addHalves_defined s14 a15)
  refine h15.trans ?_
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin,
    s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, add]

private def sumRowsValues (rows : Vector Words16 16) : Vector (BitVec 16) 32 :=
  Vector.ofFn fun i => sum16 fun row => (halves32 rows[row])[i]

private theorem sumRows16_map (rows : Vector Words16 16) :
    sumRows16 (rows.map (fun row => row.map PoisonOr.value)) =
      (sumRowsValues rows).map PoisonOr.value := by
  let input := rows.map (fun row => row.map PoisonOr.value)
  have hc (j : Fin 16) : castHalves input[j] = (halves32 rows[j]).map PoisonOr.value := by
    simp only [input, Fin.getElem_fin, Vector.getElem_map]
    exact castHalves_defined _
  have h1 := congrArg₂ addHalves (hc 1) (hc 0)
  have h2 := congrArg₂ addHalves h1 (hc 2)
  have h3 := congrArg₂ addHalves h2 (hc 3)
  have h4 := congrArg₂ addHalves h3 (hc 4)
  have h5 := congrArg₂ addHalves h4 (hc 5)
  have h6 := congrArg₂ addHalves h5 (hc 6)
  have h7 := congrArg₂ addHalves h6 (hc 7)
  have h8 := congrArg₂ addHalves h7 (hc 8)
  have h9 := congrArg₂ addHalves h8 (hc 9)
  have h10 := congrArg₂ addHalves h9 (hc 10)
  have h11 := congrArg₂ addHalves h10 (hc 11)
  have h12 := congrArg₂ addHalves h11 (hc 12)
  have h13 := congrArg₂ addHalves h12 (hc 13)
  have h14 := congrArg₂ addHalves h13 (hc 14)
  have h15 := congrArg₂ addHalves h14 (hc 15)
  refine h15.trans ((addSixteen (halves32 rows[0]) (halves32 rows[1]) (halves32 rows[2]) (halves32 rows[3]) (halves32 rows[4]) (halves32 rows[5]) (halves32 rows[6]) (halves32 rows[7]) (halves32 rows[8]) (halves32 rows[9]) (halves32 rows[10]) (halves32 rows[11]) (halves32 rows[12]) (halves32 rows[13]) (halves32 rows[14]) (halves32 rows[15])).trans ?_)
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, sumRowsValues, sum16]
  apply congrArg PoisonOr.value
  rw [BitVec.add_comm ((halves32 rows[1])[i]) ((halves32 rows[0])[i])]
  rfl

theorem sumRows16_defined (cols : Columns16) :
    sumRows16 ((transposedWords cols).map (fun row => row.map PoisonOr.value)) =
      (columnSum cols).map PoisonOr.value := by
  have h : sumRowsValues (transposedWords cols) = columnSum cols := by
    apply Vector.ext
    intro i hi
    simp only [sumRowsValues, columnSum, Vector.getElem_ofFn]
    apply congrArg sum16
    funext row
    simp only [halves32, transposedWords, Vector.getElem_ofFn, Fin.getElem_fin]
  exact (sumRows16_map (transposedWords cols)).trans
    (congrArg (fun v : Vector (BitVec 16) 32 => v.map PoisonOr.value) h)

/-- The exact emitted output network computes 32 independent wrapping u16 sums. -/
theorem reduce16_defined (cols : Columns16) :
    reduce16 (cols[0].map PoisonOr.value) (cols[1].map PoisonOr.value) (cols[2].map PoisonOr.value) (cols[3].map PoisonOr.value)
      (cols[4].map PoisonOr.value) (cols[5].map PoisonOr.value) (cols[6].map PoisonOr.value) (cols[7].map PoisonOr.value)
      (cols[8].map PoisonOr.value) (cols[9].map PoisonOr.value) (cols[10].map PoisonOr.value) (cols[11].map PoisonOr.value)
      (cols[12].map PoisonOr.value) (cols[13].map PoisonOr.value) (cols[14].map PoisonOr.value) (cols[15].map PoisonOr.value) =
      (columnSum cols).map PoisonOr.value := by
  rw [reduce16_transpose, transpose_defined, sumRows16_defined]

theorem sum16_halfWord_laneSum (row : Fin 16 → BitVec 32) (half : Fin 2) :
    sum16 (fun lane => AgaveLattice.halfWord (row lane) half) =
      AgaveLattice.halfWord (AgaveLattice.laneSum 16 (by omega) row) half := by
  unfold AgaveLattice.laneSum
  rw [AgaveLattice.halfWord_fold]
  simp [sum16, List.finRange_succ]

theorem columnSum_laneSum (cols : Columns16) (word : Fin 16) (half : Fin 2) :
    (columnSum cols)[2 * word.val + half.val]'(by omega) =
      AgaveLattice.halfWord
        (AgaveLattice.laneSum 16 (by omega) (fun lane => cols[word][lane])) half := by
  have hdiv : (2 * word.val + half.val) / 2 = word.val := by omega
  have hmod : (2 * word.val + half.val) % 2 = half.val := by omega
  simpa only [columnSum, Vector.getElem_ofFn, hdiv, hmod, AgaveLattice.halfWord,
    Fin.getElem_fin] using sum16_halfWord_laneSum (fun lane => cols[word][lane]) half

end AgaveLatticeHash.MLIR.BatchReduction16
