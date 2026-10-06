import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchTranspose

namespace AgaveLatticeHash.MLIR.BatchTranspose16
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionExit
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev InCtx16 := blockInput agave_batch_16.cfgBlock_2
abbrev Row16 := Vector (LLVM.IntW 32) 16
abbrev Row16Ty : LLVM.Ty := .vector 16 (.bitvec (.concrete 32))

private theorem hvConsAppend {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} {t : SLLVM.Ty}
    (x : TyDenote.toType t) (xs : HVector TyDenote.toType ts) (V : Γ.Valuation) :
    (x ::ₕ xs) ++ V = x ::ᵥ (xs ++ V) := by
  exact Ctxt.Valuation.cons_append
private theorem hvNilAppend {Γ : Ctxt SLLVM.Ty} (V : Γ.Valuation) :
    (HVector.nil : HVector TyDenote.toType ([] : List SLLVM.Ty)) ++ V = V := rfl

private theorem targetIte {Γ : Ctxt SLLVM.Ty} {sigs} (V : Γ.Valuation)
    (p : Prop) [Decidable p] (a b : Target Γ sigs) :
    (if p then a else b).denote V = if p then a.denote V else b.denote V := by
  split <;> rfl

private theorem shuffle0 (a b : Row16) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] a b = #v[a[0], a[1], a[2], a[3], a[8], a[9], a[10], a[11], b[0], b[1], b[2], b[3], b[8], b[9], b[10], b[11]] := by
  apply Vector.ext
  intro i hi
  change i < 16 at hi
  interval_cases i <;> simp only [LLVM.Ty.shufflevector, Vector.getElem_ofFn,
    ↓reduceIte, ↓reduceDIte, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
    List.getD_cons_succ, Int.reduceLT, Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]

private theorem shuffle1 (a b : Row16) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] a b = #v[a[4], a[5], a[6], a[7], a[12], a[13], a[14], a[15], b[4], b[5], b[6], b[7], b[12], b[13], b[14], b[15]] := by
  apply Vector.ext
  intro i hi
  change i < 16 at hi
  interval_cases i <;> simp only [LLVM.Ty.shufflevector, Vector.getElem_ofFn,
    ↓reduceIte, ↓reduceDIte, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
    List.getD_cons_succ, Int.reduceLT, Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]

private theorem shuffle2 (a b : Row16) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] a b = #v[a[0], b[0], a[1], b[1], a[4], b[4], a[5], b[5], a[8], b[8], a[9], b[9], a[12], b[12], a[13], b[13]] := by
  apply Vector.ext
  intro i hi
  change i < 16 at hi
  interval_cases i <;> simp only [LLVM.Ty.shufflevector, Vector.getElem_ofFn,
    ↓reduceIte, ↓reduceDIte, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
    List.getD_cons_succ, Int.reduceLT, Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]

private theorem shuffle3 (a b : Row16) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] a b = #v[a[2], b[2], a[3], b[3], a[6], b[6], a[7], b[7], a[10], b[10], a[11], b[11], a[14], b[14], a[15], b[15]] := by
  apply Vector.ext
  intro i hi
  change i < 16 at hi
  interval_cases i <;> simp only [LLVM.Ty.shufflevector, Vector.getElem_ofFn,
    ↓reduceIte, ↓reduceDIte, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
    List.getD_cons_succ, Int.reduceLT, Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]

def rootTarget16 (V : InCtx16.Valuation) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨5, rfl, [V ⟨26, rfl⟩, V ⟨25, rfl⟩, V ⟨24, rfl⟩, V ⟨23, rfl⟩, V ⟨22, rfl⟩, V ⟨21, rfl⟩, V ⟨20, rfl⟩, V ⟨19, rfl⟩, V ⟨18, rfl⟩, V ⟨17, rfl⟩]ₕ⟩
def nonrootTarget16 (V : InCtx16.Valuation) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨6, rfl, [V ⟨44, rfl⟩, V ⟨43, rfl⟩, V ⟨42, rfl⟩, V ⟨41, rfl⟩, V ⟨40, rfl⟩, V ⟨39, rfl⟩, V ⟨38, rfl⟩, V ⟨37, rfl⟩, V ⟨36, rfl⟩, V ⟨35, rfl⟩, V ⟨34, rfl⟩, V ⟨33, rfl⟩, V ⟨32, rfl⟩, V ⟨31, rfl⟩, V ⟨30, rfl⟩, V ⟨29, rfl⟩, V ⟨28, rfl⟩, V ⟨27, rfl⟩, V ⟨26, rfl⟩, V ⟨25, rfl⟩, V ⟨24, rfl⟩, V ⟨23, rfl⟩, V ⟨22, rfl⟩, V ⟨21, rfl⟩, V ⟨20, rfl⟩, V ⟨19, rfl⟩, V ⟨18, rfl⟩, V ⟨17, rfl⟩, V ⟨16, rfl⟩]ₕ⟩

/-- Sixteen complete input rows are transposed into message-word vectors;
all reads precede all writes, including for aliased input and scratch memory. -/
def transpose16Spec (V : InCtx16.Valuation) :
    EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) := do
  let x0 : Row16 ← liftM (load (V ⟨15, rfl⟩) Row16Ty)
  let x1 : Row16 ← liftM (load (V ⟨14, rfl⟩) Row16Ty)
  let x2 : Row16 ← liftM (load (V ⟨13, rfl⟩) Row16Ty)
  let x3 : Row16 ← liftM (load (V ⟨12, rfl⟩) Row16Ty)
  let x4 : Row16 ← liftM (load (V ⟨11, rfl⟩) Row16Ty)
  let x5 : Row16 ← liftM (load (V ⟨10, rfl⟩) Row16Ty)
  let x6 : Row16 ← liftM (load (V ⟨9, rfl⟩) Row16Ty)
  let x7 : Row16 ← liftM (load (V ⟨8, rfl⟩) Row16Ty)
  let x8 : Row16 ← liftM (load (V ⟨7, rfl⟩) Row16Ty)
  let x9 : Row16 ← liftM (load (V ⟨6, rfl⟩) Row16Ty)
  let x10 : Row16 ← liftM (load (V ⟨5, rfl⟩) Row16Ty)
  let x11 : Row16 ← liftM (load (V ⟨4, rfl⟩) Row16Ty)
  let x12 : Row16 ← liftM (load (V ⟨3, rfl⟩) Row16Ty)
  let x13 : Row16 ← liftM (load (V ⟨2, rfl⟩) Row16Ty)
  let x14 : Row16 ← liftM (load (V ⟨1, rfl⟩) Row16Ty)
  let x15 : Row16 ← liftM (load (V ⟨0, rfl⟩) Row16Ty)
  let y0 : Row16 := #v[x0[0], x1[0], x2[0], x3[0], x4[0], x5[0], x6[0], x7[0], x8[0], x9[0], x10[0], x11[0], x12[0], x13[0], x14[0], x15[0]]
  liftM (store (V ⟨79, rfl⟩) Row16Ty y0)
  let y1 : Row16 := #v[x0[1], x1[1], x2[1], x3[1], x4[1], x5[1], x6[1], x7[1], x8[1], x9[1], x10[1], x11[1], x12[1], x13[1], x14[1], x15[1]]
  liftM (store (V ⟨62, rfl⟩) Row16Ty y1)
  let y2 : Row16 := #v[x0[2], x1[2], x2[2], x3[2], x4[2], x5[2], x6[2], x7[2], x8[2], x9[2], x10[2], x11[2], x12[2], x13[2], x14[2], x15[2]]
  liftM (store (V ⟨61, rfl⟩) Row16Ty y2)
  let y3 : Row16 := #v[x0[3], x1[3], x2[3], x3[3], x4[3], x5[3], x6[3], x7[3], x8[3], x9[3], x10[3], x11[3], x12[3], x13[3], x14[3], x15[3]]
  liftM (store (V ⟨60, rfl⟩) Row16Ty y3)
  let y4 : Row16 := #v[x0[4], x1[4], x2[4], x3[4], x4[4], x5[4], x6[4], x7[4], x8[4], x9[4], x10[4], x11[4], x12[4], x13[4], x14[4], x15[4]]
  liftM (store (V ⟨59, rfl⟩) Row16Ty y4)
  let y5 : Row16 := #v[x0[5], x1[5], x2[5], x3[5], x4[5], x5[5], x6[5], x7[5], x8[5], x9[5], x10[5], x11[5], x12[5], x13[5], x14[5], x15[5]]
  liftM (store (V ⟨58, rfl⟩) Row16Ty y5)
  let y6 : Row16 := #v[x0[6], x1[6], x2[6], x3[6], x4[6], x5[6], x6[6], x7[6], x8[6], x9[6], x10[6], x11[6], x12[6], x13[6], x14[6], x15[6]]
  liftM (store (V ⟨57, rfl⟩) Row16Ty y6)
  let y7 : Row16 := #v[x0[7], x1[7], x2[7], x3[7], x4[7], x5[7], x6[7], x7[7], x8[7], x9[7], x10[7], x11[7], x12[7], x13[7], x14[7], x15[7]]
  liftM (store (V ⟨56, rfl⟩) Row16Ty y7)
  let y8 : Row16 := #v[x0[8], x1[8], x2[8], x3[8], x4[8], x5[8], x6[8], x7[8], x8[8], x9[8], x10[8], x11[8], x12[8], x13[8], x14[8], x15[8]]
  liftM (store (V ⟨55, rfl⟩) Row16Ty y8)
  let y9 : Row16 := #v[x0[9], x1[9], x2[9], x3[9], x4[9], x5[9], x6[9], x7[9], x8[9], x9[9], x10[9], x11[9], x12[9], x13[9], x14[9], x15[9]]
  liftM (store (V ⟨54, rfl⟩) Row16Ty y9)
  let y10 : Row16 := #v[x0[10], x1[10], x2[10], x3[10], x4[10], x5[10], x6[10], x7[10], x8[10], x9[10], x10[10], x11[10], x12[10], x13[10], x14[10], x15[10]]
  liftM (store (V ⟨53, rfl⟩) Row16Ty y10)
  let y11 : Row16 := #v[x0[11], x1[11], x2[11], x3[11], x4[11], x5[11], x6[11], x7[11], x8[11], x9[11], x10[11], x11[11], x12[11], x13[11], x14[11], x15[11]]
  liftM (store (V ⟨52, rfl⟩) Row16Ty y11)
  let y12 : Row16 := #v[x0[12], x1[12], x2[12], x3[12], x4[12], x5[12], x6[12], x7[12], x8[12], x9[12], x10[12], x11[12], x12[12], x13[12], x14[12], x15[12]]
  liftM (store (V ⟨51, rfl⟩) Row16Ty y12)
  let y13 : Row16 := #v[x0[13], x1[13], x2[13], x3[13], x4[13], x5[13], x6[13], x7[13], x8[13], x9[13], x10[13], x11[13], x12[13], x13[13], x14[13], x15[13]]
  liftM (store (V ⟨50, rfl⟩) Row16Ty y13)
  let y14 : Row16 := #v[x0[14], x1[14], x2[14], x3[14], x4[14], x5[14], x6[14], x7[14], x8[14], x9[14], x10[14], x11[14], x12[14], x13[14], x14[14], x15[14]]
  liftM (store (V ⟨49, rfl⟩) Row16Ty y14)
  let y15 : Row16 := #v[x0[15], x1[15], x2[15], x3[15], x4[15], x5[15], x6[15], x7[15], x8[15], x9[15], x10[15], x11[15], x12[15], x13[15], x14[15], x15[15]]
  liftM (store (V ⟨48, rfl⟩) Row16Ty y15)
  let mask := SLLVM.bitcast (.vector 16 (.bitvec (.concrete 1)))
      (.bitvec (.concrete 16)) (SLLVM.vtrunc 1 (V ⟨16, rfl⟩))
  match LLVM.icmp .eq mask (V ⟨130, rfl⟩) with
  | .poison => throwUB
  | .value b => pure (.inr (if b = 1 then rootTarget16 V else nonrootTarget16 V))

/-- Mathematical sixteen-by-sixteen transpose, indexed by output word. -/
def columns16 (rows : Vector (Vector Word 16) 16) : State (Vector Word 16) :=
  fun i => Vector.ofFn (fun k => rows[k][i])

private theorem col0 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 0)).map PoisonOr.value = #v[PoisonOr.value rows[0][0], PoisonOr.value rows[1][0], PoisonOr.value rows[2][0], PoisonOr.value rows[3][0], PoisonOr.value rows[4][0], PoisonOr.value rows[5][0], PoisonOr.value rows[6][0], PoisonOr.value rows[7][0], PoisonOr.value rows[8][0], PoisonOr.value rows[9][0], PoisonOr.value rows[10][0], PoisonOr.value rows[11][0], PoisonOr.value rows[12][0], PoisonOr.value rows[13][0], PoisonOr.value rows[14][0], PoisonOr.value rows[15][0]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col1 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 1)).map PoisonOr.value = #v[PoisonOr.value rows[0][1], PoisonOr.value rows[1][1], PoisonOr.value rows[2][1], PoisonOr.value rows[3][1], PoisonOr.value rows[4][1], PoisonOr.value rows[5][1], PoisonOr.value rows[6][1], PoisonOr.value rows[7][1], PoisonOr.value rows[8][1], PoisonOr.value rows[9][1], PoisonOr.value rows[10][1], PoisonOr.value rows[11][1], PoisonOr.value rows[12][1], PoisonOr.value rows[13][1], PoisonOr.value rows[14][1], PoisonOr.value rows[15][1]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col2 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 2)).map PoisonOr.value = #v[PoisonOr.value rows[0][2], PoisonOr.value rows[1][2], PoisonOr.value rows[2][2], PoisonOr.value rows[3][2], PoisonOr.value rows[4][2], PoisonOr.value rows[5][2], PoisonOr.value rows[6][2], PoisonOr.value rows[7][2], PoisonOr.value rows[8][2], PoisonOr.value rows[9][2], PoisonOr.value rows[10][2], PoisonOr.value rows[11][2], PoisonOr.value rows[12][2], PoisonOr.value rows[13][2], PoisonOr.value rows[14][2], PoisonOr.value rows[15][2]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col3 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 3)).map PoisonOr.value = #v[PoisonOr.value rows[0][3], PoisonOr.value rows[1][3], PoisonOr.value rows[2][3], PoisonOr.value rows[3][3], PoisonOr.value rows[4][3], PoisonOr.value rows[5][3], PoisonOr.value rows[6][3], PoisonOr.value rows[7][3], PoisonOr.value rows[8][3], PoisonOr.value rows[9][3], PoisonOr.value rows[10][3], PoisonOr.value rows[11][3], PoisonOr.value rows[12][3], PoisonOr.value rows[13][3], PoisonOr.value rows[14][3], PoisonOr.value rows[15][3]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col4 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 4)).map PoisonOr.value = #v[PoisonOr.value rows[0][4], PoisonOr.value rows[1][4], PoisonOr.value rows[2][4], PoisonOr.value rows[3][4], PoisonOr.value rows[4][4], PoisonOr.value rows[5][4], PoisonOr.value rows[6][4], PoisonOr.value rows[7][4], PoisonOr.value rows[8][4], PoisonOr.value rows[9][4], PoisonOr.value rows[10][4], PoisonOr.value rows[11][4], PoisonOr.value rows[12][4], PoisonOr.value rows[13][4], PoisonOr.value rows[14][4], PoisonOr.value rows[15][4]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col5 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 5)).map PoisonOr.value = #v[PoisonOr.value rows[0][5], PoisonOr.value rows[1][5], PoisonOr.value rows[2][5], PoisonOr.value rows[3][5], PoisonOr.value rows[4][5], PoisonOr.value rows[5][5], PoisonOr.value rows[6][5], PoisonOr.value rows[7][5], PoisonOr.value rows[8][5], PoisonOr.value rows[9][5], PoisonOr.value rows[10][5], PoisonOr.value rows[11][5], PoisonOr.value rows[12][5], PoisonOr.value rows[13][5], PoisonOr.value rows[14][5], PoisonOr.value rows[15][5]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col6 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 6)).map PoisonOr.value = #v[PoisonOr.value rows[0][6], PoisonOr.value rows[1][6], PoisonOr.value rows[2][6], PoisonOr.value rows[3][6], PoisonOr.value rows[4][6], PoisonOr.value rows[5][6], PoisonOr.value rows[6][6], PoisonOr.value rows[7][6], PoisonOr.value rows[8][6], PoisonOr.value rows[9][6], PoisonOr.value rows[10][6], PoisonOr.value rows[11][6], PoisonOr.value rows[12][6], PoisonOr.value rows[13][6], PoisonOr.value rows[14][6], PoisonOr.value rows[15][6]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col7 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 7)).map PoisonOr.value = #v[PoisonOr.value rows[0][7], PoisonOr.value rows[1][7], PoisonOr.value rows[2][7], PoisonOr.value rows[3][7], PoisonOr.value rows[4][7], PoisonOr.value rows[5][7], PoisonOr.value rows[6][7], PoisonOr.value rows[7][7], PoisonOr.value rows[8][7], PoisonOr.value rows[9][7], PoisonOr.value rows[10][7], PoisonOr.value rows[11][7], PoisonOr.value rows[12][7], PoisonOr.value rows[13][7], PoisonOr.value rows[14][7], PoisonOr.value rows[15][7]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col8 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 8)).map PoisonOr.value = #v[PoisonOr.value rows[0][8], PoisonOr.value rows[1][8], PoisonOr.value rows[2][8], PoisonOr.value rows[3][8], PoisonOr.value rows[4][8], PoisonOr.value rows[5][8], PoisonOr.value rows[6][8], PoisonOr.value rows[7][8], PoisonOr.value rows[8][8], PoisonOr.value rows[9][8], PoisonOr.value rows[10][8], PoisonOr.value rows[11][8], PoisonOr.value rows[12][8], PoisonOr.value rows[13][8], PoisonOr.value rows[14][8], PoisonOr.value rows[15][8]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col9 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 9)).map PoisonOr.value = #v[PoisonOr.value rows[0][9], PoisonOr.value rows[1][9], PoisonOr.value rows[2][9], PoisonOr.value rows[3][9], PoisonOr.value rows[4][9], PoisonOr.value rows[5][9], PoisonOr.value rows[6][9], PoisonOr.value rows[7][9], PoisonOr.value rows[8][9], PoisonOr.value rows[9][9], PoisonOr.value rows[10][9], PoisonOr.value rows[11][9], PoisonOr.value rows[12][9], PoisonOr.value rows[13][9], PoisonOr.value rows[14][9], PoisonOr.value rows[15][9]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col10 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 10)).map PoisonOr.value = #v[PoisonOr.value rows[0][10], PoisonOr.value rows[1][10], PoisonOr.value rows[2][10], PoisonOr.value rows[3][10], PoisonOr.value rows[4][10], PoisonOr.value rows[5][10], PoisonOr.value rows[6][10], PoisonOr.value rows[7][10], PoisonOr.value rows[8][10], PoisonOr.value rows[9][10], PoisonOr.value rows[10][10], PoisonOr.value rows[11][10], PoisonOr.value rows[12][10], PoisonOr.value rows[13][10], PoisonOr.value rows[14][10], PoisonOr.value rows[15][10]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col11 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 11)).map PoisonOr.value = #v[PoisonOr.value rows[0][11], PoisonOr.value rows[1][11], PoisonOr.value rows[2][11], PoisonOr.value rows[3][11], PoisonOr.value rows[4][11], PoisonOr.value rows[5][11], PoisonOr.value rows[6][11], PoisonOr.value rows[7][11], PoisonOr.value rows[8][11], PoisonOr.value rows[9][11], PoisonOr.value rows[10][11], PoisonOr.value rows[11][11], PoisonOr.value rows[12][11], PoisonOr.value rows[13][11], PoisonOr.value rows[14][11], PoisonOr.value rows[15][11]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col12 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 12)).map PoisonOr.value = #v[PoisonOr.value rows[0][12], PoisonOr.value rows[1][12], PoisonOr.value rows[2][12], PoisonOr.value rows[3][12], PoisonOr.value rows[4][12], PoisonOr.value rows[5][12], PoisonOr.value rows[6][12], PoisonOr.value rows[7][12], PoisonOr.value rows[8][12], PoisonOr.value rows[9][12], PoisonOr.value rows[10][12], PoisonOr.value rows[11][12], PoisonOr.value rows[12][12], PoisonOr.value rows[13][12], PoisonOr.value rows[14][12], PoisonOr.value rows[15][12]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col13 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 13)).map PoisonOr.value = #v[PoisonOr.value rows[0][13], PoisonOr.value rows[1][13], PoisonOr.value rows[2][13], PoisonOr.value rows[3][13], PoisonOr.value rows[4][13], PoisonOr.value rows[5][13], PoisonOr.value rows[6][13], PoisonOr.value rows[7][13], PoisonOr.value rows[8][13], PoisonOr.value rows[9][13], PoisonOr.value rows[10][13], PoisonOr.value rows[11][13], PoisonOr.value rows[12][13], PoisonOr.value rows[13][13], PoisonOr.value rows[14][13], PoisonOr.value rows[15][13]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col14 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 14)).map PoisonOr.value = #v[PoisonOr.value rows[0][14], PoisonOr.value rows[1][14], PoisonOr.value rows[2][14], PoisonOr.value rows[3][14], PoisonOr.value rows[4][14], PoisonOr.value rows[5][14], PoisonOr.value rows[6][14], PoisonOr.value rows[7][14], PoisonOr.value rows[8][14], PoisonOr.value rows[9][14], PoisonOr.value rows[10][14], PoisonOr.value rows[11][14], PoisonOr.value rows[12][14], PoisonOr.value rows[13][14], PoisonOr.value rows[14][14], PoisonOr.value rows[15][14]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private theorem col15 (rows : Vector (Vector Word 16) 16) :
    (columns16 rows (Fin.ofNat 16 15)).map PoisonOr.value = #v[PoisonOr.value rows[0][15], PoisonOr.value rows[1][15], PoisonOr.value rows[2][15], PoisonOr.value rows[3][15], PoisonOr.value rows[4][15], PoisonOr.value rows[5][15], PoisonOr.value rows[6][15], PoisonOr.value rows[7][15], PoisonOr.value rows[8][15], PoisonOr.value rows[9][15], PoisonOr.value rows[10][15], PoisonOr.value rows[11][15], PoisonOr.value rows[12][15], PoisonOr.value rows[13][15], PoisonOr.value rows[14][15], PoisonOr.value rows[15][15]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns16, Vector.getElem_ofFn]

private def storeVectors {n : Nat} (out : Pointer) (cols : State (Vector Word n)) : Nat → EffectM Unit
  | 0 => pure ()
  | k+1 => do
    storeVectors out cols k
    liftM (store (.value (out.withOffset (BitVec.ofNat 64 (4*n*k))))
      (.vector n (.bitvec (.concrete 32))) ((cols (Fin.ofNat 16 k)).map PoisonOr.value))

private abbrev stores16 (out : Pointer) (cols : State (Vector Word 16)) := storeVectors out cols

private def explicitStores16 (out : Pointer) (rows : Vector (Vector Word 16) 16) : EffectM Unit := do
  liftM (store (.value (out.withOffset 0)) Row16Ty #v[PoisonOr.value rows[0][0], PoisonOr.value rows[1][0], PoisonOr.value rows[2][0], PoisonOr.value rows[3][0], PoisonOr.value rows[4][0], PoisonOr.value rows[5][0], PoisonOr.value rows[6][0], PoisonOr.value rows[7][0], PoisonOr.value rows[8][0], PoisonOr.value rows[9][0], PoisonOr.value rows[10][0], PoisonOr.value rows[11][0], PoisonOr.value rows[12][0], PoisonOr.value rows[13][0], PoisonOr.value rows[14][0], PoisonOr.value rows[15][0]])
  liftM (store (.value (out.withOffset 64)) Row16Ty #v[PoisonOr.value rows[0][1], PoisonOr.value rows[1][1], PoisonOr.value rows[2][1], PoisonOr.value rows[3][1], PoisonOr.value rows[4][1], PoisonOr.value rows[5][1], PoisonOr.value rows[6][1], PoisonOr.value rows[7][1], PoisonOr.value rows[8][1], PoisonOr.value rows[9][1], PoisonOr.value rows[10][1], PoisonOr.value rows[11][1], PoisonOr.value rows[12][1], PoisonOr.value rows[13][1], PoisonOr.value rows[14][1], PoisonOr.value rows[15][1]])
  liftM (store (.value (out.withOffset 128)) Row16Ty #v[PoisonOr.value rows[0][2], PoisonOr.value rows[1][2], PoisonOr.value rows[2][2], PoisonOr.value rows[3][2], PoisonOr.value rows[4][2], PoisonOr.value rows[5][2], PoisonOr.value rows[6][2], PoisonOr.value rows[7][2], PoisonOr.value rows[8][2], PoisonOr.value rows[9][2], PoisonOr.value rows[10][2], PoisonOr.value rows[11][2], PoisonOr.value rows[12][2], PoisonOr.value rows[13][2], PoisonOr.value rows[14][2], PoisonOr.value rows[15][2]])
  liftM (store (.value (out.withOffset 192)) Row16Ty #v[PoisonOr.value rows[0][3], PoisonOr.value rows[1][3], PoisonOr.value rows[2][3], PoisonOr.value rows[3][3], PoisonOr.value rows[4][3], PoisonOr.value rows[5][3], PoisonOr.value rows[6][3], PoisonOr.value rows[7][3], PoisonOr.value rows[8][3], PoisonOr.value rows[9][3], PoisonOr.value rows[10][3], PoisonOr.value rows[11][3], PoisonOr.value rows[12][3], PoisonOr.value rows[13][3], PoisonOr.value rows[14][3], PoisonOr.value rows[15][3]])
  liftM (store (.value (out.withOffset 256)) Row16Ty #v[PoisonOr.value rows[0][4], PoisonOr.value rows[1][4], PoisonOr.value rows[2][4], PoisonOr.value rows[3][4], PoisonOr.value rows[4][4], PoisonOr.value rows[5][4], PoisonOr.value rows[6][4], PoisonOr.value rows[7][4], PoisonOr.value rows[8][4], PoisonOr.value rows[9][4], PoisonOr.value rows[10][4], PoisonOr.value rows[11][4], PoisonOr.value rows[12][4], PoisonOr.value rows[13][4], PoisonOr.value rows[14][4], PoisonOr.value rows[15][4]])
  liftM (store (.value (out.withOffset 320)) Row16Ty #v[PoisonOr.value rows[0][5], PoisonOr.value rows[1][5], PoisonOr.value rows[2][5], PoisonOr.value rows[3][5], PoisonOr.value rows[4][5], PoisonOr.value rows[5][5], PoisonOr.value rows[6][5], PoisonOr.value rows[7][5], PoisonOr.value rows[8][5], PoisonOr.value rows[9][5], PoisonOr.value rows[10][5], PoisonOr.value rows[11][5], PoisonOr.value rows[12][5], PoisonOr.value rows[13][5], PoisonOr.value rows[14][5], PoisonOr.value rows[15][5]])
  liftM (store (.value (out.withOffset 384)) Row16Ty #v[PoisonOr.value rows[0][6], PoisonOr.value rows[1][6], PoisonOr.value rows[2][6], PoisonOr.value rows[3][6], PoisonOr.value rows[4][6], PoisonOr.value rows[5][6], PoisonOr.value rows[6][6], PoisonOr.value rows[7][6], PoisonOr.value rows[8][6], PoisonOr.value rows[9][6], PoisonOr.value rows[10][6], PoisonOr.value rows[11][6], PoisonOr.value rows[12][6], PoisonOr.value rows[13][6], PoisonOr.value rows[14][6], PoisonOr.value rows[15][6]])
  liftM (store (.value (out.withOffset 448)) Row16Ty #v[PoisonOr.value rows[0][7], PoisonOr.value rows[1][7], PoisonOr.value rows[2][7], PoisonOr.value rows[3][7], PoisonOr.value rows[4][7], PoisonOr.value rows[5][7], PoisonOr.value rows[6][7], PoisonOr.value rows[7][7], PoisonOr.value rows[8][7], PoisonOr.value rows[9][7], PoisonOr.value rows[10][7], PoisonOr.value rows[11][7], PoisonOr.value rows[12][7], PoisonOr.value rows[13][7], PoisonOr.value rows[14][7], PoisonOr.value rows[15][7]])
  liftM (store (.value (out.withOffset 512)) Row16Ty #v[PoisonOr.value rows[0][8], PoisonOr.value rows[1][8], PoisonOr.value rows[2][8], PoisonOr.value rows[3][8], PoisonOr.value rows[4][8], PoisonOr.value rows[5][8], PoisonOr.value rows[6][8], PoisonOr.value rows[7][8], PoisonOr.value rows[8][8], PoisonOr.value rows[9][8], PoisonOr.value rows[10][8], PoisonOr.value rows[11][8], PoisonOr.value rows[12][8], PoisonOr.value rows[13][8], PoisonOr.value rows[14][8], PoisonOr.value rows[15][8]])
  liftM (store (.value (out.withOffset 576)) Row16Ty #v[PoisonOr.value rows[0][9], PoisonOr.value rows[1][9], PoisonOr.value rows[2][9], PoisonOr.value rows[3][9], PoisonOr.value rows[4][9], PoisonOr.value rows[5][9], PoisonOr.value rows[6][9], PoisonOr.value rows[7][9], PoisonOr.value rows[8][9], PoisonOr.value rows[9][9], PoisonOr.value rows[10][9], PoisonOr.value rows[11][9], PoisonOr.value rows[12][9], PoisonOr.value rows[13][9], PoisonOr.value rows[14][9], PoisonOr.value rows[15][9]])
  liftM (store (.value (out.withOffset 640)) Row16Ty #v[PoisonOr.value rows[0][10], PoisonOr.value rows[1][10], PoisonOr.value rows[2][10], PoisonOr.value rows[3][10], PoisonOr.value rows[4][10], PoisonOr.value rows[5][10], PoisonOr.value rows[6][10], PoisonOr.value rows[7][10], PoisonOr.value rows[8][10], PoisonOr.value rows[9][10], PoisonOr.value rows[10][10], PoisonOr.value rows[11][10], PoisonOr.value rows[12][10], PoisonOr.value rows[13][10], PoisonOr.value rows[14][10], PoisonOr.value rows[15][10]])
  liftM (store (.value (out.withOffset 704)) Row16Ty #v[PoisonOr.value rows[0][11], PoisonOr.value rows[1][11], PoisonOr.value rows[2][11], PoisonOr.value rows[3][11], PoisonOr.value rows[4][11], PoisonOr.value rows[5][11], PoisonOr.value rows[6][11], PoisonOr.value rows[7][11], PoisonOr.value rows[8][11], PoisonOr.value rows[9][11], PoisonOr.value rows[10][11], PoisonOr.value rows[11][11], PoisonOr.value rows[12][11], PoisonOr.value rows[13][11], PoisonOr.value rows[14][11], PoisonOr.value rows[15][11]])
  liftM (store (.value (out.withOffset 768)) Row16Ty #v[PoisonOr.value rows[0][12], PoisonOr.value rows[1][12], PoisonOr.value rows[2][12], PoisonOr.value rows[3][12], PoisonOr.value rows[4][12], PoisonOr.value rows[5][12], PoisonOr.value rows[6][12], PoisonOr.value rows[7][12], PoisonOr.value rows[8][12], PoisonOr.value rows[9][12], PoisonOr.value rows[10][12], PoisonOr.value rows[11][12], PoisonOr.value rows[12][12], PoisonOr.value rows[13][12], PoisonOr.value rows[14][12], PoisonOr.value rows[15][12]])
  liftM (store (.value (out.withOffset 832)) Row16Ty #v[PoisonOr.value rows[0][13], PoisonOr.value rows[1][13], PoisonOr.value rows[2][13], PoisonOr.value rows[3][13], PoisonOr.value rows[4][13], PoisonOr.value rows[5][13], PoisonOr.value rows[6][13], PoisonOr.value rows[7][13], PoisonOr.value rows[8][13], PoisonOr.value rows[9][13], PoisonOr.value rows[10][13], PoisonOr.value rows[11][13], PoisonOr.value rows[12][13], PoisonOr.value rows[13][13], PoisonOr.value rows[14][13], PoisonOr.value rows[15][13]])
  liftM (store (.value (out.withOffset 896)) Row16Ty #v[PoisonOr.value rows[0][14], PoisonOr.value rows[1][14], PoisonOr.value rows[2][14], PoisonOr.value rows[3][14], PoisonOr.value rows[4][14], PoisonOr.value rows[5][14], PoisonOr.value rows[6][14], PoisonOr.value rows[7][14], PoisonOr.value rows[8][14], PoisonOr.value rows[9][14], PoisonOr.value rows[10][14], PoisonOr.value rows[11][14], PoisonOr.value rows[12][14], PoisonOr.value rows[13][14], PoisonOr.value rows[14][14], PoisonOr.value rows[15][14]])
  liftM (store (.value (out.withOffset 960)) Row16Ty #v[PoisonOr.value rows[0][15], PoisonOr.value rows[1][15], PoisonOr.value rows[2][15], PoisonOr.value rows[3][15], PoisonOr.value rows[4][15], PoisonOr.value rows[5][15], PoisonOr.value rows[6][15], PoisonOr.value rows[7][15], PoisonOr.value rows[8][15], PoisonOr.value rows[9][15], PoisonOr.value rows[10][15], PoisonOr.value rows[11][15], PoisonOr.value rows[12][15], PoisonOr.value rows[13][15], PoisonOr.value rows[14][15], PoisonOr.value rows[15][15]])

set_option maxHeartbeats 1000000 in
private theorem stores16_eq (out : Pointer) (rows : Vector (Vector Word 16) 16) :
    stores16 out (columns16 rows) 16 = explicitStores16 out rows := by
  simp only [stores16, storeVectors, explicitStores16, pure_bind, bind_assoc]
  rw [col0, col1, col2, col3, col4, col5, col6, col7, col8, col9, col10, col11, col12, col13, col14, col15]
  rfl

private theorem storeVectors_run {n : Nat} (out : Pointer) (cols : State (Vector Word n))
    (count : Nat) (s : GlobalState)
    (hfit : ∀ k < count, Fits s.mem (out.withOffset (BitVec.ofNat 64 (4*n*k))) (32*n)) :
    StateT.run (storeVectors out cols count) s =
      .value ((), {s with mem := outputMem out cols count s.mem}) := by
  induction count with
  | zero => rfl
  | succ k ih =>
    simp only [storeVectors, EffectM.run_bind, ih (fun i hi => hfit i (by omega)),
      PoisonOr.value_bind]
    rw [run_liftM (s := {s with mem := outputMem out cols k s.mem})
      (run_store (flatten_packBits (cols (Fin.ofNat 16 k)))
        (fits_outputMem out cols k (hfit k (by omega))))]
    rfl

private theorem stores16_run (out : Pointer) (cols : State (Vector Word 16))
    (count : Nat) (s : GlobalState)
    (hfit : ∀ k < count, Fits s.mem (out.withOffset (BitVec.ofNat 64 (64*k))) 512) :
    StateT.run (stores16 out cols count) s =
      .value ((), {s with mem := outputMem out cols count s.mem}) :=
  storeVectors_run out cols count s hfit

structure Env16 (V : InCtx16.Valuation) (out : Pointer)
    (inputs : Fin 16 → Pointer) (mask : BitVec 16) : Prop where
  input0 : V ⟨15, rfl⟩ = .value (inputs 0)
  input1 : V ⟨14, rfl⟩ = .value (inputs 1)
  input2 : V ⟨13, rfl⟩ = .value (inputs 2)
  input3 : V ⟨12, rfl⟩ = .value (inputs 3)
  input4 : V ⟨11, rfl⟩ = .value (inputs 4)
  input5 : V ⟨10, rfl⟩ = .value (inputs 5)
  input6 : V ⟨9, rfl⟩ = .value (inputs 6)
  input7 : V ⟨8, rfl⟩ = .value (inputs 7)
  input8 : V ⟨7, rfl⟩ = .value (inputs 8)
  input9 : V ⟨6, rfl⟩ = .value (inputs 9)
  input10 : V ⟨5, rfl⟩ = .value (inputs 10)
  input11 : V ⟨4, rfl⟩ = .value (inputs 11)
  input12 : V ⟨3, rfl⟩ = .value (inputs 12)
  input13 : V ⟨2, rfl⟩ = .value (inputs 13)
  input14 : V ⟨1, rfl⟩ = .value (inputs 14)
  input15 : V ⟨0, rfl⟩ = .value (inputs 15)
  ptr0 : V ⟨79, rfl⟩ = .value (out.withOffset 0)
  ptr1 : V ⟨62, rfl⟩ = .value (out.withOffset 64)
  ptr2 : V ⟨61, rfl⟩ = .value (out.withOffset 128)
  ptr3 : V ⟨60, rfl⟩ = .value (out.withOffset 192)
  ptr4 : V ⟨59, rfl⟩ = .value (out.withOffset 256)
  ptr5 : V ⟨58, rfl⟩ = .value (out.withOffset 320)
  ptr6 : V ⟨57, rfl⟩ = .value (out.withOffset 384)
  ptr7 : V ⟨56, rfl⟩ = .value (out.withOffset 448)
  ptr8 : V ⟨55, rfl⟩ = .value (out.withOffset 512)
  ptr9 : V ⟨54, rfl⟩ = .value (out.withOffset 576)
  ptr10 : V ⟨53, rfl⟩ = .value (out.withOffset 640)
  ptr11 : V ⟨52, rfl⟩ = .value (out.withOffset 704)
  ptr12 : V ⟨51, rfl⟩ = .value (out.withOffset 768)
  ptr13 : V ⟨50, rfl⟩ = .value (out.withOffset 832)
  ptr14 : V ⟨49, rfl⟩ = .value (out.withOffset 896)
  ptr15 : V ⟨48, rfl⟩ = .value (out.withOffset 960)
  active : SLLVM.bitcast (.vector 16 (.bitvec (.concrete 1)))
    (.bitvec (.concrete 16)) (SLLVM.vtrunc 1 (V ⟨16, rfl⟩)) = .value mask
  zero : V ⟨130, rfl⟩ = .value 0#16

/-- The compiler's vector-to-i16 bitcast packs the sixteen defined active bits. -/
theorem bitcast_active16 (active : Vector (BitVec 1) 16) :
    SLLVM.bitcast (.vector 16 (.bitvec (.concrete 1))) (.bitvec (.concrete 16))
      (active.map PoisonOr.value) = .value (packBits active) := by
  rw [bitcast_of_defined]
  · rfl
  · intro i
    show LLVM.Ty.ofBitvec ((active.map PoisonOr.value)[i.val]) ≠ .poison
    rw [Vector.getElem_map]
    exact PoisonOr.value_ne_poison _

/-- The compiler truncates each frozen byte mask to its low bit before packing. -/
theorem trunc_active16 (active : Vector (BitVec 8) 16) :
    SLLVM.vtrunc 1 (active.map PoisonOr.value) =
      (active.map (·.truncate 1)).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [SLLVM.vtrunc, LLVM.trunc, LLVM.trunc?]

theorem bitcast_active16_bytes (active : Vector (BitVec 8) 16) :
    SLLVM.bitcast (.vector 16 (.bitvec (.concrete 1))) (.bitvec (.concrete 16))
      (SLLVM.vtrunc 1 (active.map PoisonOr.value)) =
        .value (packBits (active.map (·.truncate 1))) := by
  rw [trunc_active16]
  exact bitcast_active16 _

/-- A zero packed active mask is exactly the all-inactive condition. -/
theorem active16_zero_iff (active : Vector (BitVec 1) 16) :
    packBits active = 0 ↔ ∀ i : Fin 16, active[i] = 0 := by
  constructor
  · intro h i
    have hi := extract_packBits active i
    rw [h] at hi
    simpa using hi.symm
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have he := congrArg (fun x : BitVec 1 => x[0]) (extract_packBits active ⟨i, hi⟩)
    simp only [← BitVec.getLsbD_eq_getElem]
    simpa [BitVec.getElem_extractLsb', h] using he


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem spec16_run (V : InCtx16.Valuation) (out : Pointer) (inputs : Fin 16 → Pointer)
    (rows : Vector (Vector Word 16) 16) (mask : BitVec 16)
    (hV : Env16 V out inputs mask) (s : GlobalState)
    (hf : ∀ i, Fits s.mem (inputs i) 512)
    (hr : ∀ i, readWord? (inputs i) 512 s.mem = some (packBits rows[i]))
    (hfit : ∀ k < 16, Fits s.mem (out.withOffset (BitVec.ofNat 64 (64*k))) 512) :
    StateT.run (transpose16Spec V) s =
      .value (.inr (if mask = 0 then rootTarget16 V else nonrootTarget16 V),
        {s with mem := outputMem out (columns16 rows) 16 s.mem}) := by
  unfold transpose16Spec
  simp only [hV.active, hV.zero, hV.input0, hV.input1, hV.input2, hV.input3, hV.input4, hV.input5, hV.input6, hV.input7, hV.input8, hV.input9, hV.input10, hV.input11, hV.input12, hV.input13, hV.input14, hV.input15, hV.ptr0, hV.ptr1, hV.ptr2, hV.ptr3, hV.ptr4, hV.ptr5, hV.ptr6, hV.ptr7, hV.ptr8, hV.ptr9, hV.ptr10, hV.ptr11, hV.ptr12, hV.ptr13, hV.ptr14, hV.ptr15]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[0] (hf 0) (hr 0))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[1] (hf 1) (hr 1))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[2] (hf 2) (hr 2))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[3] (hf 3) (hr 3))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[4] (hf 4) (hr 4))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[5] (hf 5) (hr 5))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[6] (hf 6) (hr 6))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[7] (hf 7) (hr 7))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[8] (hf 8) (hr 8))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[9] (hf 9) (hr 9))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[10] (hf 10) (hr 10))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[11] (hf 11) (hr 11))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[12] (hf 12) (hr 12))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[13] (hf 13) (hr 13))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[14] (hf 14) (hr 14))]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[15] (hf 15) (hr 15))]
  simp only [PoisonOr.value_bind]
  simp only [Vector.getElem_map]
  have h := stores16_run out (columns16 rows) 16 s hfit
  have h' (r : HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) :
      StateT.run (stores16 out (columns16 rows) 16 >>= fun _ => pure r) s =
        .value (r, {s with mem := outputMem out (columns16 rows) 16 s.mem}) := by
    rw [EffectM.run_bind, h]
    rfl
  rw [stores16_eq] at h'
  simp only [explicitStores16, bind_assoc] at h'
  by_cases hm : mask = 0
  · have hc : LLVM.icmp .eq (.value mask) (.value 0#16) = .value 1#1 := by
      subst hm
      rfl
    rw [hc]
    simp only [hm, ↓reduceIte]
    exact h' (.inr (rootTarget16 V))
  · have hc : LLVM.icmp .eq (.value mask) (.value 0#16) = .value 0#1 := by
      simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ofBool]
      exact hm
    rw [hc]
    simp only [hm, show ¬(0#1 = 1) by decide, ↓reduceIte]
    exact h' (.inr (nonrootTarget16 V))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Refinement of the actual compiled bb3, including all input loads. -/
theorem transpose16_denote (V : InCtx16.Valuation) :
    (do let (_, r) ← agave_batch_16.cfgBlock_2.denote V; pure r) = transpose16Spec V := by
  simp (config := {maxSteps := 2000000}) only [transpose16Spec, BlockCom.denote,
    Terminator.denote, targetIte, rootTarget16, nonrootTarget16,
    simp_denote, simp_sllvm, bind_map_left]
  simp (config := {maxSteps := 2000000}) only [hvConsAppend, hvNilAppend, simp_spine]
  simp (config := {maxSteps := 2000000}) only [shuffle0, shuffle1, shuffle2, shuffle3, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp (config := {maxSteps := 2000000}) only [bind_pure]
  rfl

private theorem run_of_project {α β : Type} (x : EffectM (α × β))
    (s t : GlobalState) (b : β)
    (h : StateT.run (do let (_, r) ← x; pure r) s = .value (b, t)) :
    ∃ a, StateT.run x s = .value ((a, b), t) := by
  cases hx : StateT.run x s using PoisonOr.casesOn' with
  | poison =>
    simp only [EffectM.run_bind, hx, PoisonOr.poison_bind] at h
    exact (PoisonOr.poison_ne_value _ h).elim
  | value val =>
    rcases val with ⟨⟨a, b'⟩, t'⟩
    simp only [EffectM.run_bind, hx, PoisonOr.value_bind, EffectM.run_pure,
      PoisonOr.value_inj, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨a, rfl⟩

/-- Exact successful execution of the AVX512 batch transpose block and
its root/nonroot edge, including all sixteen scratch writes. -/
theorem transpose16_run (V : InCtx16.Valuation) (out : Pointer) (inputs : Fin 16 → Pointer)
    (rows : Vector (Vector Word 16) 16) (mask : BitVec 16)
    (hV : Env16 V out inputs mask) (s : GlobalState)
    (hf : ∀ i, Fits s.mem (inputs i) 512)
    (hr : ∀ i, readWord? (inputs i) 512 s.mem = some (packBits rows[i]))
    (hfit : ∀ k < 16, Fits s.mem (out.withOffset (BitVec.ofNat 64 (64*k))) 512) :
    ∃ V', StateT.run (agave_batch_16.cfgBlock_2.denote V) s =
      .value ((V', .inr (if mask = 0 then rootTarget16 V else nonrootTarget16 V)),
        {s with mem := outputMem out (columns16 rows) 16 s.mem}) := by
  apply run_of_project
  rw [transpose16_denote]
  exact spec16_run V out inputs rows mask hV s hf hr hfit

theorem transpose16_frame (out : Pointer) (rows : Vector (Vector Word 16) 16)
    (m : MemoryState) (q : BlockId) (hq : q ≠ out.id) :
    (outputMem out (columns16 rows) 16 m).live? q = m.live? q :=
  outputMem_frame out (columns16 rows) 16 m q hq

end AgaveLatticeHash.MLIR.BatchTranspose16
