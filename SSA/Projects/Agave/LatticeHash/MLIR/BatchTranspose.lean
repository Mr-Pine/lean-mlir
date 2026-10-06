import Mathlib.Tactic.IntervalCases
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionMemory
import SSA.Projects.Firedancer.MLIR.DenoteStep

namespace AgaveLatticeHash.MLIR.BatchTranspose
open LeanMLIR SLLVM
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev InCtx8 := blockInput agave_batch_8.cfgBlock_9
abbrev Row8 := Vector (LLVM.IntW 32) 8
abbrev Row8Ty : LLVM.Ty := .vector 8 (.bitvec (.concrete 32))

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

private theorem shuffle0 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 8, 1, 9, 4, 12, 5, 13] a b = #v[a[0], b[0], a[1], b[1], a[4], b[4], a[5], b[5]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle1 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 10, 3, 11, 6, 14, 7, 15] a b = #v[a[2], b[2], a[3], b[3], a[6], b[6], a[7], b[7]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle2 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 8, 9, 4, 5, 12, 13] a b = #v[a[0], a[1], b[0], b[1], a[4], a[5], b[4], b[5]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle3 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 3, 10, 11, 6, 7, 14, 15] a b = #v[a[2], a[3], b[2], b[3], a[6], a[7], b[6], b[7]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle4 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11] a b = #v[a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle5 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15] a b = #v[a[4], a[5], a[6], a[7], b[4], b[5], b[6], b[7]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

def rootTarget8 (V : InCtx8.Valuation) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨18, rfl, [V ⟨28, rfl⟩,V ⟨27, rfl⟩,V ⟨26, rfl⟩,V ⟨25, rfl⟩,V ⟨24, rfl⟩,V ⟨23, rfl⟩,V ⟨22, rfl⟩,V ⟨21, rfl⟩,V ⟨17, rfl⟩,V ⟨16, rfl⟩]ₕ⟩
def nonrootTarget8 (V : InCtx8.Valuation) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨19, rfl, [V ⟨28, rfl⟩,V ⟨27, rfl⟩,V ⟨26, rfl⟩,V ⟨25, rfl⟩,V ⟨24, rfl⟩,V ⟨23, rfl⟩,V ⟨22, rfl⟩,V ⟨21, rfl⟩,V ⟨20, rfl⟩,V ⟨19, rfl⟩,V ⟨18, rfl⟩,V ⟨17, rfl⟩,V ⟨16, rfl⟩]ₕ⟩

/-- The compiler block's mathematical column stores, retaining poison-aware
loads, stores and the exact root/nonroot successor arguments. -/
def transpose8Spec (V : InCtx8.Valuation) :
    EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) := do
  let x0 : Row8 := V ⟨7, rfl⟩
  let x1 : Row8 := V ⟨6, rfl⟩
  let x2 : Row8 := V ⟨5, rfl⟩
  let x3 : Row8 := V ⟨4, rfl⟩
  let x4 : Row8 := V ⟨3, rfl⟩
  let x5 : Row8 := V ⟨2, rfl⟩
  let x6 : Row8 ← liftM (load (gep (V ⟨46, rfl⟩) 4 0 (V ⟨1, rfl⟩)) Row8Ty)
  let x7 : Row8 ← liftM (load (gep (V ⟨45, rfl⟩) 4 0 (V ⟨0, rfl⟩)) Row8Ty)
  liftM (store (V ⟨53, rfl⟩) Row8Ty (V ⟨15, rfl⟩))
  liftM (store (V ⟨43, rfl⟩) Row8Ty (V ⟨14, rfl⟩))
  liftM (store (V ⟨42, rfl⟩) Row8Ty (V ⟨13, rfl⟩))
  liftM (store (V ⟨41, rfl⟩) Row8Ty (V ⟨12, rfl⟩))
  liftM (store (V ⟨40, rfl⟩) Row8Ty (V ⟨11, rfl⟩))
  liftM (store (V ⟨39, rfl⟩) Row8Ty (V ⟨10, rfl⟩))
  liftM (store (V ⟨38, rfl⟩) Row8Ty (V ⟨9, rfl⟩))
  liftM (store (V ⟨37, rfl⟩) Row8Ty (V ⟨8, rfl⟩))
  let y0 : Row8 := #v[x0[0], x1[0], x2[0], x3[0], x4[0], x5[0], x6[0], x7[0]]
  liftM (store (V ⟨36, rfl⟩) Row8Ty y0)
  let y1 : Row8 := #v[x0[1], x1[1], x2[1], x3[1], x4[1], x5[1], x6[1], x7[1]]
  liftM (store (V ⟨35, rfl⟩) Row8Ty y1)
  let y2 : Row8 := #v[x0[2], x1[2], x2[2], x3[2], x4[2], x5[2], x6[2], x7[2]]
  liftM (store (V ⟨34, rfl⟩) Row8Ty y2)
  let y3 : Row8 := #v[x0[3], x1[3], x2[3], x3[3], x4[3], x5[3], x6[3], x7[3]]
  liftM (store (V ⟨33, rfl⟩) Row8Ty y3)
  let y4 : Row8 := #v[x0[4], x1[4], x2[4], x3[4], x4[4], x5[4], x6[4], x7[4]]
  liftM (store (V ⟨32, rfl⟩) Row8Ty y4)
  let y5 : Row8 := #v[x0[5], x1[5], x2[5], x3[5], x4[5], x5[5], x6[5], x7[5]]
  liftM (store (V ⟨31, rfl⟩) Row8Ty y5)
  let y6 : Row8 := #v[x0[6], x1[6], x2[6], x3[6], x4[6], x5[6], x6[6], x7[6]]
  liftM (store (V ⟨30, rfl⟩) Row8Ty y6)
  let y7 : Row8 := #v[x0[7], x1[7], x2[7], x3[7], x4[7], x5[7], x6[7], x7[7]]
  liftM (store (V ⟨29, rfl⟩) Row8Ty y7)
  let mask := SLLVM.bitcast (.vector 8 (.bitvec (.concrete 1)))
      (.bitvec (.concrete 8)) (V ⟨18, rfl⟩)
  match LLVM.icmp .eq mask (V ⟨78, rfl⟩) with
  | .poison => throwUB
  | .value b => pure (.inr (if b = 1 then rootTarget8 V else nonrootTarget8 V))


open Firedancer Blake3Compression CompressionExit
/-- The complete sixteen-word message; the first half is already transposed
on entry and the second half is the mathematical transpose of eight rows. -/
def columns8 (lo rows : Vector (Vector Word 8) 8) : State (Vector Word 8) :=
  fun i => if h : i.val < 8 then lo[i.val] else
    Vector.ofFn (fun k : Fin 8 => rows[k][i.val - 8]'(by omega))

private theorem col0 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 0)).map PoisonOr.value = (lo[0]).map PoisonOr.value := by
  rfl

private theorem col1 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 1)).map PoisonOr.value = (lo[1]).map PoisonOr.value := by
  rfl

private theorem col2 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 2)).map PoisonOr.value = (lo[2]).map PoisonOr.value := by
  rfl

private theorem col3 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 3)).map PoisonOr.value = (lo[3]).map PoisonOr.value := by
  rfl

private theorem col4 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 4)).map PoisonOr.value = (lo[4]).map PoisonOr.value := by
  rfl

private theorem col5 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 5)).map PoisonOr.value = (lo[5]).map PoisonOr.value := by
  rfl

private theorem col6 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 6)).map PoisonOr.value = (lo[6]).map PoisonOr.value := by
  rfl

private theorem col7 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 7)).map PoisonOr.value = (lo[7]).map PoisonOr.value := by
  rfl

private theorem col8 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 8)).map PoisonOr.value = #v[PoisonOr.value rows[0][0], PoisonOr.value rows[1][0], PoisonOr.value rows[2][0], PoisonOr.value rows[3][0], PoisonOr.value rows[4][0], PoisonOr.value rows[5][0], PoisonOr.value rows[6][0], PoisonOr.value rows[7][0]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns8, Vector.getElem_ofFn]

private theorem col9 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 9)).map PoisonOr.value = #v[PoisonOr.value rows[0][1], PoisonOr.value rows[1][1], PoisonOr.value rows[2][1], PoisonOr.value rows[3][1], PoisonOr.value rows[4][1], PoisonOr.value rows[5][1], PoisonOr.value rows[6][1], PoisonOr.value rows[7][1]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns8, Vector.getElem_ofFn]

private theorem col10 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 10)).map PoisonOr.value = #v[PoisonOr.value rows[0][2], PoisonOr.value rows[1][2], PoisonOr.value rows[2][2], PoisonOr.value rows[3][2], PoisonOr.value rows[4][2], PoisonOr.value rows[5][2], PoisonOr.value rows[6][2], PoisonOr.value rows[7][2]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns8, Vector.getElem_ofFn]

private theorem col11 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 11)).map PoisonOr.value = #v[PoisonOr.value rows[0][3], PoisonOr.value rows[1][3], PoisonOr.value rows[2][3], PoisonOr.value rows[3][3], PoisonOr.value rows[4][3], PoisonOr.value rows[5][3], PoisonOr.value rows[6][3], PoisonOr.value rows[7][3]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns8, Vector.getElem_ofFn]

private theorem col12 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 12)).map PoisonOr.value = #v[PoisonOr.value rows[0][4], PoisonOr.value rows[1][4], PoisonOr.value rows[2][4], PoisonOr.value rows[3][4], PoisonOr.value rows[4][4], PoisonOr.value rows[5][4], PoisonOr.value rows[6][4], PoisonOr.value rows[7][4]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns8, Vector.getElem_ofFn]

private theorem col13 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 13)).map PoisonOr.value = #v[PoisonOr.value rows[0][5], PoisonOr.value rows[1][5], PoisonOr.value rows[2][5], PoisonOr.value rows[3][5], PoisonOr.value rows[4][5], PoisonOr.value rows[5][5], PoisonOr.value rows[6][5], PoisonOr.value rows[7][5]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns8, Vector.getElem_ofFn]

private theorem col14 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 14)).map PoisonOr.value = #v[PoisonOr.value rows[0][6], PoisonOr.value rows[1][6], PoisonOr.value rows[2][6], PoisonOr.value rows[3][6], PoisonOr.value rows[4][6], PoisonOr.value rows[5][6], PoisonOr.value rows[6][6], PoisonOr.value rows[7][6]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns8, Vector.getElem_ofFn]

private theorem col15 (lo rows : Vector (Vector Word 8) 8) :
    (columns8 lo rows (Fin.ofNat 16 15)).map PoisonOr.value = #v[PoisonOr.value rows[0][7], PoisonOr.value rows[1][7], PoisonOr.value rows[2][7], PoisonOr.value rows[3][7], PoisonOr.value rows[4][7], PoisonOr.value rows[5][7], PoisonOr.value rows[6][7], PoisonOr.value rows[7][7]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [columns8, Vector.getElem_ofFn]

private def stores8 (out : Pointer) (cols : State (Vector Word 8)) : Nat → EffectM Unit
  | 0 => pure ()
  | k+1 => do
    stores8 out cols k
    liftM (store (.value (out.withOffset (BitVec.ofNat 64 (32*k)))) Row8Ty
      ((cols (Fin.ofNat 16 k)).map PoisonOr.value))

private def explicitStores8 (out : Pointer) (lo rows : Vector (Vector Word 8) 8) : EffectM Unit := do
  liftM (store (.value (out.withOffset 0)) Row8Ty ((lo[0]).map PoisonOr.value))
  liftM (store (.value (out.withOffset 32)) Row8Ty ((lo[1]).map PoisonOr.value))
  liftM (store (.value (out.withOffset 64)) Row8Ty ((lo[2]).map PoisonOr.value))
  liftM (store (.value (out.withOffset 96)) Row8Ty ((lo[3]).map PoisonOr.value))
  liftM (store (.value (out.withOffset 128)) Row8Ty ((lo[4]).map PoisonOr.value))
  liftM (store (.value (out.withOffset 160)) Row8Ty ((lo[5]).map PoisonOr.value))
  liftM (store (.value (out.withOffset 192)) Row8Ty ((lo[6]).map PoisonOr.value))
  liftM (store (.value (out.withOffset 224)) Row8Ty ((lo[7]).map PoisonOr.value))
  liftM (store (.value (out.withOffset 256)) Row8Ty (#v[PoisonOr.value rows[0][0], PoisonOr.value rows[1][0], PoisonOr.value rows[2][0], PoisonOr.value rows[3][0], PoisonOr.value rows[4][0], PoisonOr.value rows[5][0], PoisonOr.value rows[6][0], PoisonOr.value rows[7][0]]))
  liftM (store (.value (out.withOffset 288)) Row8Ty (#v[PoisonOr.value rows[0][1], PoisonOr.value rows[1][1], PoisonOr.value rows[2][1], PoisonOr.value rows[3][1], PoisonOr.value rows[4][1], PoisonOr.value rows[5][1], PoisonOr.value rows[6][1], PoisonOr.value rows[7][1]]))
  liftM (store (.value (out.withOffset 320)) Row8Ty (#v[PoisonOr.value rows[0][2], PoisonOr.value rows[1][2], PoisonOr.value rows[2][2], PoisonOr.value rows[3][2], PoisonOr.value rows[4][2], PoisonOr.value rows[5][2], PoisonOr.value rows[6][2], PoisonOr.value rows[7][2]]))
  liftM (store (.value (out.withOffset 352)) Row8Ty (#v[PoisonOr.value rows[0][3], PoisonOr.value rows[1][3], PoisonOr.value rows[2][3], PoisonOr.value rows[3][3], PoisonOr.value rows[4][3], PoisonOr.value rows[5][3], PoisonOr.value rows[6][3], PoisonOr.value rows[7][3]]))
  liftM (store (.value (out.withOffset 384)) Row8Ty (#v[PoisonOr.value rows[0][4], PoisonOr.value rows[1][4], PoisonOr.value rows[2][4], PoisonOr.value rows[3][4], PoisonOr.value rows[4][4], PoisonOr.value rows[5][4], PoisonOr.value rows[6][4], PoisonOr.value rows[7][4]]))
  liftM (store (.value (out.withOffset 416)) Row8Ty (#v[PoisonOr.value rows[0][5], PoisonOr.value rows[1][5], PoisonOr.value rows[2][5], PoisonOr.value rows[3][5], PoisonOr.value rows[4][5], PoisonOr.value rows[5][5], PoisonOr.value rows[6][5], PoisonOr.value rows[7][5]]))
  liftM (store (.value (out.withOffset 448)) Row8Ty (#v[PoisonOr.value rows[0][6], PoisonOr.value rows[1][6], PoisonOr.value rows[2][6], PoisonOr.value rows[3][6], PoisonOr.value rows[4][6], PoisonOr.value rows[5][6], PoisonOr.value rows[6][6], PoisonOr.value rows[7][6]]))
  liftM (store (.value (out.withOffset 480)) Row8Ty (#v[PoisonOr.value rows[0][7], PoisonOr.value rows[1][7], PoisonOr.value rows[2][7], PoisonOr.value rows[3][7], PoisonOr.value rows[4][7], PoisonOr.value rows[5][7], PoisonOr.value rows[6][7], PoisonOr.value rows[7][7]]))

private theorem stores8_eq (out : Pointer) (lo rows : Vector (Vector Word 8) 8) :
    stores8 out (columns8 lo rows) 16 = explicitStores8 out lo rows := by
  simp only [stores8, explicitStores8, pure_bind, bind_assoc]
  rw [col0, col1, col2, col3, col4, col5, col6, col7, col8, col9, col10, col11, col12, col13, col14, col15]
  rfl


private theorem stores8_run (out : Pointer) (cols : State (Vector Word 8))
    (count : Nat) (s : GlobalState)
    (hfit : ∀ k < count, Fits s.mem (out.withOffset (BitVec.ofNat 64 (32*k))) 256) :
    StateT.run (stores8 out cols count) s =
      .value ((), {s with mem := outputMem out cols count s.mem}) := by
  induction count with
  | zero => rfl
  | succ k ih =>
    simp only [stores8, EffectM.run_bind, ih (fun i hi => hfit i (by omega)),
      PoisonOr.value_bind]
    rw [run_liftM (s := {s with mem := outputMem out cols k s.mem})
      (run_store (flatten_packBits (cols (Fin.ofNat 16 k)))
        (fits_outputMem out cols k (hfit k (by omega))))]
    rfl

/-- Environment facts needed by bb10. No relation between input and scratch
allocations is required because both remaining reads precede all stores. -/
structure Env8 (V : InCtx8.Valuation) (out p6 p7 : Pointer)
    (lo rows : Vector (Vector Word 8) 8) (mask : BitVec 8) : Prop where
  load6 : gep (V ⟨46, rfl⟩) 4 0 (V ⟨1, rfl⟩) = .value p6
  load7 : gep (V ⟨45, rfl⟩) 4 0 (V ⟨0, rfl⟩) = .value p7
  row0 : V ⟨7, rfl⟩ = (rows[0]).map PoisonOr.value
  row1 : V ⟨6, rfl⟩ = (rows[1]).map PoisonOr.value
  row2 : V ⟨5, rfl⟩ = (rows[2]).map PoisonOr.value
  row3 : V ⟨4, rfl⟩ = (rows[3]).map PoisonOr.value
  row4 : V ⟨3, rfl⟩ = (rows[4]).map PoisonOr.value
  row5 : V ⟨2, rfl⟩ = (rows[5]).map PoisonOr.value
  low0 : V ⟨15, rfl⟩ = (lo[0]).map PoisonOr.value
  low1 : V ⟨14, rfl⟩ = (lo[1]).map PoisonOr.value
  low2 : V ⟨13, rfl⟩ = (lo[2]).map PoisonOr.value
  low3 : V ⟨12, rfl⟩ = (lo[3]).map PoisonOr.value
  low4 : V ⟨11, rfl⟩ = (lo[4]).map PoisonOr.value
  low5 : V ⟨10, rfl⟩ = (lo[5]).map PoisonOr.value
  low6 : V ⟨9, rfl⟩ = (lo[6]).map PoisonOr.value
  low7 : V ⟨8, rfl⟩ = (lo[7]).map PoisonOr.value
  ptr0 : V ⟨53, rfl⟩ = .value (out.withOffset 0)
  ptr1 : V ⟨43, rfl⟩ = .value (out.withOffset 32)
  ptr2 : V ⟨42, rfl⟩ = .value (out.withOffset 64)
  ptr3 : V ⟨41, rfl⟩ = .value (out.withOffset 96)
  ptr4 : V ⟨40, rfl⟩ = .value (out.withOffset 128)
  ptr5 : V ⟨39, rfl⟩ = .value (out.withOffset 160)
  ptr6 : V ⟨38, rfl⟩ = .value (out.withOffset 192)
  ptr7 : V ⟨37, rfl⟩ = .value (out.withOffset 224)
  ptr8 : V ⟨36, rfl⟩ = .value (out.withOffset 256)
  ptr9 : V ⟨35, rfl⟩ = .value (out.withOffset 288)
  ptr10 : V ⟨34, rfl⟩ = .value (out.withOffset 320)
  ptr11 : V ⟨33, rfl⟩ = .value (out.withOffset 352)
  ptr12 : V ⟨32, rfl⟩ = .value (out.withOffset 384)
  ptr13 : V ⟨31, rfl⟩ = .value (out.withOffset 416)
  ptr14 : V ⟨30, rfl⟩ = .value (out.withOffset 448)
  ptr15 : V ⟨29, rfl⟩ = .value (out.withOffset 480)
  active : SLLVM.bitcast (.vector 8 (.bitvec (.concrete 1)))
    (.bitvec (.concrete 8)) (V ⟨18, rfl⟩) = .value mask
  zero : V ⟨78, rfl⟩ = .value 0#8

/-- The compiler's vector-to-byte bitcast packs the eight defined active bits. -/
theorem bitcast_active8 (active : Vector (BitVec 1) 8) :
    SLLVM.bitcast (.vector 8 (.bitvec (.concrete 1))) (.bitvec (.concrete 8))
      (active.map PoisonOr.value) = .value (packBits active) := by
  rw [bitcast_of_defined]
  · rfl
  · intro i
    show LLVM.Ty.ofBitvec ((active.map PoisonOr.value)[i.val]) ≠ .poison
    rw [Vector.getElem_map]
    exact PoisonOr.value_ne_poison _

/-- A zero packed active mask is exactly the all-inactive condition. -/
theorem active8_zero_iff (active : Vector (BitVec 1) 8) :
    packBits active = 0 ↔ ∀ i : Fin 8, active[i] = 0 := by
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


set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem spec8_run (V : InCtx8.Valuation) (out p6 p7 : Pointer)
    (lo rows : Vector (Vector Word 8) 8) (mask : BitVec 8)
    (hV : Env8 V out p6 p7 lo rows mask) (s : GlobalState)
    (hf6 : Fits s.mem p6 256) (hr6 : readWord? p6 256 s.mem = some (packBits rows[6]))
    (hf7 : Fits s.mem p7 256) (hr7 : readWord? p7 256 s.mem = some (packBits rows[7]))
    (hfit : ∀ k < 16, Fits s.mem (out.withOffset (BitVec.ofNat 64 (32*k))) 256) :
    StateT.run (transpose8Spec V) s =
      .value (.inr (if mask = 0 then rootTarget8 V else nonrootTarget8 V),
        {s with mem := outputMem out (columns8 lo rows) 16 s.mem}) := by
  unfold transpose8Spec
  simp only [hV.load6, hV.load7, hV.active, hV.zero, hV.row0, hV.row1, hV.row2, hV.row3, hV.row4, hV.row5, hV.low0, hV.low1, hV.low2, hV.low3, hV.low4, hV.low5, hV.low6, hV.low7, hV.ptr0, hV.ptr1, hV.ptr2, hV.ptr3, hV.ptr4, hV.ptr5, hV.ptr6, hV.ptr7, hV.ptr8, hV.ptr9, hV.ptr10, hV.ptr11, hV.ptr12, hV.ptr13, hV.ptr14, hV.ptr15]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[6] hf6 hr6)]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[7] hf7 hr7)]
  simp only [PoisonOr.value_bind, Vector.getElem_map]
  have h := stores8_run out (columns8 lo rows) 16 s hfit
  have h' (r : HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) :
      StateT.run (stores8 out (columns8 lo rows) 16 >>= fun _ => pure r) s =
        .value (r, {s with mem := outputMem out (columns8 lo rows) 16 s.mem}) := by
    rw [EffectM.run_bind, h]
    rfl
  rw [stores8_eq] at h'
  simp only [explicitStores8, bind_assoc] at h'
  by_cases hm : mask = 0
  · have hc : LLVM.icmp .eq (.value mask) (.value 0#8) = .value 1#1 := by
      subst hm
      rfl
    rw [hc]
    simp only [hm, ↓reduceIte]
    exact h' (.inr (rootTarget8 V))
  · have hc : LLVM.icmp .eq (.value mask) (.value 0#8) = .value 0#1 := by
      simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ofBool]
      exact hm
    rw [hc]
    simp only [hm, show ¬(0#1 = 1) by decide, ↓reduceIte]
    exact h' (.inr (nonrootTarget8 V))


set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Refinement of the actual compiled bb10, including both final input loads. -/
theorem transpose8_denote (V : InCtx8.Valuation) :
    (do let (_, r) ← agave_batch_8.cfgBlock_9.denote V; pure r) = transpose8Spec V := by
  simp only [transpose8Spec, BlockCom.denote,
    Terminator.denote, targetIte, rootTarget8, nonrootTarget8,
    simp_denote, simp_sllvm, bind_map_left]
  simp only [hvConsAppend, hvNilAppend, simp_spine]
  simp only [shuffle0, shuffle1, shuffle2, shuffle3, shuffle4, shuffle5, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [bind_pure]
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

/-- Exact successful execution of the compiler's transpose/store/branch
block. The successor carries every live phi value, and the final state changes
only the sixteen specified scratch vectors. -/
theorem transpose8_run (V : InCtx8.Valuation) (out p6 p7 : Pointer)
    (lo rows : Vector (Vector Word 8) 8) (mask : BitVec 8)
    (hV : Env8 V out p6 p7 lo rows mask) (s : GlobalState)
    (hf6 : Fits s.mem p6 256) (hr6 : readWord? p6 256 s.mem = some (packBits rows[6]))
    (hf7 : Fits s.mem p7 256) (hr7 : readWord? p7 256 s.mem = some (packBits rows[7]))
    (hfit : ∀ k < 16, Fits s.mem (out.withOffset (BitVec.ofNat 64 (32*k))) 256) :
    ∃ V', StateT.run (agave_batch_8.cfgBlock_9.denote V) s =
      .value ((V', .inr (if mask = 0 then rootTarget8 V else nonrootTarget8 V)),
        {s with mem := outputMem out (columns8 lo rows) 16 s.mem}) := by
  apply run_of_project
  rw [transpose8_denote]
  exact spec8_run V out p6 p7 lo rows mask hV s hf6 hr6 hf7 hr7 hfit

/-- Scratch writes preserve all other allocations. -/
theorem transpose8_frame (out : Pointer) (lo rows : Vector (Vector Word 8) 8)
    (m : MemoryState) (q : BlockId) (hq : q ≠ out.id) :
    (outputMem out (columns8 lo rows) 16 m).live? q = m.live? q :=
  outputMem_frame out (columns8 lo rows) 16 m q hq

end AgaveLatticeHash.MLIR.BatchTranspose
