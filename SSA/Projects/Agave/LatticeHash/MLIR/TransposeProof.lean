import Mathlib.Tactic.IntervalCases
import SSA.Projects.Agave.LatticeHash.MLIR.agave_transpose_8
import SSA.Projects.Agave.LatticeHash.MLIR.agave_transpose_16
import SSA.Projects.Firedancer.MLIR.DenoteStep

/-!
# Compiler-emitted transpose refinement

The imported programs are lifted from the pinned Rust wrappers' actual MLIR.
The specifications below contain no shuffle network: output row `r` consists
of word `r` from each input row. The equalities quantify over all pointers and
retain the SLLVM load/store effects, including undefined behavior. Thus they
also cover arbitrary initial memory and per-lane poison under that model.

This proves the whole lifted straight-line program, rather than evaluating
only a provenance-label model. It does not establish the Rust compiler's
correctness, or strengthen SLLVM's memory/metadata semantics to LLVM's.
-/

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- A row has eight 32-bit words, including the SLLVM per-lane poison marker. -/
abbrev Row8 := Vector (LLVM.IntW 32) 8
abbrev Row8Ty : LLVM.Ty := .vector 8 (.bitvec (.concrete 32))

/-- The read/write specification uses the mathematical transpose directly.
All reads precede all writes, so the operation is in-place. -/
def transpose8Spec (p : SLLVM.Ptr) : EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty)) := do
  let x0 : Row8 ← liftM (SLLVM.load p Row8Ty)
  let x1 : Row8 ← liftM (SLLVM.load (gep p 1 0 (.value 32#64)) Row8Ty)
  let x2 : Row8 ← liftM (SLLVM.load (gep p 1 0 (.value 64#64)) Row8Ty)
  let x3 : Row8 ← liftM (SLLVM.load (gep p 1 0 (.value 96#64)) Row8Ty)
  let x4 : Row8 ← liftM (SLLVM.load (gep p 1 0 (.value 128#64)) Row8Ty)
  let x5 : Row8 ← liftM (SLLVM.load (gep p 1 0 (.value 160#64)) Row8Ty)
  let x6 : Row8 ← liftM (SLLVM.load (gep p 1 0 (.value 192#64)) Row8Ty)
  let x7 : Row8 ← liftM (SLLVM.load (gep p 1 0 (.value 224#64)) Row8Ty)
  let y0 : Row8 := #v[x0[0], x1[0], x2[0], x3[0], x4[0], x5[0], x6[0], x7[0]]
  liftM (SLLVM.store p Row8Ty y0)
  let y1 : Row8 := #v[x0[1], x1[1], x2[1], x3[1], x4[1], x5[1], x6[1], x7[1]]
  liftM (SLLVM.store (gep p 1 0 (.value 32#64)) Row8Ty y1)
  let y2 : Row8 := #v[x0[2], x1[2], x2[2], x3[2], x4[2], x5[2], x6[2], x7[2]]
  liftM (SLLVM.store (gep p 1 0 (.value 64#64)) Row8Ty y2)
  let y3 : Row8 := #v[x0[3], x1[3], x2[3], x3[3], x4[3], x5[3], x6[3], x7[3]]
  liftM (SLLVM.store (gep p 1 0 (.value 96#64)) Row8Ty y3)
  let y4 : Row8 := #v[x0[4], x1[4], x2[4], x3[4], x4[4], x5[4], x6[4], x7[4]]
  liftM (SLLVM.store (gep p 1 0 (.value 128#64)) Row8Ty y4)
  let y5 : Row8 := #v[x0[5], x1[5], x2[5], x3[5], x4[5], x5[5], x6[5], x7[5]]
  liftM (SLLVM.store (gep p 1 0 (.value 160#64)) Row8Ty y5)
  let y6 : Row8 := #v[x0[6], x1[6], x2[6], x3[6], x4[6], x5[6], x6[6], x7[6]]
  liftM (SLLVM.store (gep p 1 0 (.value 192#64)) Row8Ty y6)
  let y7 : Row8 := #v[x0[7], x1[7], x2[7], x3[7], x4[7], x5[7], x6[7], x7[7]]
  liftM (SLLVM.store (gep p 1 0 (.value 224#64)) Row8Ty y7)
  pure .nil

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The actual lifted AVX2 program denotes the mathematical in-place transpose. -/
theorem transpose8_denote (p : SLLVM.Ptr) :
    agave_transpose_8_com.denote (Ctxt.Valuation.singleton p) = transpose8Spec p := by
  simp only [agave_transpose_8_com, transpose8Spec, simp_denote, bind_map_left,
    Ctxt.Valuation.singleton, LLVM.const?]

  congr 1

/-- Sixteen-word counterpart of `transpose8Spec`. Loads follow the compiler's
order; each stored row is explicitly one column of the input. -/
abbrev Row16 := Vector (LLVM.IntW 32) 16
abbrev Row16Ty : LLVM.Ty := .vector 16 (.bitvec (.concrete 32))

def transpose16Spec (p : SLLVM.Ptr) : EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty)) := do
  let x0 : Row16 ← liftM (SLLVM.load p Row16Ty)
  let x4 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 256#64)) Row16Ty)
  let x1 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 64#64)) Row16Ty)
  let x5 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 320#64)) Row16Ty)
  let x2 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 128#64)) Row16Ty)
  let x6 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 384#64)) Row16Ty)
  let x3 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 192#64)) Row16Ty)
  let x7 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 448#64)) Row16Ty)
  let x8 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 512#64)) Row16Ty)
  let x12 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 768#64)) Row16Ty)
  let x9 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 576#64)) Row16Ty)
  let x13 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 832#64)) Row16Ty)
  let x10 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 640#64)) Row16Ty)
  let x14 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 896#64)) Row16Ty)
  let x11 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 704#64)) Row16Ty)
  let x15 : Row16 ← liftM (SLLVM.load (gep p 1 0 (.value 960#64)) Row16Ty)
  let y0 : Row16 := #v[x0[0], x1[0], x2[0], x3[0], x4[0], x5[0], x6[0], x7[0], x8[0], x9[0], x10[0], x11[0], x12[0], x13[0], x14[0], x15[0]]
  liftM (SLLVM.store p Row16Ty y0)
  let y1 : Row16 := #v[x0[1], x1[1], x2[1], x3[1], x4[1], x5[1], x6[1], x7[1], x8[1], x9[1], x10[1], x11[1], x12[1], x13[1], x14[1], x15[1]]
  liftM (SLLVM.store (gep p 1 0 (.value 64#64)) Row16Ty y1)
  let y2 : Row16 := #v[x0[2], x1[2], x2[2], x3[2], x4[2], x5[2], x6[2], x7[2], x8[2], x9[2], x10[2], x11[2], x12[2], x13[2], x14[2], x15[2]]
  liftM (SLLVM.store (gep p 1 0 (.value 128#64)) Row16Ty y2)
  let y3 : Row16 := #v[x0[3], x1[3], x2[3], x3[3], x4[3], x5[3], x6[3], x7[3], x8[3], x9[3], x10[3], x11[3], x12[3], x13[3], x14[3], x15[3]]
  liftM (SLLVM.store (gep p 1 0 (.value 192#64)) Row16Ty y3)
  let y4 : Row16 := #v[x0[4], x1[4], x2[4], x3[4], x4[4], x5[4], x6[4], x7[4], x8[4], x9[4], x10[4], x11[4], x12[4], x13[4], x14[4], x15[4]]
  liftM (SLLVM.store (gep p 1 0 (.value 256#64)) Row16Ty y4)
  let y5 : Row16 := #v[x0[5], x1[5], x2[5], x3[5], x4[5], x5[5], x6[5], x7[5], x8[5], x9[5], x10[5], x11[5], x12[5], x13[5], x14[5], x15[5]]
  liftM (SLLVM.store (gep p 1 0 (.value 320#64)) Row16Ty y5)
  let y6 : Row16 := #v[x0[6], x1[6], x2[6], x3[6], x4[6], x5[6], x6[6], x7[6], x8[6], x9[6], x10[6], x11[6], x12[6], x13[6], x14[6], x15[6]]
  liftM (SLLVM.store (gep p 1 0 (.value 384#64)) Row16Ty y6)
  let y7 : Row16 := #v[x0[7], x1[7], x2[7], x3[7], x4[7], x5[7], x6[7], x7[7], x8[7], x9[7], x10[7], x11[7], x12[7], x13[7], x14[7], x15[7]]
  liftM (SLLVM.store (gep p 1 0 (.value 448#64)) Row16Ty y7)
  let y8 : Row16 := #v[x0[8], x1[8], x2[8], x3[8], x4[8], x5[8], x6[8], x7[8], x8[8], x9[8], x10[8], x11[8], x12[8], x13[8], x14[8], x15[8]]
  liftM (SLLVM.store (gep p 1 0 (.value 512#64)) Row16Ty y8)
  let y9 : Row16 := #v[x0[9], x1[9], x2[9], x3[9], x4[9], x5[9], x6[9], x7[9], x8[9], x9[9], x10[9], x11[9], x12[9], x13[9], x14[9], x15[9]]
  liftM (SLLVM.store (gep p 1 0 (.value 576#64)) Row16Ty y9)
  let y10 : Row16 := #v[x0[10], x1[10], x2[10], x3[10], x4[10], x5[10], x6[10], x7[10], x8[10], x9[10], x10[10], x11[10], x12[10], x13[10], x14[10], x15[10]]
  liftM (SLLVM.store (gep p 1 0 (.value 640#64)) Row16Ty y10)
  let y11 : Row16 := #v[x0[11], x1[11], x2[11], x3[11], x4[11], x5[11], x6[11], x7[11], x8[11], x9[11], x10[11], x11[11], x12[11], x13[11], x14[11], x15[11]]
  liftM (SLLVM.store (gep p 1 0 (.value 704#64)) Row16Ty y11)
  let y12 : Row16 := #v[x0[12], x1[12], x2[12], x3[12], x4[12], x5[12], x6[12], x7[12], x8[12], x9[12], x10[12], x11[12], x12[12], x13[12], x14[12], x15[12]]
  liftM (SLLVM.store (gep p 1 0 (.value 768#64)) Row16Ty y12)
  let y13 : Row16 := #v[x0[13], x1[13], x2[13], x3[13], x4[13], x5[13], x6[13], x7[13], x8[13], x9[13], x10[13], x11[13], x12[13], x13[13], x14[13], x15[13]]
  liftM (SLLVM.store (gep p 1 0 (.value 832#64)) Row16Ty y13)
  let y14 : Row16 := #v[x0[14], x1[14], x2[14], x3[14], x4[14], x5[14], x6[14], x7[14], x8[14], x9[14], x10[14], x11[14], x12[14], x13[14], x14[14], x15[14]]
  liftM (SLLVM.store (gep p 1 0 (.value 896#64)) Row16Ty y14)
  let y15 : Row16 := #v[x0[15], x1[15], x2[15], x3[15], x4[15], x5[15], x6[15], x7[15], x8[15], x9[15], x10[15], x11[15], x12[15], x13[15], x14[15], x15[15]]
  liftM (SLLVM.store (gep p 1 0 (.value 960#64)) Row16Ty y15)
  pure .nil

/-- Expose just the selected lane. Explicit `rw` is intentional: the inner
shuffle's dependent length is definitionally, but not syntactically, the
outer input length, so recursive simplifier lookup alone misses it. -/
private theorem shuffleLane {l : Nat} (mask : List Int)
    (a b : Vector (LLVM.IntW 32) l) (i : Nat) (hi : i < mask.length) :
    (LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) mask a b)[i] =
      (let m := mask.getD i (-1)
       if m < 0 then .poison
       else if h : m.toNat < l then a[m.toNat]
       else if h : m.toNat - l < l then b[m.toNat - l] else .poison) := by
  simp only [LLVM.Ty.shufflevector, Vector.getElem_ofFn]
  rfl

private theorem storeSeqCongr {n : Nat} {p : SLLVM.Ptr}
    {v w : Vector (LLVM.IntW 32) n}
    {a b : EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty))}
    (hv : v = w) (hab : a = b) :
    (do liftM (SLLVM.store p (.vector n (.bitvec (.concrete 32))) v); a) =
      (do liftM (SLLVM.store p (.vector n (.bitvec (.concrete 32))) w); b) := by
  rw [hv, hab]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The actual lifted AVX-512 program denotes the mathematical in-place transpose. -/
theorem transpose16_denote (p : SLLVM.Ptr) :
    agave_transpose_16_com.denote (Ctxt.Valuation.singleton p) = transpose16Spec p := by
  simp (config := { maxSteps := 2000000 }) only [agave_transpose_16_com, transpose16Spec, simp_denote, bind_map_left,
    Ctxt.Valuation.singleton, LLVM.const?]
  apply bind_congr
  intro x0
  apply bind_congr
  intro x1
  apply bind_congr
  intro x2
  apply bind_congr
  intro x3
  apply bind_congr
  intro x4
  apply bind_congr
  intro x5
  apply bind_congr
  intro x6
  apply bind_congr
  intro x7
  apply bind_congr
  intro x8
  apply bind_congr
  intro x9
  apply bind_congr
  intro x10
  apply bind_congr
  intro x11
  apply bind_congr
  intro x12
  apply bind_congr
  intro x13
  apply bind_congr
  intro x14
  apply bind_congr
  intro x15
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  apply storeSeqCongr
  · apply Vector.ext
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      (repeat'
        (rw [shuffleLane]
         simp only [↓reduceIte, ↓reduceDIte, Vector.getElem_mk,
           List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
           List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT,
           Int.reduceToNat, Nat.reduceLT, Nat.reduceSub]))
  rfl

end AgaveLatticeHash.MLIR
