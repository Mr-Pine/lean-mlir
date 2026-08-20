/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `vpermi2var`

Coverage for `x86vector.avx512.intr.vpermi2var.q.512`: the two-table lane
selection, the high index bits being ignored, and the two poison behaviours.

The two-table test uses the exact index vector `fd_r43x6_ge_is_eq` uses for
its `FD_R43X6_QUAD_UNPACK` (`dense<[0, 1, 8, 4, 5, 12, 9, 9]>`), so a mistake
in the table-select bit would misassemble a field element's limbs here before
it could misassemble them there.
-/

namespace LeanMLIR.SLLVM.Tests
open LeanMLIR
open InstCombine (LLVM)

/-- Run a closed pure program returning a whole `<8 x i64>`. -/
private def runVec
    (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.arith (.vector 8 (.bitvec 64))]) :
    Vector (LLVM.IntW 64) 8 :=
  (com.denote Ctxt.Valuation.nil).head

/-- An `<8 x i64>` of values, in lane order. -/
private def vec8 (vals : List Int) : Vector (LLVM.IntW 64) 8 :=
  LLVM.Ty.dense (LLVM.Ty.vector 8 (.bitvec 64)) vals

/-! ## Two-table selection

Index `k < 8` reads lane `k` of the first table, `8 ≤ k < 16` lane `k - 8` of
the second. The tables' values are disjoint (`100 + i` vs `200 + i`), so a
wrong table-select bit changes the answer, not just its provenance. -/

def twoTables : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure
    [SLLVM.Ty.arith (.vector 8 (.bitvec 64))] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = dense<[100, 101, 102, 103, 104, 105, 106, 107]> : vector<8xi64>}> : () -> (vector<8xi64>)
      %idx = "llvm.mlir.constant"() <{value = dense<[0, 1, 8, 4, 5, 12, 9, 9]> : vector<8xi64>}> : () -> (vector<8xi64>)
      %b = "llvm.mlir.constant"() <{value = dense<[200, 201, 202, 203, 204, 205, 206, 207]> : vector<8xi64>}> : () -> (vector<8xi64>)
      %r = "x86vector.avx512.intr.vpermi2var.q.512"(%a, %idx, %b) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> (vector<8xi64>)
      "llvm.return"(%r) : (vector<8xi64>) -> ()
  }]

#guard runVec twoTables == vec8 [100, 101, 200, 104, 105, 204, 201, 201]

/-! ## Only the low `log2 16` index bits are read

Per Intel, higher bits are ignored: index `k` selects like `k % 16` does. -/

#guard
    LLVM.Ty.vpermi2var
      (vec8 [100, 101, 102, 103, 104, 105, 106, 107])
      (vec8 [16, 25, 35, 44, -1, 17, 62, 15])
      (vec8 [200, 201, 202, 203, 204, 205, 206, 207])
  == vec8 [100, 201, 103, 204, 207, 101, 206, 207]

/-! ## Poison

A poison *index* poisons its lane -- and only its lane. A poison element in
the *unselected* table does not: only the selected lane is read. Selecting the
poison element itself of course propagates it. -/

private def aWithPoison5 : Vector (LLVM.IntW 64) 8 :=
  (vec8 [100, 101, 102, 103, 104, 105, 106, 107]).set 5 .poison

#guard
    LLVM.Ty.vpermi2var aWithPoison5 (vec8 [5, 13, 0, 0, 0, 0, 0, 0])
      (vec8 [200, 201, 202, 203, 204, 205, 206, 207])
  == ((vec8 [0, 205, 100, 100, 100, 100, 100, 100]).set 0 .poison)

#guard
    LLVM.Ty.vpermi2var (vec8 [100, 101, 102, 103, 104, 105, 106, 107])
      ((vec8 [0, 9, 0, 0, 0, 0, 0, 0]).set 0 .poison)
      (vec8 [200, 201, 202, 203, 204, 205, 206, 207])
  == ((vec8 [0, 201, 100, 100, 100, 100, 100, 100]).set 0 .poison)

end LeanMLIR.SLLVM.Tests
