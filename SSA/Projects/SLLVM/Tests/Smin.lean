/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `llvm.intr.smin`

The signed minimum. `fd_int_min` is this at `i32`.
-/

namespace LeanMLIR.SLLVM.Tests.Smin

open LeanMLIR
open InstCombine (LLVM)

def min :
    Com SLLVM (Ctxt.ofList [SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 8]) .pure [SLLVM.Ty.bitvec 8] :=
  [sllvm| {^entry(%a:i8,%b:i8):%r="llvm.intr.smin"(%a, %b):(i8, i8)->i8"llvm.return"(%r):(i8)->()}]

example :
    (min.denote (Ctxt.Valuation.ofHVector [(.value 14#8 : LLVM.IntW 8), .value 3#8]ₕ)).head =
      .value 3#8 :=
  rfl

/-- Signed: `0xff` is `-1`, below `3`. -/
example :
    (min.denote (Ctxt.Valuation.ofHVector [(.value 3#8 : LLVM.IntW 8), .value 0xff#8]ₕ)).head =
      .value 0xff#8 :=
  rfl

example :
    (min.denote (Ctxt.Valuation.ofHVector [(.value 3#8 : LLVM.IntW 8), .poison]ₕ)).head = .poison :=
  rfl

end LeanMLIR.SLLVM.Tests.Smin
