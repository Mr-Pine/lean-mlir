/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `llvm.mlir.zero`

The zero value of the result type. At `!llvm.ptr` that is the null pointer --
its own operation, since `SLLVM.Ptr` is `PoisonOr Pointer` and null is a
*value*, not poison; at an integer type it is the constant `0`, which
`llvm.mlir.constant` already covers.
-/

namespace LeanMLIR.SLLVM.Tests.Null

open LeanMLIR

def nullPtr : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.ptr] :=
  [sllvm| {^entry():%p="llvm.mlir.zero"():()->!llvm.ptr"llvm.return"(%p):(!llvm.ptr)->()}]

example : (nullPtr.denote Ctxt.Valuation.nil).head = SLLVM.Ptr.null :=
  rfl

-- ... which is a `PoisonOr.value`, not poison: a spec may state it as *the*
-- returned value, and a caller may branch on it.
example : (nullPtr.denote Ctxt.Valuation.nil).head = PoisonOr.value ⟨SLLVM.nullBlock, 0#64⟩ :=
  rfl

def zeroI64 : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {^entry():%z="llvm.mlir.zero"():()->i64"llvm.return"(%z):(i64)->()}]

example : (zeroI64.denote Ctxt.Valuation.nil).head = .value 0#64 :=
  rfl

end LeanMLIR.SLLVM.Tests.Null
