/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `llvm.select` at `!llvm.ptr`

`c ? p : NULL`, the way C hands back a validated argument or the failure
sentinel. The *operand* type selects `ptrselect`, as it does `ptricmp`.
-/

namespace LeanMLIR.SLLVM.Tests.PtrSelect

open LeanMLIR
open InstCombine (LLVM)

def pick : Com SLLVM (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.bitvec 1]) .pure [SLLVM.Ty.ptr] :=
  [sllvm|
    {^entry(%c:i1,%p:!llvm.ptr):%z="llvm.mlir.zero"():()->!llvm.ptr%r="llvm.select"(%c, %p, %z):(i1,
            !llvm.ptr, !llvm.ptr)->!llvm.ptr"llvm.return"(%r):(!llvm.ptr)->()}]

def p7 : SLLVM.Ptr :=
  PoisonOr.value ⟨⟨7⟩, 0#64⟩

example : (pick.denote (Ctxt.Valuation.ofHVector [p7, (.value 1#1 : LLVM.IntW 1)]ₕ)).head = p7 :=
  rfl

example :
    (pick.denote (Ctxt.Valuation.ofHVector [p7, (.value 0#1 : LLVM.IntW 1)]ₕ)).head =
      SLLVM.Ptr.null :=
  rfl

example : (pick.denote (Ctxt.Valuation.ofHVector [p7, (.poison : LLVM.IntW 1)]ₕ)).head = .poison :=
  rfl

end LeanMLIR.SLLVM.Tests.PtrSelect
