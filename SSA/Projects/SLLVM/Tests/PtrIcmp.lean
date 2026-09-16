/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `llvm.icmp` at `!llvm.ptr`

The null check a caller does on a returned sentinel. The predicate is an
attribute, as it is for the integer form; the *operand* type is what selects
`ptricmp`.
-/

namespace LeanMLIR.SLLVM.Tests.PtrIcmp

open LeanMLIR

def isNull : Com SLLVM (Ctxt.ofList [SLLVM.Ty.ptr]) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm|
    {^entry(%p:!llvm.ptr):%z="llvm.mlir.zero"():()->!llvm.ptr%c="llvm.icmp"(%p,
            %z)<{predicate = 0:i64}>:(!llvm.ptr, !llvm.ptr)->i1"llvm.return"(%c):(i1)->()}]

example : (isNull.denote (Ctxt.Valuation.singleton SLLVM.Ptr.null)).head = .value 1#1 :=
  rfl

example :
    (isNull.denote (Ctxt.Valuation.singleton (PoisonOr.value ⟨⟨7⟩, 0#64⟩ : SLLVM.Ptr))).head =
      .value 0#1 :=
  rfl

-- A different offset into the null block is not null either.
example :
    (isNull.denote
          (Ctxt.Valuation.singleton (PoisonOr.value ⟨SLLVM.nullBlock, 8#64⟩ : SLLVM.Ptr))).head =
      .value 0#1 :=
  rfl

example : (isNull.denote (Ctxt.Valuation.singleton (PoisonOr.poison : SLLVM.Ptr))).head = .poison :=
  rfl

def isNotNull : Com SLLVM (Ctxt.ofList [SLLVM.Ty.ptr]) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm|
    {^entry(%p:!llvm.ptr):%z="llvm.mlir.zero"():()->!llvm.ptr%c="llvm.icmp"(%p,
            %z)<{predicate = 1:i64}>:(!llvm.ptr, !llvm.ptr)->i1"llvm.return"(%c):(i1)->()}]

example : (isNotNull.denote (Ctxt.Valuation.singleton SLLVM.Ptr.null)).head = .value 0#1 :=
  rfl

end LeanMLIR.SLLVM.Tests.PtrIcmp
