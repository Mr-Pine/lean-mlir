/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# SLLVM `llvm.icmp` in generic form

`mlir-opt --mlir-print-op-generic` -- and MLIR itself -- always names the
operation `llvm.icmp` and carries the condition code in an attribute. The
hand-spelled `llvm.icmp.<pred>` names the parser also accepts are not syntax
MLIR ever emits.

What is worth testing is the *numbering*, not the plumbing.
`LLVM.IntPred.ofMLIRPredicate?` maps MLIR's `ICmpPredicate` (0-based, signed
comparisons before unsigned) onto `LLVM.IntPred`, which follows LLVM IR's
`CmpInst::Predicate` (32-based, unsigned first). Get that mapping wrong by a
pair and `sgt` silently becomes `ugt`: still a comparison, still well typed,
wrong answer only on operands that straddle the sign boundary.

So every case below compares `-1` against `1`, which is the pair that
separates the two readings -- signed `-1 < 1`, unsigned `2^64 - 1 > 1` -- and
each generic form is also checked against the hand-spelled name for the same
predicate.

The ten numbers themselves were read off
`clang | mlir-translate --import-llvm | mlir-opt --mlir-print-op-generic` on a
C file with all ten comparisons in it.
-/

namespace LeanMLIR.SLLVM.Tests
open LeanMLIR

/-- Run a closed pure program and read its single `i1` result. -/
private def runBool (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1]) :
    PoisonOr (BitVec 1) :=
  (com.denote Ctxt.Valuation.nil).head

/-- `predicate = 0` is `eq`. -/
def generic_eq : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 0 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_eq : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.eq"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_eq == .value 0#1
#guard runBool generic_eq == runBool named_eq

/-- `predicate = 1` is `ne`. -/
def generic_ne : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 1 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_ne : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.ne"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_ne == .value 1#1
#guard runBool generic_ne == runBool named_ne

/-- `predicate = 2` is `slt`. -/
def generic_slt : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 2 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_slt : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.slt"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_slt == .value 1#1
#guard runBool generic_slt == runBool named_slt

/-- `predicate = 3` is `sle`. -/
def generic_sle : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 3 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_sle : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.sle"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_sle == .value 1#1
#guard runBool generic_sle == runBool named_sle

/-- `predicate = 4` is `sgt`. -/
def generic_sgt : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 4 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_sgt : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.sgt"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_sgt == .value 0#1
#guard runBool generic_sgt == runBool named_sgt

/-- `predicate = 5` is `sge`. -/
def generic_sge : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 5 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_sge : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.sge"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_sge == .value 0#1
#guard runBool generic_sge == runBool named_sge

/-- `predicate = 6` is `ult`. -/
def generic_ult : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 6 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_ult : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.ult"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_ult == .value 0#1
#guard runBool generic_ult == runBool named_ult

/-- `predicate = 7` is `ule`. -/
def generic_ule : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 7 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_ule : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.ule"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_ule == .value 0#1
#guard runBool generic_ule == runBool named_ule

/-- `predicate = 8` is `ugt`. -/
def generic_ugt : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 8 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_ugt : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.ugt"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_ugt == .value 1#1
#guard runBool generic_ugt == runBool named_ugt

/-- `predicate = 9` is `uge`. -/
def generic_uge : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 9 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

/-- The same comparison written the hand-spelled way must agree. -/
def named_uge : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp.uge"(%a, %b) : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

#guard runBool generic_uge == .value 1#1
#guard runBool generic_uge == runBool named_uge

/-! An unknown predicate is rejected rather than silently mapped. `10` is one
past `uge`, the last code MLIR defines. -/

/--
error: llvm.icmp: unsupported predicate 10
-/
#guard_msgs in
def unknownPredicate : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 1] :=
  [sllvm| {
    ^entry():
      %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %r = "llvm.icmp"(%a, %b) <{predicate = 10 : i64}> : (i64, i64) -> (i1)
      "llvm.return"(%r) : (i1) -> ()
  }]

end LeanMLIR.SLLVM.Tests
