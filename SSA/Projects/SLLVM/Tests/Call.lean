/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# SLLVM `llvm.call`

`Com` has no symbol table, so a call carries its callee's body as its region
argument and denotes by applying it -- `Scf.run` generalised to any arity.

Two things here are worth more than the plumbing. **Purity**: the call declares
the callee's effect, so calling a pure function is pure and the enclosing `Com`
stays pure. Before regions carried their operation's declared effect that was
impossible; every region-carrying operation was forced impure. **Argument
order**: a call is the one place where an operand list is turned into a
`Valuation` over a fresh context, so a transposition there would silently swap
a callee's parameters.
-/

namespace LeanMLIR.SLLVM.Tests
open LeanMLIR

private def runPure (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64]) :
    PoisonOr (BitVec 64) :=
  (com.denote Ctxt.Valuation.nil).head

/-! ## A call is its callee applied to its arguments -/

def callDouble : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %c = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> (i64)
      %r = "llvm.call"(%c) ({
        ^bb0(%a: i64):
          %d = "llvm.add"(%a, %a) : (i64, i64) -> (i64)
          "llvm.return"(%d) : (i64) -> ()
      }) <{callee = @double}> : (i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure callDouble == .value 10#64

/-! ## Purity

The type ascription on `callDouble` is the test: it is `.pure`. A call to a
pure callee does not drag the caller into the effect monad. -/

example : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] := callDouble

/-! ## Argument order

`sub(7, 3)` is `4`, not `-4`. The subtraction is not commutative precisely so
that a swapped operand order fails rather than agreeing by luck. -/

def callSub : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %x = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> (i64)
      %y = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> (i64)
      %r = "llvm.call"(%x, %y) ({
        ^bb0(%a: i64, %b: i64):
          %d = "llvm.sub"(%a, %b) : (i64, i64) -> (i64)
          "llvm.return"(%d) : (i64) -> ()
      }) <{callee = @sub}> : (i64, i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure callSub == .value 4#64

/-! ## Poison propagates through a call -/

def callPoison : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %p = "llvm.mlir.poison"() : () -> (i64)
      %r = "llvm.call"(%p) ({
        ^bb0(%a: i64):
          %d = "llvm.add"(%a, %a) : (i64, i64) -> (i64)
          "llvm.return"(%d) : (i64) -> ()
      }) <{callee = @double}> : (i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure callPoison == .poison

/-! ## The callee ignoring its argument

A callee that returns a constant is not affected by what is passed, which
checks that the region really is evaluated under a valuation of its *own*
context rather than the caller's. -/

def callConst : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %c = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> (i64)
      %r = "llvm.call"(%c) ({
        ^bb0(%a: i64):
          %k = "llvm.mlir.constant"() <{value = 99 : i64}> : () -> (i64)
          "llvm.return"(%k) : (i64) -> ()
      }) <{callee = @konst}> : (i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure callConst == .value 99#64

/-! ## The callee's frame dies at its return

An impure call deallocates on return every block its region allocated. The
callee below works with its alloca freely -- store, load back, return the
value -- and the call returns `7`: internal memory use is unaffected. -/

private def runImpure (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64]) :
    Option (BitVec 64) := do
  let r ← ((com.denote Ctxt.Valuation.nil).run ⟨⟨0⟩, ⟨∅⟩⟩).toOption
  r.1.head.toOption

def callUsesOwnSlot : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %r = "llvm.call"() ({
        ^bb0():
          %s = "ptr.alloca"() <{elem_type = i64}> : () -> (!llvm.ptr)
          %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> (i64)
          "llvm.store"(%c, %s) : (i64, !llvm.ptr) -> ()
          %v = "llvm.load"(%s) : (!llvm.ptr) -> (i64)
          "llvm.return"(%v) : (i64) -> ()
      }) <{callee = @usesOwnSlot}> : () -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runImpure callUsesOwnSlot == some 7#64

/-- But a pointer into the frame that *escapes* the call is dangling: loading
through it afterwards is UB, exactly as a returned stack address is in C. -/
def callEscapesSlot : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %p = "llvm.call"() ({
        ^bb0():
          %s = "ptr.alloca"() <{elem_type = i64}> : () -> (!llvm.ptr)
          %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> (i64)
          "llvm.store"(%c, %s) : (i64, !llvm.ptr) -> ()
          "llvm.return"(%s) : (!llvm.ptr) -> ()
      }) <{callee = @escapesSlot}> : () -> (!llvm.ptr)
      %v = "llvm.load"(%p) : (!llvm.ptr) -> (i64)
      "llvm.return"(%v) : (i64) -> ()
  }]

#guard runImpure callEscapesSlot == none

/-- The other direction stays live: a caller block written through an
out-parameter, the shape `fd_r43x6_quad_mul_fast` is called with, survives
the callee's return -- it predates the call's counter snapshot. -/
def callOutParam : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %s = "ptr.alloca"() <{elem_type = i64}> : () -> (!llvm.ptr)
      "llvm.call"(%s) ({
        ^bb0(%out: !llvm.ptr):
          %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> (i64)
          "llvm.store"(%c, %out) : (i64, !llvm.ptr) -> ()
          "llvm.return"() : () -> ()
      }) <{callee = @fillsOutParam}> : (!llvm.ptr) -> ()
      %v = "llvm.load"(%s) : (!llvm.ptr) -> (i64)
      "llvm.return"(%v) : (i64) -> ()
  }]

#guard runImpure callOutParam == some 7#64

end LeanMLIR.SLLVM.Tests
