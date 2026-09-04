/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `llvm.mlir.addressof`

A global's address lives in `GlobalState.globals`, keyed by its symbol, and
`addressof` reads it out. An unknown symbol is UB, so what a global *holds* is
a hypothesis at the spec level -- the operation itself reads nothing and checks
nothing.

That is what these tests are for. The address is a property of the state, not
of the operation, so every `addressof` of a symbol names the same block no
matter where it appears -- including inside a callee, which is the case a
per-region parameter could not get right. And because nothing is checked
against an initialiser, a *mutable* global works: a store through one
`addressof` is seen by the next.
-/

namespace LeanMLIR.SLLVM.Tests.Globals
open LeanMLIR

/-- A state with one 128-bit block per named global, blocks `0, 1, …` in list
order, each zeroed. The Firedancer layer's `GlobalState.ofGlobals` is this with
the initialisers spliced in; here zeroes are enough. -/
private def stateWith (names : List String) : GlobalState :=
  names.foldl (init := (⟨⟨0⟩, ⟨∅⟩, ∅⟩ : GlobalState)) fun s name =>
    { s.afterAlloca 128 with
      globals := s.globals.insert name ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ }

private def run (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64])
    (s : GlobalState) : Option (PoisonOr (BitVec 64)) :=
  ((com.denote Ctxt.Valuation.nil).run s).toOption.map (fun r => r.1.head)

/-! ## One address per symbol -/

/-- Two `addressof`s of the same symbol give the same pointer: store through
the first, read through the second. -/
def sameSymbol : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %q = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    "llvm.store"(%v, %p) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %r = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
}]

#guard run sameSymbol (stateWith ["g"]) == some (.value 42#64)

-- ... and that is what makes a *mutable* global work: the write above is
-- visible, rather than being overwritten by an initialiser or lost to a second
-- copy of the global.
#guard run sameSymbol (stateWith ["g"]) != some (.value 0#64)

/-- Two different symbols are two different blocks: a store through `@g` does
not disturb `@h`. -/
def twoSymbols : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %q = "llvm.mlir.addressof"() <{global_name = @h}> : () -> !llvm.ptr
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    "llvm.store"(%v, %p) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %r = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
}]

#guard run twoSymbols (stateWith ["g", "h"]) == some (.value 0#64)

/-! ## Across a call

The case a per-region pointer parameter could not get right without threading
the pointer through every call site: the caller and the callee reach the same
block because both read the same table. -/

def acrossCall : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %v = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "llvm.store"(%v, %p) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %r = "llvm.call"() ({
      ^bb0():
        %q = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
        %x = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
        "llvm.return"(%x) : (i64) -> ()
    }) <{callee = @readGlobal}> : () -> (i64)
    "llvm.return"(%r) : (i64) -> ()
}]

#guard run acrossCall (stateWith ["g"]) == some (.value 7#64)

/-! ## An absent symbol is UB -/

def missingSymbol : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p = "llvm.mlir.addressof"() <{global_name = @nowhere}> : () -> !llvm.ptr
    %r = "llvm.load"(%p) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
}]

#guard (run missingSymbol (stateWith ["g"])).isNone

/-! ## The table is write-once

Nothing an operation can do reaches it -- including a call, whose frame pop
restores it along with the counter. -/

private def globalsAfter (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64])
    (s : GlobalState) : Option (List String) :=
  ((com.denote Ctxt.Valuation.nil).run s).toOption.map fun r => r.2.globals.keys

#guard globalsAfter acrossCall (stateWith ["g"]) == some ["g"]

end LeanMLIR.SLLVM.Tests.Globals
