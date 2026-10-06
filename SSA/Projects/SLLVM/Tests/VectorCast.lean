import SSA.Projects.SLLVM.Dialect

/-! Parsed vector casts preserve lane order, poison, and scalar flag checks. -/
namespace LeanMLIR.SLLVM.Tests.VectorCast
open LeanMLIR
open InstCombine (LLVM)

private abbrev V (w : Nat) := SLLVM.Ty.arith (.vector 4 (.bitvec w))
private abbrev Vec (w : Nat) := Vector (LLVM.IntW w) 4

private def run {w w' : Nat} (p : Com SLLVM (Ctxt.ofList [V w]) .pure [V w'])
    (a : Vec w) : Vec w' := (p.denote (Ctxt.Valuation.singleton a)).head

def zeroExtend : Com SLLVM (Ctxt.ofList [V 1]) .pure [V 32] := [sllvm| {
  ^entry(%a: vector<4xi1>):
    %r = "llvm.zext"(%a) : (vector<4xi1>) -> vector<4xi32>
    "llvm.return"(%r) : (vector<4xi32>) -> ()
}]

def signExtend : Com SLLVM (Ctxt.ofList [V 1]) .pure [V 32] := [sllvm| {
  ^entry(%a: vector<4xi1>):
    %r = "llvm.sext"(%a) : (vector<4xi1>) -> vector<4xi32>
    "llvm.return"(%r) : (vector<4xi32>) -> ()
}]

def nonnegativeExtend : Com SLLVM (Ctxt.ofList [V 8]) .pure [V 32] := [sllvm| {
  ^entry(%a: vector<4xi8>):
    %r = "llvm.zext"(%a) <{nonNeg}> : (vector<4xi8>) -> vector<4xi32>
    "llvm.return"(%r) : (vector<4xi32>) -> ()
}]

def truncateBoth : Com SLLVM (Ctxt.ofList [V 64]) .pure [V 32] := [sllvm| {
  ^entry(%a: vector<4xi64>):
    %r = "llvm.trunc"(%a) <{overflowFlags = 3 : i32}> : (vector<4xi64>) -> vector<4xi32>
    "llvm.return"(%r) : (vector<4xi32>) -> ()
}]

def truncateMask : Com SLLVM (Ctxt.ofList [V 8]) .pure [V 1] := [sllvm| {
  ^entry(%a: vector<4xi8>):
    %r = "llvm.trunc"(%a) <{overflowFlags = 0 : i32}> : (vector<4xi8>) -> vector<4xi1>
    "llvm.return"(%r) : (vector<4xi1>) -> ()
}]

theorem zeroExtend_lane (a : Vec 1) (i : Fin 4) :
    (run zeroExtend a)[i.val] = LLVM.zext 32 a[i.val] := by
  change (SLLVM.vzext 32 a {})[i.val] = _
  exact SLLVM.vzext_lane 32 a {} i

theorem signExtend_lane (a : Vec 1) (i : Fin 4) :
    (run signExtend a)[i.val] = LLVM.sext 32 a[i.val] := by
  change (SLLVM.vsext 32 a)[i.val] = _
  exact SLLVM.vsext_lane 32 a i

theorem truncateBoth_lane (a : Vec 64) (i : Fin 4) :
    (run truncateBoth a)[i.val] = LLVM.trunc 32 a[i.val] ⟨true, true⟩ := by
  change (SLLVM.vtrunc 32 a ⟨true, true⟩)[i.val] = _
  exact SLLVM.vtrunc_lane 32 a ⟨true, true⟩ i

example : run zeroExtend #v[.value 1#1, .value 0#1, .poison, .value 1#1] =
    #v[.value 1#32, .value 0#32, .poison, .value 1#32] := by decide +kernel
example : run signExtend #v[.value 1#1, .value 0#1, .poison, .value 1#1] =
    #v[.value 4294967295#32, .value 0#32, .poison, .value 4294967295#32] := by decide +kernel
example : run nonnegativeExtend #v[.value 127#8, .value 128#8, .poison, .value 0#8] =
    #v[.value 127#32, .poison, .poison, .value 0#32] := by decide +kernel
-- 2^31 violates nsw only; -1 violates nuw only. Both must poison their own lane.
example : run truncateBoth #v[.value 2147483647#64, .value 2147483648#64,
    .value 18446744073709551615#64, .poison] =
    #v[.value 2147483647#32, .poison, .poison, .poison] := by decide +kernel
example : run truncateMask #v[.value 255#8, .value 2#8, .poison, .value 0#8] =
    #v[.value 1#1, .value 0#1, .poison, .value 0#1] := by decide +kernel

-- Printed flags use the same MLIR attributes as the parsed cases above.
private def attrs (op : SLLVM.Op) := DialectPrint.printAttributes (d := SLLVM) op

example : attrs (.vzext 4 8 32 ⟨true⟩) = "<{nonNeg}>" := rfl
example : attrs (.vzext 4 8 32 ⟨false⟩) = "" := rfl
example : attrs (.vtrunc 4 64 32 ⟨false, false⟩) = "<{overflowFlags = 0 : i32}>" := rfl
example : attrs (.vtrunc 4 64 32 ⟨true, false⟩) = "<{overflowFlags = 1 : i32}>" := rfl
example : attrs (.vtrunc 4 64 32 ⟨false, true⟩) = "<{overflowFlags = 2 : i32}>" := rfl
example : attrs (.vtrunc 4 64 32 ⟨true, true⟩) = "<{overflowFlags = 3 : i32}>" := rfl

example (flag : LLVM.NonNegFlag) :
    attrs (SLLVM.Op.zext 8 32 flag) = attrs (.vzext 4 8 32 flag) := rfl
example (flags : LLVM.NoWrapFlags) :
    attrs (SLLVM.Op.trunc 64 32 flags) = attrs (.vtrunc 4 64 32 flags) := rfl

-- LLVM casts require a strict change in element width in the correct direction.
/-- error: llvm.zext: result element width must be larger than input element width -/
#guard_msgs in
def equalZext : Com SLLVM (Ctxt.ofList [V 8]) .pure [V 8] := [sllvm| {
  ^entry(%a: vector<4xi8>):
    %r = "llvm.zext"(%a) : (vector<4xi8>) -> vector<4xi8>
    "llvm.return"(%r) : (vector<4xi8>) -> ()
}]

/-- error: llvm.zext: result element width must be larger than input element width -/
#guard_msgs in
def narrowZext : Com SLLVM (Ctxt.ofList [V 32]) .pure [V 8] := [sllvm| {
  ^entry(%a: vector<4xi32>):
    %r = "llvm.zext"(%a) : (vector<4xi32>) -> vector<4xi8>
    "llvm.return"(%r) : (vector<4xi8>) -> ()
}]

/-- error: llvm.sext: result element width must be larger than input element width -/
#guard_msgs in
def equalSext : Com SLLVM (Ctxt.ofList [V 8]) .pure [V 8] := [sllvm| {
  ^entry(%a: vector<4xi8>):
    %r = "llvm.sext"(%a) : (vector<4xi8>) -> vector<4xi8>
    "llvm.return"(%r) : (vector<4xi8>) -> ()
}]

/-- error: llvm.sext: result element width must be larger than input element width -/
#guard_msgs in
def narrowSext : Com SLLVM (Ctxt.ofList [V 32]) .pure [V 8] := [sllvm| {
  ^entry(%a: vector<4xi32>):
    %r = "llvm.sext"(%a) : (vector<4xi32>) -> vector<4xi8>
    "llvm.return"(%r) : (vector<4xi8>) -> ()
}]

/-- error: llvm.trunc: result element width must be smaller than input element width -/
#guard_msgs in
def equalTrunc : Com SLLVM (Ctxt.ofList [V 8]) .pure [V 8] := [sllvm| {
  ^entry(%a: vector<4xi8>):
    %r = "llvm.trunc"(%a) : (vector<4xi8>) -> vector<4xi8>
    "llvm.return"(%r) : (vector<4xi8>) -> ()
}]

/-- error: llvm.trunc: result element width must be smaller than input element width -/
#guard_msgs in
def widenTrunc : Com SLLVM (Ctxt.ofList [V 8]) .pure [V 32] := [sllvm| {
  ^entry(%a: vector<4xi8>):
    %r = "llvm.trunc"(%a) : (vector<4xi8>) -> vector<4xi32>
    "llvm.return"(%r) : (vector<4xi32>) -> ()
}]

end LeanMLIR.SLLVM.Tests.VectorCast
