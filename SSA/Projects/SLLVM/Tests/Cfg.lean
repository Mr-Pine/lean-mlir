/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# Forward CFG semantics

Hand-built CFGs pinning the denotation: a `cond_br` diamond joining at a
φ-carrying block (the `bb4`/`bb8` → `bb10` shape of `fd_f25519_is_zero`), a
`switch`, skipping over a block (`Target.there`), and UB on a poison
condition.
-/

namespace LeanMLIR.SLLVM.Tests.Cfg
open LeanMLIR

private def run {Γin : Ctxt SLLVM.Ty} (cfg : Cfg Γin [SLLVM.Ty.bitvec 32])
    (V : Γin.Valuation) : Option (PoisonOr (BitVec 32)) :=
  ((cfg.denote V).run ⟨⟨0⟩, ⟨∅⟩⟩).toOption.map (·.1.head)

/-- `c ? x : y`, as a diamond: both edges target the same one-argument block,
passing different values -- the φ shape. -/
private def diamond :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32])
      [SLLVM.Ty.bitvec 32] where
  entry := .term (.condBr ⟨0, rfl⟩ (.here [⟨1, rfl⟩]ₕ) (.here [⟨2, rfl⟩]ₕ))
  blocks := .cons (.term (.ret [⟨0, rfl⟩]ₕ)) .nil

private def diamondV (c : BitVec 1) :=
  run diamond <| Ctxt.Valuation.ofHVector
    [PoisonOr.value c, PoisonOr.value 11#32, PoisonOr.value 22#32]ₕ

#guard diamondV 1 == some (.value 11#32)
#guard diamondV 0 == some (.value 22#32)

-- Branching on poison is UB.
#guard (run diamond <| Ctxt.Valuation.ofHVector
  [PoisonOr.poison, PoisonOr.value 11#32, PoisonOr.value 22#32]ₕ).isNone

/-- A 3-way switch: case 0 and case `2^51 - 19` pick different region args,
the default block returns the third. Case blocks are entered through
`Target.there` chains, so this also covers skipping over blocks. -/
private def switch3 :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32,
        SLLVM.Ty.bitvec 32])
      [SLLVM.Ty.bitvec 32] where
  entry := .term (.switch ⟨0, rfl⟩
    (.there (.there (.here []ₕ)))
    [(0#64, .here []ₕ), (2251799813685229#64, .there (.here []ₕ))])
  blocks :=
    .cons (.term (.ret [⟨1, rfl⟩]ₕ)) <|   -- case 0: region arg %1
    .cons (.term (.ret [⟨2, rfl⟩]ₕ)) <|   -- case 2^51-19: region arg %2
    .cons (.term (.ret [⟨3, rfl⟩]ₕ)) .nil -- default: region arg %3

private def switch3V (x : BitVec 64) :=
  run switch3 <| Ctxt.Valuation.ofHVector
    [PoisonOr.value x, PoisonOr.value 10#32, PoisonOr.value 20#32, PoisonOr.value 30#32]ₕ

#guard switch3V 0 == some (.value 10#32)
#guard switch3V 2251799813685229#64 == some (.value 20#32)
#guard switch3V 7 == some (.value 30#32)

-- A poison scrutinee is UB.
#guard (run switch3 <| Ctxt.Valuation.ofHVector
  [PoisonOr.poison, PoisonOr.value 10#32, PoisonOr.value 20#32, PoisonOr.value 30#32]ₕ).isNone

/-! ## Through the quotation

`[sllvm_cfg| …]` = parse, `mkCfg`, reflect. The shapes below are the ones the
artifact uses: `cond_br` with branch operands (`operandSegmentSizes`), a
3-way `switch` with `case_values`, and `// pred:` comments. -/

/-- Both edges of the `cond_br` enter the same φ block with different
operands. -/
def brPhi : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i1):
    %0 = "llvm.mlir.constant"() <{value = 11 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 22 : i32}> : () -> i32
    "llvm.cond_br"(%arg0, %0, %1)[^bb1, ^bb1] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^bb1(%2: i32):  // 2 preds: ^bb0, ^bb0
    "llvm.return"(%2) : (i32) -> ()
}]

#guard run brPhi (Ctxt.Valuation.singleton (PoisonOr.value 1#1)) == some (.value 11#32)
#guard run brPhi (Ctxt.Valuation.singleton (PoisonOr.value 0#1)) == some (.value 22#32)

/-- The artifact's exact switch shape (attributes included). -/
def switchQuoted : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i64):
    "llvm.switch"(%arg0)[^bb3, ^bb1, ^bb2] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[0, 2251799813685229]> : vector<2xi64>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^bb1:  // pred: ^bb0
    %0 = "llvm.mlir.constant"() <{value = 10 : i32}> : () -> i32
    "llvm.return"(%0) : (i32) -> ()
  ^bb2:  // pred: ^bb0
    %1 = "llvm.mlir.constant"() <{value = 20 : i32}> : () -> i32
    "llvm.return"(%1) : (i32) -> ()
  ^bb3:  // pred: ^bb0
    %2 = "llvm.mlir.constant"() <{value = 30 : i32}> : () -> i32
    "llvm.return"(%2) : (i32) -> ()
}]

#guard run switchQuoted (Ctxt.Valuation.singleton (PoisonOr.value 0#64)) == some (.value 10#32)
#guard run switchQuoted (Ctxt.Valuation.singleton (PoisonOr.value 2251799813685229#64))
  == some (.value 20#32)
#guard run switchQuoted (Ctxt.Valuation.singleton (PoisonOr.value 7#64)) == some (.value 30#32)

/-! ## Calls

A call inside a CFG block is a `BlockCom.call` node whose callee is itself a
`Cfg`; a straight-line callee is the one-block case. The callee's frame dies
on return (`runFunction`), as with `SLLVMOp.call`. -/

/-- `sub(a, b) = a - b`: non-commutative, so an argument-order mistake in the
reverse convention shows up as a wrong value. -/
private def subRegion : MLIR.AST.Region 0 := [mlir_region| {
  ^bb0(%a: i32, %b: i32):
    %0 = "llvm.sub"(%a, %b) : (i32, i32) -> i32
    "llvm.return"(%0) : (i32) -> ()
}]

/-- `sel(c) = c ? 11 : 22` -- a genuinely multi-block callee. -/
private def selRegion : MLIR.AST.Region 0 := [mlir_region| {
  ^bb0(%c: i1):
    %0 = "llvm.mlir.constant"() <{value = 11 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 22 : i32}> : () -> i32
    "llvm.cond_br"(%c, %0, %1)[^bb1, ^bb1] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^bb1(%2: i32):  // 2 preds: ^bb0, ^bb0
    "llvm.return"(%2) : (i32) -> ()
}]

/-- Calls a one-block callee (`sub`) and a multi-block callee (`sel`), and
combines the results: `sub(sel(c), 1) = (c ? 11 : 22) - 1`. -/
def callBoth : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i1):
    %0 = "llvm.call"(%arg0) <{CConv = #llvm.cconv<fastcc>, callee = @sel, fastmathFlags = #llvm.fastmath<none>}> : (i1) -> i32
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.call"(%0, %1) <{callee = @sub}> : (i32, i32) -> i32
    "llvm.return"(%2) : (i32) -> ()
} with @sel := selRegion, @sub := subRegion]

#guard run callBoth (Ctxt.Valuation.singleton (PoisonOr.value 1#1)) == some (.value 10#32)
#guard run callBoth (Ctxt.Valuation.singleton (PoisonOr.value 0#1)) == some (.value 21#32)

/-- `selIndirect(c) = sel(c)`: a callee that itself calls a multi-block
callee -- `bindCallees` splices transitively and `mkCfg` recurses. -/
private def selIndirectRegion : MLIR.AST.Region 0 := [mlir_region| {
  ^bb0(%c: i1):
    %0 = "llvm.call"(%c) <{callee = @sel}> : (i1) -> i32
    "llvm.return"(%0) : (i32) -> ()
}]

def callNested : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i1):
    %0 = "llvm.call"(%arg0) <{callee = @selIndirect}> : (i1) -> i32
    "llvm.return"(%0) : (i32) -> ()
} with @selIndirect := selIndirectRegion, @sel := selRegion]

#guard run callNested (Ctxt.Valuation.singleton (PoisonOr.value 1#1)) == some (.value 11#32)
#guard run callNested (Ctxt.Valuation.singleton (PoisonOr.value 0#1)) == some (.value 22#32)

/-- A call in a *tail block* (after a branch), with the callee's result
flowing into the return -- the `fd_ed25519_point_is_zero` shape once it is
lifted. -/
def callInTailBlock : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i1):
    "llvm.cond_br"(%arg0)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %0 = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    %1 = "llvm.call"(%0) <{callee = @sel}> : (i1) -> i32
    "llvm.return"(%1) : (i32) -> ()
  ^bb2:  // pred: ^bb0
    %2 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "llvm.return"(%2) : (i32) -> ()
} with @sel := selRegion]

#guard run callInTailBlock (Ctxt.Valuation.singleton (PoisonOr.value 1#1))
  == some (.value 22#32)
#guard run callInTailBlock (Ctxt.Valuation.singleton (PoisonOr.value 0#1))
  == some (.value 7#32)

/--
error: Unsupported operation 'llvm.call to nowhere: the callee's body is not bound. Supply it with `with @nowhere := …`.'
-/
#guard_msgs in
def unboundCallee : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i1):
    %0 = "llvm.call"(%arg0) <{callee = @nowhere}> : (i1) -> i32
    "llvm.return"(%0) : (i32) -> ()
}]

/-! ## Rejected shapes -/

/--
error: ^bb1: backward or self branch -- only forward branches are supported (LIMITATIONS 5.1)
-/
#guard_msgs in
def backwardBranch : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i1):
    "llvm.br"()[^bb1] : () -> ()
  ^bb1:
    "llvm.br"()[^bb1] : () -> ()
  ^bb2:
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.return"(%0) : (i32) -> ()
}]

/--
error: 'llvm.mlir.constant' is not a terminator -- every block must end in llvm.return, llvm.br, llvm.cond_br or llvm.switch
-/
#guard_msgs in
def noTerminator : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i1):
    "llvm.br"()[^bb1] : () -> ()
  ^bb1:
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.return"(%0) : (i32) -> ()
  ^bb2:
    %1 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
}]

/--
error: %0 is not in scope in ^bb2: a CFG block may only use entry-block definitions and its own arguments (depth-1 dominance)
-/
#guard_msgs in
def crossBlockRef : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i1):
    "llvm.cond_br"(%arg0)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.br"()[^bb2] : () -> ()
  ^bb2:
    "llvm.return"(%0) : (i32) -> ()
}]

/--
error: expected 0 block argument(s), found 1
-/
#guard_msgs in
def phiArityMismatch : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i1):
    "llvm.br"(%arg0)[^bb1] : (i1) -> ()
  ^bb1:
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.return"(%0) : (i32) -> ()
}]

end LeanMLIR.SLLVM.Tests.Cfg
