/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg

/-!
# CFG semantics

Hand-built CFGs pinning the fueled interpreter (`Cfg.eval`): a `cond_br`
diamond joining at a φ-carrying block (the `bb4`/`bb8` → `bb10` shape of
`fd_f25519_is_zero`), a `switch`, UB on a poison condition, a counted loop,
an out-of-order forward edge, fuel exhaustion on an infinite loop, and values
read across tail blocks.
-/

namespace LeanMLIR.SLLVM.Tests.Cfg

open LeanMLIR

/-- Evaluate through the fueled interpreter (`Cfg.denote` is classical, so
`#guard` cannot run it). `none` conflates UB with fuel exhaustion; at this
fuel, every terminating test below is UB when it is `none`. -/
private def run {Γin : Ctxt SLLVM.Ty} (cfg : Cfg Γin [SLLVM.Ty.bitvec 32]) (V : Γin.Valuation) :
    Option (PoisonOr (BitVec 32)) :=
  match Cfg.eval 100 cfg V ⟨⟨0⟩, ⟨∅⟩, ∅⟩ with
  | some (.value (rs, _)) => some rs.head
  | _ => none

/-- `c ? x : y`, as a diamond: both edges target the same one-argument block,
passing different values -- the φ shape. -/
private def diamond :
    Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32])
      [SLLVM.Ty.bitvec 32]
    where
  entry := .term (.condBr ⟨0, rfl⟩ ⟨0, rfl, [⟨1, rfl⟩]ₕ⟩ ⟨0, rfl, [⟨2, rfl⟩]ₕ⟩)
  blocks := .cons (.term (.ret [⟨0, rfl⟩]ₕ)) .nil

private def diamondV (c : BitVec 1) :=
  run diamond <|
    Ctxt.Valuation.ofHVector [PoisonOr.value c, PoisonOr.value 11#32, PoisonOr.value 22#32]ₕ

#guard diamondV 1 == some (.value 11#32)

#guard diamondV 0 == some (.value 22#32)

-- Branching on poison is UB.
#guard
  (run diamond <|
      Ctxt.Valuation.ofHVector
        [PoisonOr.poison, PoisonOr.value 11#32, PoisonOr.value 22#32]ₕ).isNone

/-- A 3-way switch: case 0 and case `2^51 - 19` pick different region args,
the default block returns the third. Case blocks sit at distinct indices, so
this also covers targets past the first block. -/
private def switch3 :
    Cfg
      (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32])
      [SLLVM.Ty.bitvec 32]
    where
  entry :=
    .term
      (.switch ⟨0, rfl⟩ ⟨2, rfl, []ₕ⟩ [(0#64, ⟨0, rfl, []ₕ⟩), (2251799813685229#64, ⟨1, rfl, []ₕ⟩)])
  blocks :=
    .cons (.term (.ret [⟨1, rfl⟩]ₕ)) <| -- case 0: region arg %1
      .cons (.term (.ret [⟨2, rfl⟩]ₕ)) <| -- case 2^51-19: region arg %2
      .cons (.term (.ret [⟨3, rfl⟩]ₕ)) .nil -- default: region arg %3

private def switch3V (x : BitVec 64) :=
  run switch3 <|
    Ctxt.Valuation.ofHVector
      [PoisonOr.value x, PoisonOr.value 10#32, PoisonOr.value 20#32, PoisonOr.value 30#32]ₕ

#guard switch3V 0 == some (.value 10#32)

#guard switch3V 2251799813685229#64 == some (.value 20#32)

#guard switch3V 7 == some (.value 30#32)

-- A poison scrutinee is UB.
#guard
  (run switch3 <|
      Ctxt.Valuation.ofHVector
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

#guard
  run switchQuoted (Ctxt.Valuation.singleton (PoisonOr.value 2251799813685229#64)) ==
    some (.value 20#32)

#guard run switchQuoted (Ctxt.Valuation.singleton (PoisonOr.value 7#64)) == some (.value 30#32)

/-! ## Calls

A call inside a CFG block is a `BlockCom.call` node whose callee is itself a
`Cfg`; a straight-line callee is the one-block case. The callee's frame dies
on return (`runFunction`), as with `SLLVMOp.call`. -/

/-- `sub(a, b) = a - b`: non-commutative, so an argument-order mistake in the
reverse convention shows up as a wrong value. -/
private def subRegion : MLIR.AST.Region 0 :=
  [mlir_region|{^bb0(%a:i32,%b:i32):%0="llvm.sub"(%a, %b):(i32,
            i32)->i32"llvm.return"(%0):(i32)->()}]

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
def callBoth : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg|
    {^bb0(%arg0:i1):%0="llvm.call"(%arg0)<{CConv = #llvm.cconv<fastcc>,callee = @sel,fastmathFlags =
              #llvm.fastmath<none>}>:(i1)->i32%1="llvm.mlir.constant"()<{value =
              1:i32}>:()->i32%2="llvm.call"(%0, %1)<{callee = @sub}>:(i32,
            i32)->i32"llvm.return"(%2):(i32)->()} with
    @sel := selRegion, @sub := subRegion]

#guard run callBoth (Ctxt.Valuation.singleton (PoisonOr.value 1#1)) == some (.value 10#32)

#guard run callBoth (Ctxt.Valuation.singleton (PoisonOr.value 0#1)) == some (.value 21#32)

/-- `selIndirect(c) = sel(c)`: a callee that itself calls a multi-block
callee -- `bindCallees` splices transitively and `mkCfg` recurses. -/
private def selIndirectRegion : MLIR.AST.Region 0 :=
  [mlir_region|{^bb0(%c:i1):%0="llvm.call"(%c)<{callee =
              @sel}>:(i1)->i32"llvm.return"(%0):(i32)->()}]

def callNested : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg|
    {^bb0(%arg0:i1):%0="llvm.call"(%arg0)<{callee =
              @selIndirect}>:(i1)->i32"llvm.return"(%0):(i32)->()} with
    @selIndirect := selIndirectRegion, @sel := selRegion]

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

#guard run callInTailBlock (Ctxt.Valuation.singleton (PoisonOr.value 1#1)) == some (.value 22#32)

#guard run callInTailBlock (Ctxt.Valuation.singleton (PoisonOr.value 0#1)) == some (.value 7#32)

/--
error: Unsupported operation 'llvm.call to nowhere: the callee's body is not bound. Supply it with `with @nowhere := …` or define a lifted `nowhere` in scope.'
-/
#guard_msgs in
def unboundCallee : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg|
    {^bb0(%arg0:i1):%0="llvm.call"(%arg0)<{callee =
              @nowhere}>:(i1)->i32"llvm.return"(%0):(i32)->()}]

/-! ## Loops and out-of-order edges -/

/-- A counted do-while, the artifact's exact latch shape: enter with the
counter at 1, `add`/`icmp eq`/`cond_br` back to the header until it reaches
5, then pass the final counter to the exit block. 4 iterations. -/
def countLoop : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i32):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    "llvm.br"(%arg0)[^bb1] : (i32) -> ()
  ^bb1(%2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = "llvm.add"(%2, %0) : (i32, i32) -> i32
    %4 = "llvm.icmp"(%3, %1) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%4, %3, %3)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^bb2(%5: i32):  // pred: ^bb1
    "llvm.return"(%5) : (i32) -> ()
}]

#guard run countLoop (Ctxt.Valuation.singleton (PoisonOr.value 1#32)) == some (.value 5#32)

#guard run countLoop (Ctxt.Valuation.singleton (PoisonOr.value 4#32)) == some (.value 5#32)

-- A loop that never exits runs out of fuel: `eval` says "still running".
def spin : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i32):
    "llvm.br"()[^bb1] : () -> ()
  ^bb1:  // 2 preds: ^bb0, ^bb1
    "llvm.br"()[^bb1] : () -> ()
  ^bb2:  // no preds: unreachable, supplies the region's return type
    "llvm.return"(%arg0) : (i32) -> ()
}]

#guard (Cfg.eval 100 spin (Ctxt.Valuation.singleton (PoisonOr.value 0#32)) ⟨⟨0⟩, ⟨∅⟩, ∅⟩).isNone

/-- An edge that is *forward in the CFG* but backward in the printed block
order (`^bb2 → ^bb1`) -- the pow22523 shape that indexing targets by the
remaining list used to reject. -/
def outOfOrder : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32]) [SLLVM.Ty.bitvec 32] := [sllvm_cfg| {
  ^bb0(%arg0: i32):
    "llvm.br"()[^bb2] : () -> ()
  ^bb1:  // pred: ^bb2
    "llvm.return"(%arg0) : (i32) -> ()
  ^bb2:  // pred: ^bb0
    "llvm.br"()[^bb1] : () -> ()
}]

#guard run outOfOrder (Ctxt.Valuation.singleton (PoisonOr.value 9#32)) == some (.value 9#32)

/-! ## Values used across tail blocks

`threadLive` passes a tail block's definition to the blocks it dominates as an
extra block argument. -/

/-- `%1`, defined in `^bb1`, is read two blocks later in `^bb3`. -/
def crossBlockDom : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg|
    {^bb0(%arg0:i32):"llvm.br"()[^bb1]:()->()^bb1:%0="llvm.mlir.constant"()<{value =
              3:i32}>:()->i32%1="llvm.add"(%arg0, %0):(i32,
            i32)->i32"llvm.br"()[^bb2]:()->()^bb2:"llvm.br"()[^bb3]:()->()^bb3:"llvm.return"(%1):(i32)->()}]

#guard run crossBlockDom (Ctxt.Valuation.singleton (PoisonOr.value 4#32)) == some (.value 7#32)

/-- A loop whose body reads the preheader's `%1` and the header's `%3`, and
exits through a `cond_br` whose segments grow on both sides. Counts `%arg0` up
by `%1 = 2` until it passes 9, returning the header's last value plus `%1`. -/
def loopDom : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 32]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg|
    {^bb0(%arg0:i32):"llvm.br"(%arg0)[^bb1]:(i32)->()^bb1(%0:i32):%1="llvm.mlir.constant"()<{value =
              2:i32}>:()->i32%2="llvm.mlir.constant"()<{value =
              9:i32}>:()->i32"llvm.br"(%0)[^bb2]:(i32)->()^bb2(%3:i32):%4="llvm.icmp"(%3,
            %2)<{predicate = 4:i64}>:(i32,
            i32)->i1"llvm.cond_br"(%4)[^bb4,
            ^bb3]<{operandSegmentSizes =
              array<i32:1,0,0>}>:(i1)->()^bb3:%5="llvm.add"(%3, %1):(i32,
            i32)->i32"llvm.br"(%5)[^bb2]:(i32)->()^bb4:%6="llvm.add"(%3, %1):(i32,
            i32)->i32"llvm.return"(%6):(i32)->()}]

#guard run loopDom (Ctxt.Valuation.singleton (PoisonOr.value 0#32)) == some (.value 12#32)

#guard run loopDom (Ctxt.Valuation.singleton (PoisonOr.value 11#32)) == some (.value 13#32)

/-! ## Rejected shapes -/

/--
error: 'llvm.mlir.constant' is not a terminator -- every block must end in llvm.return, llvm.unreachable, llvm.br, llvm.cond_br or llvm.switch
-/
#guard_msgs in
def noTerminator : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg|
    {^bb0(%arg0:i1):"llvm.br"()[^bb1]:()->()^bb1:%0="llvm.mlir.constant"()<{value =
              1:i32}>:()->i32"llvm.return"(%0):(i32)->()^bb2:%1="llvm.mlir.constant"()<{value =
              2:i32}>:()->i32}]

/--
error: %0 does not dominate its uses: a path from the entry block reaches them without defining it
-/
#guard_msgs in
def crossBlockRef : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg|
    {^bb0(%arg0:i1):"llvm.cond_br"(%arg0)[^bb1,
            ^bb2]<{operandSegmentSizes =
              array<i32:1,0,0>}>:(i1)->()^bb1:%0="llvm.mlir.constant"()<{value =
              1:i32}>:()->i32"llvm.br"()[^bb2]:()->()^bb2:"llvm.return"(%0):(i32)->()}]

/--
error: expected 0 block argument(s), found 1
-/
#guard_msgs in
def phiArityMismatch : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg|
    {^bb0(%arg0:i1):"llvm.br"(%arg0)[^bb1]:(i1)->()^bb1:%0="llvm.mlir.constant"()<{value =
              1:i32}>:()->i32"llvm.return"(%0):(i32)->()}]

end LeanMLIR.SLLVM.Tests.Cfg
