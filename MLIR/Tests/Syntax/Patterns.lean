module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic

/-! # `step_pattern` regressions -/

namespace MLIR.Tests.Syntax.Patterns

@[expose] public section

mlir_def dbl3 :=
{
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.add"(%0, %0) : (i64, i64) -> i64
    %2 = "llvm.add"(%1, %1) : (i64, i64) -> i64
    %3 = "llvm.add"(%2, %2) : (i64, i64) -> i64
    "llvm.return"(%3) : (i64) -> ()
}

/-- `y = x + x`. -/
def dblRun (x y : Dst Γ (.bv 64)) : List (Instr Γ) :=
  [.binop (.add {}) y (.val x.i x.h) (.val x.i x.h)]

theorem runBodyFrom_dblRun {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {x y : Dst Γ (.bv 64)} {rest : List (Instr Γ)} {X : BitVec 64} {S : GlobalState}
    {g : ⟪Γ⟫ × GlobalState → PoisonOr β} {K : PoisonOr β}
    (hbody : blk.body.drop pos = dblRun x y ++ rest) (hR : E ⊨ [x := X])
    (hK : (blk.runBodyFrom E[y := .value (X + X)] (pos + 1) S >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pure
  rw [hE]
  exact hK

/-- Two doublings. -/
def dbl2Run (x y z : Dst Γ (.bv 64)) : List (Instr Γ) :=
  dblRun x y ++ dblRun y z

-- a pattern stepped inside another pattern's proof, over the abstract block
theorem runBodyFrom_dbl2Run {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {x y z : Dst Γ (.bv 64)} {rest : List (Instr Γ)} {X : BitVec 64} {S : GlobalState}
    {g : ⟪Γ⟫ × GlobalState → PoisonOr β} {K : PoisonOr β}
    (hbody : blk.body.drop pos = dbl2Run x y z ++ rest) (hR : E ⊨ [x := X])
    (hK : ∀ vy, (blk.runBodyFrom E[y := vy, z := .value (X + X + (X + X))] (pos + 2) S >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pattern using runBodyFrom_dblRun
  step_pattern using runBodyFrom_dblRun
  subst_vars
  exact hK _

example (s : GlobalState) (hwf : s.WF) :
    dbl3.call (dbl3.args (.value 0)) s = .value (.cons (.value 8#64) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pattern using runBodyFrom_dbl2Run
  step_pattern using runBodyFrom_dblRun
  finish_block
  subst_vars
  rfl

mlir_def sum2 :=
{
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %2 = "llvm.add"(%0, %1) : (i64, i64) -> i64
    "llvm.return"(%2) : (i64) -> ()
}

/-- `z = x + y`. -/
def addRun (x y z : Dst Γ (.bv 64)) : List (Instr Γ) :=
  [.binop (.add {}) z (.val x.i x.h) (.val y.i y.h)]

/-- `x` and `y` hold `X` and `Y`. -/
abbrev Holds2 (E : ⟪Γ⟫) (x y : Dst Γ (.bv 64)) (X Y : BitVec 64) : Prop :=
  E ⊨ [x := X, y := Y]

-- reads stated through an abbreviation: a fact in the lemma's proof, a premise at the site
theorem runBodyFrom_addRun {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {x y z : Dst Γ (.bv 64)} {rest : List (Instr Γ)} {X Y : BitVec 64} {S : GlobalState}
    {g : ⟪Γ⟫ × GlobalState → PoisonOr β} {K : PoisonOr β}
    (hbody : blk.body.drop pos = addRun x y z ++ rest) (hR : Holds2 E x y X Y)
    (hK : (blk.runBodyFrom E[z := .value (X + Y)] (pos + 1) S >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pure
  rw [hE]
  exact hK

example (s : GlobalState) (hwf : s.WF) :
    sum2.call (sum2.args (.value 0)) s = .value (.cons (.value 3#64) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pure
  step_pattern using runBodyFrom_addRun
  finish_block
  subst_vars
  rfl

end

end MLIR.Tests.Syntax.Patterns
