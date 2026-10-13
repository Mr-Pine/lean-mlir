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

-- `inline` and `named` after a lemma and its arguments: modifiers, not arguments
example (s : GlobalState) (hwf : s.WF) :
    dbl3.call (dbl3.args (.value 0)) s = .value (.cons (.value 8#64) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pattern using runBodyFrom_dbl2Run inline
  fail_if_success have := hv2
  step_pattern using runBodyFrom_dblRun (X := _) named
  have := hv3
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

mlir_def halfAdd :=
{
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.poison"() : () -> vector<2xi64>
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.insertelement"(%0, %arg0, %1) : (vector<2xi64>, i64, i64) -> vector<2xi64>
    %3 = "llvm.add"(%2, %2) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.return"(%3) : (vector<2xi64>) -> ()
}

/-- `r = k + j` on vectors. -/
def addVRun (k j r : Dst Γ (.vec 2 64)) : List (Instr Γ) :=
  [.binop (.vector (.add {})) r (.val k.i k.h) (.val j.i j.h)]

-- a read of a vector with a poison lane, in `E ⊨ […]`
theorem runBodyFrom_addVRun {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {k j r : Dst Γ (.vec 2 64)} {rest : List (Instr Γ)} {X Y : BitVec 64} {S : GlobalState}
    {g : ⟪Γ⟫ × GlobalState → PoisonOr β} {K : PoisonOr β}
    (hbody : blk.body.drop pos = addVRun k j r ++ rest)
    (hR : E ⊨ [k := #v[.value X, .poison], j := #v[.value Y, .poison]])
    (hK : (blk.runBodyFrom E[r := #v[.value (X + Y), .poison]] (pos + 1) S >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pure
  rw [hE]
  exact hK

example (x : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    halfAdd.call (halfAdd.args (.value x)) s =
      .value (.cons #v[.value (x + x), .poison] .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pattern using runBodyFrom_addVRun
  finish_block
  subst_vars
  rfl

/-- `r` a shuffle of `x` and `y` by `m`. -/
def shufRun (m : Vector (Option (Fin (2 * 8))) 8) (x y r : Dst Γ (.vec 8 64)) : List (Instr Γ) :=
  [.binop (.shufflevector m) r (.val x.i x.h) (.val y.i y.h)]

-- a shuffle by a mask parameter stays folded: its lanes cannot be decided
theorem runBodyFrom_shufRun {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {m : Vector (Option (Fin (2 * 8))) 8} {x y r : Dst Γ (.vec 8 64)} {rest : List (Instr Γ)}
    {X Y : Vector (BitVec 64) 8} {S : GlobalState} {g : ⟪Γ⟫ × GlobalState → PoisonOr β}
    {K : PoisonOr β} (hbody : blk.body.drop pos = shufRun m x y r ++ rest)
    (hR : E ⊨ [x := X, y := Y])
    (hK :
      (blk.runBodyFrom E[r := Operation.shufflevector m (Ty.wrap (t := .vec 8 64) X) (Ty.wrap Y)]
            (pos + 1) S >>=
          g) =
        K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pure
  rw [hE]
  exact hK

/-- A shuffle by `m`, folded. -/
@[irreducible]
def shuf (m : Vector (Option (Fin (2 * 8))) 8) (X Y : Vector (BitVec 64) 8) : ⟦.vec 8 64⟧ :=
  Operation.shufflevector m (Ty.wrap (t := .vec 8 64) X) (Ty.wrap Y)

theorem shufflevector_eq_shuf (m : Vector (Option (Fin (2 * 8))) 8) (X Y : Vector (BitVec 64) 8) :
    Operation.shufflevector m (Ty.wrap (t := .vec 8 64) X) (Ty.wrap Y) = shuf m X Y := by
  unfold shuf
  rfl

-- ... for a lemma about it, which needs its operands resolved
example {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {m : Vector (Option (Fin (2 * 8))) 8} {x y r : Dst Γ (.vec 8 64)} {rest : List (Instr Γ)}
    {X Y : Vector (BitVec 64) 8} {S : GlobalState} {g : ⟪Γ⟫ × GlobalState → PoisonOr β}
    {K : PoisonOr β} (hbody : blk.body.drop pos = shufRun m x y r ++ rest)
    (hR : E ⊨ [x := X, y := Y])
    (hK : (blk.runBodyFrom E[r := shuf m X Y] (pos + 1) S >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pure [shufflevector_eq_shuf]
  rw [hE]
  exact hK

mlir_def put3 :=
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.add"(%0, %0) : (i64, i64) -> i64
    "llvm.store"(%1, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %2 = "llvm.getelementptr"(%arg0) <{elem_type = i8, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%1, %2) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %3 = "llvm.getelementptr"(%arg0) <{elem_type = i8, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%1, %3) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

/-- `y = x + x` stored at `p`, `p + 8` (through `q`) and `p + 16` (through `q'`). -/
def put3Run (x y : Dst Γ (.bv 64)) (p : Reg Γ .ptr) (q q' : Dst Γ .ptr) : List (Instr Γ) :=
  [.binop (.add {}) y (.val x.i x.h) (.val x.i x.h), .store p (.val y.i y.h),
    .unop (.gepConst {} 8) q p, .store (.val q.i q.h) (.val y.i y.h), .unop (.gepConst {} 16) q' p,
    .store (.val q'.i q'.h) (.val y.i y.h)]

-- stores through a pointer register that may be an argument or a value
theorem runBodyFrom_put3Run {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {x y : Dst Γ (.bv 64)} {p : Reg Γ .ptr} {q q' : Dst Γ .ptr} {rest : List (Instr Γ)}
    {X : BitVec 64} {P : Pointer} {S : GlobalState} {g : ⟪Γ⟫ × GlobalState → PoisonOr β}
    {K : PoisonOr β} (hbody : blk.body.drop pos = put3Run x y p q q' ++ rest)
    (hR : E ⊨ [x := X, p := P]) (hpq : p ≠ .val q.i q.h) (hwf : S.WF)
    (hP : Fits S.mem P 64) (hP8 : Fits S.mem (P.add 8#64) 64) (hP16 : Fits S.mem (P.add 16#64) 64)
    (hK :
      ∀ vq vq',
        (blk.runBodyFrom E[y := .value (X + X), q := vq, q' := vq'] (pos + 6)
              { S with
                mem :=
                  ((S.mem.storeAt P (X + X)).storeAt (P.add 8#64) (X + X)).storeAt (P.add 16#64)
                    (X + X) } >>=
            g) =
          K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pure
  step_store
  step_pure
  step_store
  step_pure
  step_store
  subst_vars
  exact hK _ _

example (p : Pointer) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 64)
    (hp8 : Fits s.mem (p.add 8#64) 64) (hp16 : Fits s.mem (p.add 16#64) 64) :
    put3.call (put3.args (.value p)) s =
      .value
        (.nil,
          { s with
            mem :=
              ((s.mem.storeAt p 2#64).storeAt (p.add 8#64) 2#64).storeAt (p.add 16#64) 2#64 }) := by
  func_init
  block_init
  step_pure
  step_pattern using runBodyFrom_put3Run
  finish_block
  subst_vars
  rfl

/-! ## Values and states the continuation binds -/

-- `y = x + x`, the value bound by the continuation with its equation
theorem runBodyFrom_dblRunBound {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {x y : Dst Γ (.bv 64)} {rest : List (Instr Γ)} {X : BitVec 64} {S : GlobalState}
    {g : ⟪Γ⟫ × GlobalState → PoisonOr β} {K : PoisonOr β}
    (hbody : blk.body.drop pos = dblRun x y ++ rest) (hR : E ⊨ [x := X])
    (hK : ∀ Y : BitVec 64, Y = X + X → (blk.runBodyFrom E[y := .value Y] (pos + 1) S >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pure
  rw [hE]
  exact hK _ rfl

-- `with` names the bound value, its anonymous equation after it
example (s : GlobalState) (hwf : s.WF) :
    dbl3.call (dbl3.args (.value 0)) s = .value (.cons (.value 8#64) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pattern using runBodyFrom_dblRunBound with a
  have : a = 1#64 + 1#64 := ha
  step_pattern using runBodyFrom_dblRunBound with b
  have : b = a + a := hb
  step_pattern using runBodyFrom_dblRun
  finish_block
  subst_vars
  rfl

/-- `*p = y`, then `z = *p`. -/
def putGetRun (y : Dst Γ (.bv 64)) (p : Reg Γ .ptr) (z : Dst Γ (.bv 64)) : List (Instr Γ) :=
  [.store p (.val y.i y.h), .load z p]

-- the store's state bound by the continuation, known only by the facts it states
theorem runBodyFrom_putRun {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {y : Dst Γ (.bv 64)} {p : Reg Γ .ptr} {rest : List (Instr Γ)} {Y : BitVec 64} {P : Pointer}
    {S : GlobalState} {g : ⟪Γ⟫ × GlobalState → PoisonOr β} {K : PoisonOr β}
    (hbody : blk.body.drop pos = [.store p (.val y.i y.h)] ++ rest) (hR : E ⊨ [y := Y, p := P])
    (hP : Room S.mem P 64)
    (hK :
      ∀ S' : GlobalState,
        Fits S'.mem P 64 → S'.mem.readAt P 64 = Y → (blk.runBodyFrom E (pos + 1) S' >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_store
  exact hK _ hfits_P hread_P

-- a fresh state: the old state's facts dropped (no goals), the continuation's about `S`
theorem runBodyFrom_putGetRun {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {y z : Dst Γ (.bv 64)} {p : Reg Γ .ptr} {rest : List (Instr Γ)} {Y : BitVec 64}
    {P : Pointer} {S : GlobalState} {g : ⟪Γ⟫ × GlobalState → PoisonOr β} {K : PoisonOr β}
    (hbody : blk.body.drop pos = putGetRun y p z ++ rest) (hR : E ⊨ [y := Y, p := P])
    (hP : Room S.mem P 64) (hwf : S.WF)
    (hK : ∀ S' : GlobalState, (blk.runBodyFrom E[z := .value Y] (pos + 2) S' >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pattern using runBodyFrom_putRun
  fail_if_success have := hwf
  step_load
  subst_vars
  exact hK _

end

end MLIR.Tests.Syntax.Patterns
