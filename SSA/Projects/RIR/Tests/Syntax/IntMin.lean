module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Run.Tactic
meta import SSA.Projects.RIR.Semantics.Func

/-! # `mlir_def` on `fd_int_min`: the hand lift, its tests and its proof -/

namespace LeanMLIR.RIR.Tests.Syntax

@[expose] public section

mlir_def fd_int_min := {
  ^bb0(%arg0: i32):
    %0 = "llvm.mlir.constant"() <{value = 14 : i32}> : () -> i32
    %1 = "llvm.intr.smin"(%arg0, %0) : (i32, i32) -> i32
    "llvm.return"(%1) : (i32) -> ()
}

/-! The hand lift, for comparison. -/
namespace Hand

abbrev fd_int_min.Γ : Ctx :=
  ⟨[.bv 32], [.bv 32, .bv 32]⟩

abbrev fd_int_min.blockTys : Fin 1 → List Ty := fun _ => []

abbrev fd_int_min.blockParams : (k : Fin 1) → Dsts fd_int_min.Γ (fd_int_min.blockTys k) :=
  fun _ => .nil

def fd_int_min.entry : BasicBlock fd_int_min.Γ [.bv 32] fd_int_min.blockTys where
  body :=
    [ .const (14 : BitVec 32) ⟨0, rfl⟩,
      .binop .smin ⟨1, rfl⟩ (.arg 0 rfl) (.val 0 rfl)]
  exit := .ret (.cons (.val 1 rfl) .nil)

@[reducible]
def fd_int_min : Func where
  Γ := fd_int_min.Γ
  tRets := [.bv 32]
  n := 1
  blockTys := fd_int_min.blockTys
  blockParams := fd_int_min.blockParams
  hhasBlock := by decide
  hentry := rfl
  blocks := fun _ => fd_int_min.entry

def fd_int_min.args (x : ⟦Ty.bv 32⟧) : Vals fd_int_min.Γ.args :=
  .cons x .nil

end Hand

example : fd_int_min = Hand.fd_int_min := rfl
example : fd_int_min.args = Hand.fd_int_min.args := rfl

/-- `smin`'s result, as a mathematical function. -/
def fd_int_min.spec (x : BitVec 32) : BitVec 32 :=
  if x.slt 14#32 then x else 14#32

end

/-! ## Execution tests -/

section Tests

private def s0 : GlobalState :=
  ⟨default, default⟩

private def out (x : PoisonOr (BitVec 32)) (fuel : Nat := 1) : Option (PoisonOr (BitVec 32)) :=
  match fd_int_min.eval fuel (fd_int_min.args x) s0 with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

#guard out (.value 3#32) == some (.value 3#32)
#guard out (.value 20#32) == some (.value 14#32)
#guard out (.value (-5 : BitVec 32)) == some (.value (-5 : BitVec 32))
#guard out .poison == some .poison
#guard out (.value 3#32) 0 == none

end Tests

/-! ## The hand lift's proof -/

public theorem fd_int_min.call_eq (x : BitVec 32) (s : GlobalState) (hwf : s.WF) :
    fd_int_min.call (fd_int_min.args (.value x)) s =
      .value (.cons (.value (fd_int_min.spec x)) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pure
  finish_block
  rw [hS, fd_int_min.spec]

end LeanMLIR.RIR.Tests.Syntax
