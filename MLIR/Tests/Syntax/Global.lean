module

public import MLIR.Syntax.Elab
meta import MLIR.Semantics.Func
meta import MLIR.Semantics.GlobalInitializer

/-! # `mlir_const_def`, and `llvm.mlir.addressof` of the global it defines -/

namespace MLIR.Tests.Syntax.Global

@[expose] public section

mlir_const_def answer := {
    %0 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    "llvm.return"(%0) : (i64) -> ()
}

example : answer.t = .bv 64 := rfl

mlir_def readAnswer := {
    %0 = "llvm.mlir.addressof"() <{global_name = @answer}> : () -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1) : (i64) -> ()
} with @answer := answer

mlir_const_def limbs := {
    %0 = "llvm.mlir.constant"() <{value = dense<[1, 2, 3, 4, 5]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    "llvm.return"(%0) : (!llvm.array<5 x i64>) -> ()
}

example : limbs.t = .array 5 (.bv 64) := rfl

mlir_def readLimb1 := {
    %0 = "llvm.mlir.addressof"() <{global_name = @limbs}> : () -> !llvm.ptr
    %1 = "llvm.getelementptr"(%0) <{elem_type = i64, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%2) : (i64) -> ()
} with @limbs := limbs

/-- Two addresses of one global, compared. -/
mlir_def sameAddress := {
    %0 = "llvm.mlir.addressof"() <{global_name = @answer}> : () -> !llvm.ptr
    %1 = "llvm.mlir.addressof"() <{global_name = @answer}> : () -> !llvm.ptr
    %2 = "llvm.icmp"(%0, %1) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.return"(%2) : (i1) -> ()
} with @answer := answer

/-- The addresses of two globals, compared. -/
mlir_def otherAddress := {
    %0 = "llvm.mlir.addressof"() <{global_name = @answer}> : () -> !llvm.ptr
    %1 = "llvm.mlir.addressof"() <{global_name = @limbs}> : () -> !llvm.ptr
    %2 = "llvm.icmp"(%0, %1) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.return"(%2) : (i1) -> ()
} with @answer := answer, @limbs := limbs

/-- A store into a constant global: UB. -/
mlir_def storeAnswer := {
    %0 = "llvm.mlir.addressof"() <{global_name = @answer}> : () -> !llvm.ptr
    %1 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "llvm.store"(%1, %0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
} with @answer := answer

/-- A mutable global, `0` initially. -/
mlir_const_def counter :=
"llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 8 : i64, global_type = i64, linkage = #llvm.linkage<internal>, sym_name = "counter", value = 0 : i64, visibility_ = 0 : i64}> ({
}) : () -> ()

example : counter.constant = false :=
  rfl

/-- Store `x` into `counter`, then load it back, and its old value read first. -/
mlir_def bumpCounter := {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.addressof"() <{global_name = @counter}> : () -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.store"(%arg0, %0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %2 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1, %2) : (i64, i64) -> ()
} with @counter := counter

end

/-! ## Execution tests -/

section Tests

/-- What `readAnswer` returns from an empty state, or `none` for UB. -/
private def out : Option (BitVec 64) :=
  match readAnswer.eval 1 readAnswer.args (GlobalState.withGlobals readAnswer.globals ⟨⟨1⟩, ⟨∅⟩⟩)
    with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none

#guard out == some 42#64

/-- Element `1` of `limbs`, read through its address, or `none` for UB. -/
private def limb1 : Option (BitVec 64) :=
  match readLimb1.eval 1 readLimb1.args (GlobalState.withGlobals readLimb1.globals ⟨⟨1⟩, ⟨∅⟩⟩)
    with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none

#guard limb1 == some 2#64

/-- What `f` returns from no arguments in a state holding its globals, if it returns one `i1`. -/
private def flag (f : Func) : Option (PoisonOr (BitVec 1)) :=
  if h : f.Γ.args = [] ∧ f.tRets = [.bv 1] then
    match f.eval 1 (h.1 ▸ .nil) (GlobalState.withGlobals f.globals ⟨⟨1⟩, ⟨∅⟩⟩) with
    | .value (some vs, _) => match h.2 ▸ vs with | .cons v .nil => some v
    | _ => none
  else none

-- one global's addresses are equal, two globals' not
#guard flag sameAddress == some (.value 1)
#guard flag otherAddress == some (.value 0)

-- a store into a constant global is UB
#guard (match storeAnswer.eval 1 storeAnswer.args
    (GlobalState.withGlobals storeAnswer.globals ⟨⟨1⟩, ⟨∅⟩⟩) with
  | .poison => true
  | _ => false)

-- a mutable global: its initial value, then what was stored
#guard (match bumpCounter.eval 1 (bumpCounter.args (.value 5))
    (GlobalState.withGlobals bumpCounter.globals ⟨⟨1⟩, ⟨∅⟩⟩) with
  | .value (some (.cons a (.cons b .nil)), _) => a == .value 0 && b == .value 5
  | _ => false)

-- without the globals placed, `addressof` is UB
#guard (match readAnswer.eval 1 readAnswer.args ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .poison => true
  | _ => false)

end Tests

end MLIR.Tests.Syntax.Global
