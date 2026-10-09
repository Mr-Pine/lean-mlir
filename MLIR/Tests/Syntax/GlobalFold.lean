module

public import MLIR.Syntax.Elab
meta import MLIR.Semantics.Func
meta import MLIR.Semantics.GlobalInitializer

/-! # `mlir_const_def` folds an initializer built by `insertvalue`s to its constant -/

namespace MLIR.Tests.Syntax.GlobalFold

@[expose] public section

/-- `[{7, [1, 2]}, {7, [9, 2]}]`, the `9` inserted into a copy of the constant `[1, 2]`. -/
mlir_const_def pairs := {
    %0 = "llvm.mlir.constant"() <{value = dense<[1, 2]> : tensor<2xi64>}> : () -> !llvm.array<2 x i64>
    %1 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %2 = "llvm.mlir.undef"() : () -> !llvm.struct<(i64, array<2 x i64>)>
    %3 = "llvm.insertvalue"(%2, %1) <{position = array<i64: 0>}> : (!llvm.struct<(i64, array<2 x i64>)>, i64) -> !llvm.struct<(i64, array<2 x i64>)>
    %4 = "llvm.insertvalue"(%3, %0) <{position = array<i64: 1>}> : (!llvm.struct<(i64, array<2 x i64>)>, !llvm.array<2 x i64>) -> !llvm.struct<(i64, array<2 x i64>)>
    %5 = "llvm.mlir.undef"() : () -> !llvm.array<2 x struct<(i64, array<2 x i64>)>>
    %6 = "llvm.insertvalue"(%5, %4) <{position = array<i64: 0>}> : (!llvm.array<2 x struct<(i64, array<2 x i64>)>>, !llvm.struct<(i64, array<2 x i64>)>) -> !llvm.array<2 x struct<(i64, array<2 x i64>)>>
    %7 = "llvm.insertvalue"(%6, %4) <{position = array<i64: 1>}> : (!llvm.array<2 x struct<(i64, array<2 x i64>)>>, !llvm.struct<(i64, array<2 x i64>)>) -> !llvm.array<2 x struct<(i64, array<2 x i64>)>>
    %8 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %9 = "llvm.insertvalue"(%7, %8) <{position = array<i64: 1, 1, 0>}> : (!llvm.array<2 x struct<(i64, array<2 x i64>)>>, i64) -> !llvm.array<2 x struct<(i64, array<2 x i64>)>>
    "llvm.return"(%9) : (!llvm.array<2 x struct<(i64, array<2 x i64>)>>) -> ()
}

-- one value, the literal
example : pairs.Γ.n = 1 := rfl
example : pairs.lit = #v[(7, #v[1, 2]), (7, #v[9, 2])] := rfl

example (s : GlobalState) : pairs.value s = .value (Ty.wrap pairs.lit, s) :=
  GlobalInitializer.compute_value _ _ ⟨_, by with_unfolding_all rfl⟩

/-- Element `1`'s array's `0`th `i64`, `9`, read through the global's address. -/
mlir_def readPairs := {
    %0 = "llvm.mlir.addressof"() <{global_name = @pairs}> : () -> !llvm.ptr
    %1 = "llvm.getelementptr"(%0) <{elem_type = !llvm.array<2 x struct<(i64, array<2 x i64>)>>, rawConstantIndices = array<i32: 0, 1, 1, 0>}> : (!llvm.ptr) -> !llvm.ptr
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%2) : (i64) -> ()
} with @pairs := pairs

/-- `fd_f25519_zero` as LLVM 23 builds it: one `zero` of the whole array. -/
mlir_const_def zeros := {
    %0 = "llvm.mlir.zero"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    "llvm.return"(%0) : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>) -> ()
}

example : zeros.lit = #v[#v[0, 0, 0, 0, 0]] := rfl

example (s : GlobalState) : zeros.value s = .value (Ty.wrap zeros.lit, s) :=
  GlobalInitializer.compute_value _ _ ⟨_, by with_unfolding_all rfl⟩

/-- `(0, null, 7)`: a `zero` with one field inserted. -/
mlir_const_def zeroThenSeven := {
    %0 = "llvm.mlir.zero"() : () -> !llvm.struct<(i64, ptr, i64)>
    %1 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %2 = "llvm.insertvalue"(%0, %1) <{position = array<i64: 2>}> : (!llvm.struct<(i64, ptr, i64)>, i64) -> !llvm.struct<(i64, ptr, i64)>
    "llvm.return"(%2) : (!llvm.struct<(i64, ptr, i64)>) -> ()
}

example : zeroThenSeven.Γ.n = 1 := rfl
example : zeroThenSeven.lit = (0, Pointer.null, 7) := rfl

/-- A struct whose second field stays `undef`: folded with a zero there, then that field poisoned
by one `insertvalue`. -/
mlir_const_def half := {
    %0 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %1 = "llvm.mlir.undef"() : () -> !llvm.struct<(i64, i64)>
    %2 = "llvm.insertvalue"(%1, %0) <{position = array<i64: 0>}> : (!llvm.struct<(i64, i64)>, i64) -> !llvm.struct<(i64, i64)>
    "llvm.return"(%2) : (!llvm.struct<(i64, i64)>) -> ()
}

example : half.lit = (7, 0) := rfl
example : half.Γ.n = 3 := rfl

example (s : GlobalState) : half.value s = .value ((.value 7, .poison), s) :=
  GlobalInitializer.compute_value _ _ ⟨_, by with_unfolding_all rfl⟩

/-- `half`'s fields, read through its address. -/
mlir_def readHalf := {
    %0 = "llvm.mlir.addressof"() <{global_name = @half}> : () -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %2 = "llvm.getelementptr"(%0) <{elem_type = !llvm.struct<(i64, i64)>, rawConstantIndices = array<i32: 0, 1>}> : (!llvm.ptr) -> !llvm.ptr
    %3 = "llvm.load"(%2) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1, %3) : (i64, i64) -> ()
} with @half := half

-- a noncomputable lift, and a function binding it, likewise noncomputable
noncomputable mlir_const_def seven := {
    %0 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "llvm.return"(%0) : (i64) -> ()
}

noncomputable mlir_def readSeven := {
    %0 = "llvm.mlir.addressof"() <{global_name = @seven}> : () -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1) : (i64) -> ()
} with @seven := seven

example : seven.lit = 7 := rfl

end

/-! ## Execution tests -/

section Tests

/-- The region of `pairs`. -/
private def pairs.region : MLIR.Region := mlir_region% {
    %0 = "llvm.mlir.constant"() <{value = dense<[1, 2]> : tensor<2xi64>}> : () -> !llvm.array<2 x i64>
    %1 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %2 = "llvm.mlir.undef"() : () -> !llvm.struct<(i64, array<2 x i64>)>
    %3 = "llvm.insertvalue"(%2, %1) <{position = array<i64: 0>}> : (!llvm.struct<(i64, array<2 x i64>)>, i64) -> !llvm.struct<(i64, array<2 x i64>)>
    %4 = "llvm.insertvalue"(%3, %0) <{position = array<i64: 1>}> : (!llvm.struct<(i64, array<2 x i64>)>, !llvm.array<2 x i64>) -> !llvm.struct<(i64, array<2 x i64>)>
    %5 = "llvm.mlir.undef"() : () -> !llvm.array<2 x struct<(i64, array<2 x i64>)>>
    %6 = "llvm.insertvalue"(%5, %4) <{position = array<i64: 0>}> : (!llvm.array<2 x struct<(i64, array<2 x i64>)>>, !llvm.struct<(i64, array<2 x i64>)>) -> !llvm.array<2 x struct<(i64, array<2 x i64>)>>
    %7 = "llvm.insertvalue"(%6, %4) <{position = array<i64: 1>}> : (!llvm.array<2 x struct<(i64, array<2 x i64>)>>, !llvm.struct<(i64, array<2 x i64>)>) -> !llvm.array<2 x struct<(i64, array<2 x i64>)>>
    %8 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %9 = "llvm.insertvalue"(%7, %8) <{position = array<i64: 1, 1, 0>}> : (!llvm.array<2 x struct<(i64, array<2 x i64>)>>, i64) -> !llvm.array<2 x struct<(i64, array<2 x i64>)>>
    "llvm.return"(%9) : (!llvm.array<2 x struct<(i64, array<2 x i64>)>>) -> ()
}

/-- What `f` returns from no arguments, if it returns one `t`. -/
private def ret (f : Func) (t : Ty) : Option ⟦t⟧ :=
  if h : f.Γ.args = [] ∧ f.tRets = [t] then
    match f.eval 1 (h.1 ▸ .nil) ⟨default, default⟩ with
    | .value (some vs, _) => match h.2 ▸ vs with | .cons v .nil => some v
    | _ => none
  else none

-- the unfolded region, run instruction by instruction, returns the literal
#guard match translate pairs.region with
  | .ok f => ret f pairs.t == some (Ty.wrap pairs.lit)
  | .error _ => false

-- the folded constant's `value` is the literal
#guard match (Prog.ofRegion pairs.region).toOption.bind Prog.constant? with
  | some (c, []) => if h : c.ty = pairs.t then (h ▸ c.value : ⟦pairs.t⟧ᵣ) == pairs.lit else false
  | some _ => false
  | none => false

/-- What `readPairs` returns from an empty state, or `none` for UB. -/
private def out : Option (BitVec 64) :=
  match readPairs.eval 1 readPairs.args ⟨⟨0⟩, ⟨∅⟩⟩ with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none

#guard out == some 9#64

-- the undefined field's bytes are undefined: its load is poison, the other field's not
#guard (match readHalf.eval 1 readHalf.args ⟨⟨0⟩, ⟨∅⟩⟩ with
  | .value (some (.cons a (.cons b .nil)), _) => some (a, b)
  | _ => none) == some (.value 7, .poison)

end Tests

end MLIR.Tests.Syntax.GlobalFold
