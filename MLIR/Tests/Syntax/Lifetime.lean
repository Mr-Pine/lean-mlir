module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func
meta import MLIR.Syntax.Translate

/-! # Lifetime markers, `assume` and undefined bytes, through `mlir_def` and the steps -/

namespace MLIR.Tests.Syntax.Lifetime

@[expose] public section

/-- A slot with lifetime markers, as newer LLVM writes them: stored, loaded, ended. -/
mlir_def slotted := {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) : (!llvm.ptr) -> ()
    "llvm.store"(%arg0, %1) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.intr.lifetime.end"(%1) : (!llvm.ptr) -> ()
    "llvm.return"(%2) : (i64) -> ()
}

-- the `alloca` a `lifetime.start` marks starts dead
example :
    slotted.entry.body[1]? = some (.alloca (rir_dst% slotted.hty 1) 8 true) := rfl

/-- A slot without lifetime markers, loaded before any store. -/
mlir_def uninit := {
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%2) : (i64) -> ()
}

example : uninit.entry.body[1]? = some (.alloca (rir_dst% uninit.hty 1) 8) := rfl

/-- A slot loaded after its lifetime ends. -/
mlir_def loadAfterEnd := {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) : (!llvm.ptr) -> ()
    "llvm.store"(%arg0, %1) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%1) : (!llvm.ptr) -> ()
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%2) : (i64) -> ()
}

/-- A slot stored to after its lifetime ends. -/
mlir_def storeAfterEnd := {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%1) : (!llvm.ptr) -> ()
    "llvm.store"(%arg0, %1) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (i64) -> ()
}

/-- `assume (x == y)`, the scope declaration translated to nothing. -/
mlir_def assumeEq := {
  ^bb0(%arg0: i64, %arg1: i64):
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    %0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.intr.assume"(%0) <{op_bundle_sizes = array<i32>}> : (i1) -> ()
    "llvm.return"(%arg0) : (i64) -> ()
}

example : assumeEq.entry.body.length = 2 := rfl

end

/-! ## Execution tests -/

section Tests

/-- What `f` returns from one `i64` argument, or `none` for UB. -/
private def ret1 (f : Func) (x : BitVec 64) : Option ⟦Ty.bv 64⟧ :=
  if h : f.Γ.args = [.bv 64] ∧ f.tRets = [.bv 64] then
    match f.eval 1 (h.1 ▸ .cons (.value x) .nil) ⟨⟨1⟩, ⟨∅⟩⟩ with
    | .value (some vs, _) => match h.2 ▸ vs with | .cons v .nil => some v
    | _ => none
  else none

#guard ret1 slotted 7 == some (.value 7)

-- loads of a slot never stored to, or past its lifetime, are poison; a store past it is UB
#guard (match uninit.eval 1 .nil ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => some v
  | _ => none) == some .poison

#guard ret1 loadAfterEnd 7 == some .poison

#guard ret1 storeAfterEnd 7 == none

/-- `assumeEq` of `x` and `y`, or `none` for UB. -/
private def assumed (x y : BitVec 64) : Option ⟦Ty.bv 64⟧ :=
  match assumeEq.eval 1 (assumeEq.args (.value x) (.value y)) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

#guard assumed 3 3 == some (.value 3)

#guard assumed 3 4 == none

end Tests

/-! ## Steps -/

section Steps

-- the lifetime markers by `step_pure`: the slot has room once started, its stored bits are known
example (x : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    slotted.call (slotted.args (.value x)) s =
      .value (.cons (.value x) .nil, { s with alloc := ⟨s.alloc.nextFreeBlock + 1⟩ }) := by
  func_init
  block_init
  step_pure
  step_alloca
  guard_hyp hv1_bounds : InBounds S.mem v1 64
  step_pure
  guard_hyp hroom_v1 : Room S.mem v1 64
  step_store
  step_load with v
  step_lifetime
  finish_block
  subst hS
  erase_frame
  rfl

-- an `assume` whose condition the facts decide
example (x y : BitVec 64) (s : GlobalState) (hwf : s.WF) (h : x = y) :
    assumeEq.call (assumeEq.args (.value x) (.value y)) s = .value (.cons (.value x) .nil, s) := by
  func_init
  block_init
  step_pure
  step_assume [h]
  finish_block
  subst_vars
  rfl

end Steps

end MLIR.Tests.Syntax.Lifetime
