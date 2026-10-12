module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic

/-! # Step tactic regressions on small functions -/

namespace MLIR.Tests.Syntax.Steps

@[expose] public section

mlir_def twice :=
  {^bb0(%arg0:i32):%0 = "llvm.add"(%arg0, %arg0):(i32, i32)->i32"llvm.return"(%0):(i32)->()}

-- an argument read before the env is first sealed: by the args fact of the chain's root
example (E : ⟪twice.Γ⟫) (S : GlobalState) (x : BitVec 32)
    (hArgs : E.args = (twice.args (.value x)).get) :
    twice.runFrom (E[%0 := .value 0#32]) 0 S = .value (.cons (.value (x + x)) .nil, S) := by
  block_init
  step_pure
  -- the write it overwrites is dead
  guard_hyp hE :~ E = E₀[%0 := .value (x + x)]
  finish_block
  rfl

mlir_def put :=
  {^bb0(%arg0:!llvm.ptr,
      %arg1:i64):"llvm.store"(%arg1, %arg0)<{alignment = 8:i64, ordering = 0:i64}>:(i64,
        !llvm.ptr)->()"llvm.return"():()->()}

-- a consumed fact the store's state cannot carry (`hm`) is no goal
example (p : Pointer) (x : BitVec 64) (s : GlobalState) (m : MemoryState) (hwf : s.WF)
    (hp : Fits s.mem p 64) (hm : m = s.mem) :
    put.call (put.args (.value p) (.value x)) s =
      .value (.nil, { s with mem := s.mem.storeAt p x }) := by
  func_init
  block_init
  step_store consuming hm
  finish_block
  rw [hS]

-- an equation about the state that the store cannot carry stays about the state before it
example (p : Pointer) (x : BitVec 64) (b : Nat) (s : GlobalState) (hwf : s.WF)
    (hp : Fits s.mem p 64) :
    put.call (put.args (.value p) (.value x)) s =
      .value (.nil, { s with mem := s.mem.storeAt p x }) := by
  func_init
  block_init
  have hm : S.mem.eraseFrom b = S₀.mem.eraseFrom b := by rw [hS]
  step_store
  guard_hyp hm : S₀.mem.eraseFrom b = S₀.mem.eraseFrom b
  finish_block
  rw [hS]

-- an output needs only `Room`
example (p : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Room s.mem p 64) :
    put.call (put.args (.value p) (.value x)) s =
      .value (.nil, { s with mem := s.mem.storeAt p x }) := by
  func_init
  block_init
  step_store
  finish_block
  rw [hS]

mlir_def putGet :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    "llvm.store"(%arg1, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %0 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

-- a store into `Room` makes its bits known: the load after it reads them back
example (p : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Room s.mem p 64) :
    putGet.call (putGet.args (.value p) (.value x)) s =
      .value (.cons (.value x) .nil, { s with mem := s.mem.storeAt p x }) := by
  func_init
  block_init
  step_store
  guard_hyp hfits_p : Fits S.mem p 64
  step_load
  finish_block
  rw [hS]

mlir_def stackSlot :=
{
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%arg0, %1) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%2) : (i64) -> ()
}

-- a fresh slot has `Room`, not `Fits`: it is undefined until stored to
example (x : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    stackSlot.call (stackSlot.args (.value x)) s =
      .value (.cons (.value x) .nil, { s with alloc := ⟨s.alloc.nextFreeBlock + 1⟩ }) := by
  func_init
  block_init
  step_pure
  step_alloca
  guard_hyp hv1_room : Room S.mem v1 64
  step_store
  step_load with v
  finish_block
  subst hS
  erase_frame
  rfl

mlir_def copy :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.store"(%0, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

theorem copy.call_eq (r a : Pointer) (s : GlobalState) (hwf : s.WF) (hr : Fits s.mem r 64)
    (ha : Fits s.mem a 64) :
    copy.call (copy.args (.value r) (.value a)) s =
      .value (.nil, { s with mem := s.mem.storeAt r (s.mem.readAt a 64) }) := by
  func_init
  block_init
  step_load
  step_store
  finish_block
  subst_vars
  rfl

mlir_def copyTwice :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    "llvm.call"(%arg0, %arg1) <{callee = @copy}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%arg2, %arg0) <{callee = @copy}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
} with @copy := copy

-- a call's stored value that is a read with a fact is read back: the second call reads `x`
example (r a q : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hr : Fits s.mem r 64)
    (ha : Fits s.mem a 64) (hq : Fits s.mem q 64)
    (hx : s.mem.readAt a 64 = x) :
    copyTwice.call (copyTwice.args (.value r) (.value a) (.value q)) s =
      .value (.nil, { s with mem := (s.mem.storeAt r x).storeAt q x }) := by
  func_init
  block_init
  step_call using copy.call_eq
  guard_hyp hread_r : S.mem.readAt r 64 = x
  step_call using copy.call_eq
  finish_block
  rw [hS]

mlir_def jump :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    "llvm.store"(%arg1, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.br"()[^bb1] : () -> ()
  ^bb1:
    "llvm.return"() : () -> ()
}

/-- The entry block, its exit's env and state given to a continuation. -/
theorem jump.entry (p : Pointer) (x : BitVec 64) (S : GlobalState) (E : ⟪jump.Γ⟫)
    (hArgs : E.args = (jump.args (.value p) (.value x)).get) (hwf : S.WF) (hp : Fits S.mem p 64)
    (K : PoisonOr (Vals [] × GlobalState))
    (hK :
      ∀ (E' : ⟪jump.Γ⟫) (S' : GlobalState), E'.args = (jump.args (.value p) (.value x)).get →
        S' = { S with mem := S.mem.storeAt p x } → jump.runFrom E' ^bb1 S' = K) :
    jump.runFrom E ^bb0 S = K := by
  block_init
  step_store
  finish_block
  step_loop using hK

-- a continuation's state binder keeps its name; the args fact is `hArgs₀`
example (p : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 64) :
    jump.call (jump.args (.value p) (.value x)) s =
      .value (.nil, { s with mem := s.mem.storeAt p x }) := by
  func_init
  step_loop using jump.entry p x
  guard_hyp hArgs₀ : E₀.args = (jump.args (.value p) (.value x)).get
  intro hS'
  block_init
  finish_block
  subst_vars
  rfl

/-- `q` holds `y`. -/
def Holds (m : MemoryState) (q : Pointer) (y : BitVec 64) : Prop :=
  m.readAt q 64 = y

theorem Holds.storeAt {m : MemoryState} {p q : Pointer} {x y : BitVec 64} (h : Holds m q y)
    (hne : p.id ≠ q.id) : Holds (m.storeAt p x) q y :=
  (MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hne) x).trans h

attribute [local mlir_transport] Holds.storeAt

-- a transport lemma's `≠` premise from a `Nodup` fact
example (p q : Pointer) (x y : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 64)
    (hq : Holds s.mem q y) (_hnd : [p.id, q.id].Nodup) :
    put.call (put.args (.value p) (.value x)) s =
      .value (.nil, { s with mem := s.mem.storeAt p x }) := by
  func_init
  block_init
  step_store
  guard_hyp hq : Holds S.mem q y
  finish_block
  rw [hS]

mlir_def put2 :=
  {^bb0(%arg0:!llvm.ptr, %arg1:!llvm.ptr,
      %arg2:i64):"llvm.store"(%arg2, %arg0)<{alignment = 8:i64, ordering = 0:i64}>:(i64,
        !llvm.ptr)->()"llvm.store"(%arg2, %arg1)<{alignment = 8:i64, ordering = 0:i64}>:(i64,
        !llvm.ptr)->()"llvm.return"():()->()}

-- a read fact past a possibly aliasing store is dropped, and traced
/--
trace: [rir] read fact hread_p dropped (a write not known to miss it):
      (S.mem.storeAt q x).readAt p 64
-/
#guard_msgs in
set_option trace.rir true in
example (p q : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 64)
    (hq : Fits s.mem q 64) :
    put2.call (put2.args (.value p) (.value q) (.value x)) s =
      .value (.nil, { s with mem := (s.mem.storeAt p x).storeAt q x }) := by
  func_init
  block_init
  step_store
  step_store
  finish_block
  rw [hS]

/-- Two stores, as one write. -/
def storeBoth (m : MemoryState) (p q : Pointer) (x : BitVec 64) : MemoryState :=
  (m.storeAt p x).storeAt q x

theorem storeAt_storeAt_both {m : MemoryState} {p q : Pointer} {x : BitVec 64} :
    (m.storeAt p x).storeAt q x = storeBoth m p q x :=
  rfl

attribute [local mlir_state] storeAt_storeAt_both

-- an `mlir_state` lemma over two writes merges a store with the one below it in `hS`
example (p q : Pointer) (x : BitVec 64) (s : GlobalState) (E : ⟪put2.Γ⟫) (hwf : s.WF)
    (hp : Fits s.mem p 64) (hq : Fits s.mem q 64)
    (hArgs : E.args = (put2.args (.value p) (.value q) (.value x)).get) :
    put2.runFrom E 0 s = .value (.nil, { s with mem := storeBoth s.mem p q x }) := by
  block_init
  step_store
  step_store
  guard_hyp hS : S = { s with mem := storeBoth s.mem p q x }
  finish_block
  rw [hS]

mlir_def isZero :=
  {^bb0(%arg0:i32):%0 = "llvm.mlir.constant"()<{value =
        0:i32}>:()->i32%1 = "llvm.icmp"(%arg0, %0)<{predicate = 0:i64}>:(i32,
        i32)->i1"llvm.cond_br"(%1)[^bb1, ^bb2]<{operandSegmentSizes =
        array<i32:1, 0,
          0>}>:(i1)->()^bb1:%2 = "llvm.mlir.constant"()<{value =
        1:i32}>:()->i32"llvm.return"(%2):(i32)->()^bb2:"llvm.return"(%0):(i32)->()}

-- a jump decided by a negated fact: one goal
example (x : BitVec 32) (s : GlobalState) (hwf : s.WF) (hx : ¬x = 0#32) :
    isZero.call (isZero.args (.value x)) s = .value (.cons (.value 0#32) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pure
  finish_block
  block_init
  finish_block
  rw [hS]

mlir_def addTwo :=
  {^bb0(%arg0:i32):%0 = "llvm.mlir.constant"()<{value =
        0:i32}>:()->i32%1 = "llvm.mlir.constant"()<{value =
        1:i32}>:()->i32"llvm.br"()[^bb1]:()->()^bb1:%2 = "llvm.add"(%arg0, %0):(i32,
        i32)->i32%3 = "llvm.add"(%2, %1):(i32, i32)->i32"llvm.return"(%3):(i32)->()}

-- a step leaves the env's other values as they are: `v[1]`, not unfolded to `List.get`
example (E : ⟪addTwo.Γ⟫) (S : GlobalState) (x : BitVec 32) (v : Vector (BitVec 32) 2)
    (hArgs : E.args = (addTwo.args (.value x)).get) :
    addTwo.runFrom (E[%1 := .value v[1], %0 := .value v[0]]) 1 S =
      .value (.cons (.value (x + v[0] + v[1])) .nil, S) := by
  block_init
  step_pure
  fail_if_success simp only [List.get_eq_getElem] at hE
  step_pure
  finish_block
  rfl

mlir_def at8 :=
  {^bb0(%arg0:!llvm.ptr,
      %arg1:i64):%0 = "llvm.getelementptr"(%arg0, %arg1)<{elem_type = i64, noWrapFlags = 7 : i32,
        rawConstantIndices = array<i32:-2147483648>}>:(!llvm.ptr, i64)->!llvm.ptr
        "llvm.return"(%0):(!llvm.ptr)->()}

-- a `gep inbounds nuw` by a symbolic index from a block's start (`p.offset = 0`) does not wrap
example (p : Pointer) (i : BitVec 64) (E : ⟪at8.Γ⟫) (S : GlobalState) (hp : p.offset = 0)
    (hi : i.toNat * 8 < 2 ^ 63) (hArgs : E.args = (at8.args (.value p) (.value i)).get) :
    at8.runFrom E 0 S =
      .value (.cons (.value (p.add (BitVec.ofNat 64 (i.toNat * 8)))) .nil, S) := by
  block_init
  step_pure [hi]
  finish_block
  rfl

-- an offset `192 * k` for `k < 8` that does not wrap: `omega` alone misses it through `% 2 ^ 64`
example (p : Pointer) (k : Nat) (hp : p.offset.toNat + 192 * 8 < 2 ^ 64) (hk : k < 8) :
    Operation.gep { nusw := true, nuw := true } (.value (BitVec.ofNat 64 (192 * k))) (.value p) =
      .value (p.add (BitVec.ofNat 64 (192 * k))) := by
  simp only [Tactic.gepValue]

mlir_def deepLoad :=
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %2 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %3 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %4 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %5 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %6 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %7 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%7) : (i64) -> ()
}

-- a load below six `alloca`s: the entry `Fits` carried through each, not searched for
example (p : Pointer) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 64) :
    deepLoad.call (deepLoad.args (.value p)) s =
      .value
        (.cons (.value (s.mem.readAt p 64)) .nil,
          { s with alloc := ⟨s.alloc.nextFreeBlock + 6⟩ }) := by
  func_init
  block_init
  step_pure
  iterate 6 step_alloca
  step_load with v
  guard_hyp hv : v = S₀.mem.readAt p 64
  finish_block
  subst hS
  erase_frame
  rfl

/-- `p` and the word after it fit. -/
abbrev PairFit (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p 64 ∧ Fits m (p.add 8#64) 64

theorem PairFit.alloca {s : GlobalState} (hwf : s.WF) (h : PairFit s.mem p) :
    PairFit (s.alloca n).mem p :=
  ⟨h.1.alloca hwf, h.2.alloca hwf⟩

attribute [local mlir_transport] PairFit.alloca

-- the same with the pointer's `Fits` a conjunct of an object predicate
example (p : Pointer) (s : GlobalState) (hwf : s.WF) (hp : PairFit s.mem p) :
    deepLoad.call (deepLoad.args (.value p)) s =
      .value
        (.cons (.value (s.mem.readAt p 64)) .nil,
          { s with alloc := ⟨s.alloc.nextFreeBlock + 6⟩ }) := by
  func_init
  block_init
  step_pure
  iterate 6 step_alloca
  step_load with v
  guard_hyp hv : v = S₀.mem.readAt p 64
  finish_block
  subst hS
  erase_frame
  rfl

mlir_def back8 :=
  {^bb0(%arg0:!llvm.ptr):%0 = "llvm.getelementptr"(%arg0)<{elem_type = i8, noWrapFlags = 3 : i32,
        rawConstantIndices = array<i32:16>}>:(!llvm.ptr)->!llvm.ptr%1 = "llvm.getelementptr"(%0)<{
        elem_type = i8, noWrapFlags = 3 : i32, rawConstantIndices = array<i32:-8>}>:(!llvm.ptr)
        ->!llvm.ptr"llvm.return"(%1):(!llvm.ptr)->()}

-- constant `gep inbounds`s forward and back, from a block's start
example (p : Pointer) (E : ⟪back8.Γ⟫) (S : GlobalState) (hp : p.offset = 0)
    (hArgs : E.args = (back8.args (.value p)).get) :
    back8.runFrom E 0 S = .value (.cons (.value (p.add 8#64)) .nil, S) := by
  block_init
  step_pure
  step_pure
  finish_block
  rfl

mlir_const_def answer :=
  {%0 = "llvm.mlir.constant"()<{value = 42:i64}>:()->i64"llvm.return"(%0):(i64)->()}

mlir_def frameLoad :=
  {^bb0(%arg0:!llvm.ptr):%0 = "llvm.mlir.constant"()<{value =
        1:i64}>:()->i64%1 = "llvm.mlir.addressof"()<{global_name =
        @answer}>:()->!llvm.ptr%2 = "llvm.alloca"(%0)<{alignment = 8:i64, elem_type =
        i64}>:(i64)->!llvm.ptr%3 = "llvm.load"(%arg0)<{alignment = 8:i64, ordering =
        0:i64}>:(!llvm.ptr)->i64"llvm.return"(%3):(i64)->()} with
  @answer := answer

theorem answer.value_eq (s : GlobalState) : answer.value s = .value (Ty.wrap 42#64, s) :=
  GlobalInitializer.compute_value _ _ ⟨_, by with_unfolding_all rfl⟩

-- a load below a frame's new blocks: by the entry facts about `S₀` that `func_init` keeps
example (p : Pointer) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 64) :
    frameLoad.call (frameLoad.args (.value p)) s =
      .value
        (.cons (.value (s.mem.readAt p 64)) .nil,
          { s with alloc := ⟨s.alloc.nextFreeBlock + 2⟩ }) := by
  func_init
  block_init
  step_pure
  step_addressof answer.value_eq
  step_alloca
  step_load with v
  guard_hyp hv : v = S₀.mem.readAt p 64
  finish_block
  subst hS
  erase_frame
  rfl

mlir_def sbb :=
{
  ^bb0(%arg0: i8, %arg1: i64, %arg2: i64):
    %0 = "llvm.call_intrinsic"(%arg0, %arg1, %arg2) <{fastmathFlags = #llvm.fastmath<none>, intrin = "llvm.x86.subborrow.64", op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i8, i64, i64) -> !llvm.struct<(i8, i64)>
    %1 = "llvm.extractvalue"(%0) <{position = array<i64: 0>}> : (!llvm.struct<(i8, i64)>) -> i8
    %2 = "llvm.extractvalue"(%0) <{position = array<i64: 1>}> : (!llvm.struct<(i8, i64)>) -> i64
    "llvm.return"(%1, %2) : (i8, i64) -> ()
}

-- a `subborrow`'s fields, each by `step_pure`
example (a b : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    sbb.call (sbb.args (.value 1) (.value a) (.value b)) s =
      .value
        (.cons (.value (if a.toNat < b.toNat + 1 then 1 else 0)) (.cons (.value (a - b - 1)) .nil),
          s) := by
  func_init
  block_init
  step_pure
  step_pure with bo
  guard_hyp hbo : bo = if a.toNat < b.toNat + 1 then 1#8 else 0#8
  step_pure with d
  guard_hyp hd : d = a - b - 1#64
  finish_block
  subst_vars
  rfl

mlir_def blendOr :=
{
  ^bb0(%arg0: vector<2xi8>, %arg1: vector<2xi8>, %arg2: vector<2xi8>):
    %0 = "llvm.call_intrinsic"(%arg0, %arg1, %arg2) <{fastmathFlags = #llvm.fastmath<none>, intrin = "llvm.x86.avx2.pblendvb", op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (vector<2xi8>, vector<2xi8>, vector<2xi8>) -> vector<2xi8>
    %1 = "llvm.intr.vector.reduce.or"(%0) : (vector<2xi8>) -> i8
    "llvm.return"(%1) : (i8) -> ()
}

-- `pblendvb` and `vector.reduce.or` to their lanes
example (x y : Vector (BitVec 8) 2) (s : GlobalState) (hwf : s.WF) :
    blendOr.call
        (blendOr.args (Ty.wrap (t := .vec 2 8) x) (Ty.wrap (t := .vec 2 8) y)
          (Ty.wrap (t := .vec 2 8) #v[0x80, 0])) s =
      .value (.cons (.value (y[0] ||| x[1])) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pure with r
  guard_hyp hr : r = (if (0x80#8).msb = true then y[0] else x[0]) ||| x[1]
  finish_block
  subst_vars
  rfl

end

end MLIR.Tests.Syntax.Steps
