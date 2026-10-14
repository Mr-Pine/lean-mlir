module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic

/-! # Fresh facts, premise searches and lifetime markers in the steps -/

namespace MLIR.Tests.Syntax.Fresh

@[expose] public section

/-! ## A callee's several writes -/

mlir_def put2 :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    "llvm.store"(%arg2, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%arg2, %arg1) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

theorem put2.call_eq (p q : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF)
    (hp : Room s.mem p 64) (hq : Room s.mem q 64) :
    put2.call (put2.args (.value p) (.value q) (.value x)) s =
      .value (.nil, { s with mem := (s.mem.storeAt p x).storeAt q x }) := by
  func_init
  block_init
  step_store
  step_store
  finish_block
  rw [hS]

mlir_def callPut2 :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    "llvm.call"(%arg0, %arg1, %arg2) <{callee = @put2}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
} with @put2 := put2

-- each write's known bits, the first's carried past the second
example (p q : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Room s.mem p 64)
    (hq : Room s.mem q 64) :
    callPut2.call (callPut2.args (.value p) (.value q) (.value x)) s =
      .value (.nil, { s with mem := (s.mem.storeAt p x).storeAt q x }) := by
  func_init
  block_init
  step_call using put2.call_eq
  guard_hyp hfits_p : Fits S.mem p 64
  guard_hyp hfits_q : Fits S.mem q 64
  finish_block
  rw [hS]

/-- `put2`'s writes, as one. -/
abbrev storeTwo (m : MemoryState) (p q : Pointer) (x : BitVec 64) : MemoryState :=
  (m.storeAt p x).storeAt q x

theorem put2.call_eq' (p q : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF)
    (hp : Room s.mem p 64) (hq : Room s.mem q 64) :
    put2.call (put2.args (.value p) (.value q) (.value x)) s =
      .value (.nil, { s with mem := storeTwo s.mem p q x }) :=
  put2.call_eq p q x s hwf hp hq

-- the same through an abbreviation of the writes: the facts about it as spelled, its reads
example (p q : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Room s.mem p 64)
    (hq : Room s.mem q 64) :
    callPut2.call (callPut2.args (.value p) (.value q) (.value x)) s =
      .value (.nil, { s with mem := storeTwo s.mem p q x }) := by
  func_init
  block_init
  step_call using put2.call_eq'
  guard_hyp hfits_p : Fits S.mem p 64
  guard_hyp hfits_q : Fits S.mem q 64
  guard_hyp hread_q : S.mem.readAt q 64 = x
  finish_block
  rw [hS]

/-! ## Object facts -/

/-- Room for a word at `p`. -/
def WordRoom (m : MemoryState) (p : Pointer) : Prop :=
  Room m p 64

/-- A known word at `p`. -/
def WordFit (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p 64

/-- A word stored at `p`. -/
def putWord (m : MemoryState) (p : Pointer) (x : BitVec 64) : MemoryState :=
  m.storeAt p x

theorem WordRoom.put (h : WordRoom m p) : WordRoom (putWord m q y) p :=
  Room.storeAt h

theorem WordFit.put (h : WordFit m p) : WordFit (putWord m q y) p :=
  Fits.storeAt h

theorem WordFit.put_self (h : WordRoom m p) : WordFit (putWord m p x) p :=
  Fits.storeAt_self h

theorem GlobalState.WF.putWord_mk {a : AllocState} {m : MemoryState}
    (h : (⟨a, m⟩ : GlobalState).WF) : (⟨a, putWord m p x⟩ : GlobalState).WF :=
  GlobalState.WF.storeAt_mk h

@[simp]
theorem GlobalState.WF_putWord {s : GlobalState} :
    ({ s with mem := putWord m p x } : GlobalState).WF ↔ ({ s with mem := m } : GlobalState).WF :=
  GlobalState.WF_storeAt

attribute [local mlir_mem] GlobalState.WF_putWord

attribute [local mlir_transport] WordRoom.put WordFit.put GlobalState.WF.putWord_mk

attribute [local mlir_fresh] WordFit.put_self

mlir_def put6 :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: !llvm.ptr,
      %arg5: !llvm.ptr, %arg6: i64):
    "llvm.store"(%arg6, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%arg6, %arg1) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%arg6, %arg2) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%arg6, %arg3) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%arg6, %arg4) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%arg6, %arg5) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

/-- `put6` stores a word at each pointer: a callee's six outputs. -/
theorem put6.call_eq (p0 p1 p2 p3 p4 p5 : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF)
    (h0 : WordRoom s.mem p0) (h1 : WordRoom s.mem p1) (h2 : WordRoom s.mem p2)
    (h3 : WordRoom s.mem p3) (h4 : WordRoom s.mem p4) (h5 : WordRoom s.mem p5) :
    put6.call
        (put6.args (.value p0) (.value p1) (.value p2) (.value p3) (.value p4) (.value p5)
          (.value x)) s =
      .value
        (.nil,
          { s with
            mem :=
              putWord
                (putWord (putWord (putWord (putWord (putWord s.mem p0 x) p1 x) p2 x) p3 x)
                  p4 x)
                p5 x }) := by
  unfold WordRoom at h0 h1 h2 h3 h4 h5
  func_init
  block_init
  iterate 6 step_store
  finish_block
  subst hS
  rfl

mlir_def callPut6 :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: !llvm.ptr,
      %arg5: !llvm.ptr, %arg6: i64):
    "llvm.call"(%arg0, %arg1, %arg2, %arg3, %arg4, %arg5, %arg6) <{callee = @put6}> :
      (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
} with @put6 := put6

-- six object writes: each word known, its fact named as its room, which stays shadowed (known bits
-- need not be writable); the premise of the outermost's fresh lemma is five transports deep
example (p0 p1 p2 p3 p4 p5 : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF)
    (hp0 : WordRoom s.mem p0) (hp1 : WordRoom s.mem p1) (hp2 : WordRoom s.mem p2)
    (hp3 : WordRoom s.mem p3) (hp4 : WordRoom s.mem p4) (hp5 : WordRoom s.mem p5) :
    callPut6.call
        (callPut6.args (.value p0) (.value p1) (.value p2) (.value p3) (.value p4) (.value p5)
          (.value x)) s =
      .value
        (.nil,
          { s with
            mem :=
              putWord
                (putWord (putWord (putWord (putWord (putWord s.mem p0 x) p1 x) p2 x) p3 x)
                  p4 x)
                p5 x }) := by
  func_init
  block_init
  step_call using put6.call_eq
  guard_hyp hp0 : WordFit S.mem p0
  guard_hyp hp5 : WordFit S.mem p5
  have : WordRoom S.mem p0 := by assumption
  finish_block
  rw [hS]

-- a consumed room: the fresh fact stays
example (p0 p1 p2 p3 p4 p5 : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF)
    (hp0 : WordRoom s.mem p0) (hp1 : WordRoom s.mem p1) (hp2 : WordRoom s.mem p2)
    (hp3 : WordRoom s.mem p3) (hp4 : WordRoom s.mem p4) (hp5 : WordRoom s.mem p5) :
    callPut6.call
        (callPut6.args (.value p0) (.value p1) (.value p2) (.value p3) (.value p4) (.value p5)
          (.value x)) s =
      .value
        (.nil,
          { s with
            mem :=
              putWord
                (putWord (putWord (putWord (putWord (putWord s.mem p0 x) p1 x) p2 x) p3 x)
                  p4 x)
                p5 x }) := by
  func_init
  block_init
  step_call using put6.call_eq consuming hp0
  guard_hyp hp0 : WordFit S.mem p0
  fail_if_success have : WordRoom S.mem p0 := by assumption
  finish_block
  rw [hS]

/-! ## Ranges inside a store, at a variable offset -/

-- a lane of a stored array, from room for the array
example (m : MemoryState) (p : Pointer) (x : BitVec 4096) (j : Nat) (h : Room m p 4096)
    (hso : ¬p.offset.uaddOverflow 512#64) (hj : j < 256) :
    Fits (m.storeAt p x) (p.add (BitVec.ofNat 64 (2 * j))) 16 := by
  mem_fact

-- room for a lane, from room for the array
example (m : MemoryState) (p : Pointer) (j : Nat) (h : Room m p 4096)
    (hso : ¬p.offset.uaddOverflow 512#64) (hj : j < 256) :
    Room m (p.add (BitVec.ofNat 64 (2 * j))) 16 := by
  mem_fact

-- a word of a known array at a variable offset, the array's start known
example (m : MemoryState) (v : Pointer) (hf : Fits m v 320) (hv : v.offset = 0) (w : Nat)
    (hw : w < 5) : Fits m (v.add (BitVec.ofNat 64 (8 * w))) 64 := by
  mem_fact

-- a stored array's start
example (m : MemoryState) (p : Pointer) (x : BitVec 4096) (h : Room m p 4096) :
    Fits (m.storeAt p x) p 64 := by
  mem_fact

-- overlaying what a range holds changes nothing
example (m : MemoryState) (p : Pointer) (h : InBounds m p 64) :
    m.overlay p (m.readAt p 64) (m.definedAt p 64) = m :=
  MemoryState.overlay_readAt_definedAt h

/-! ## Copies of partly defined objects -/

mlir_def copy16 :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    "llvm.intr.memcpy"(%arg0, %arg1, %0) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %1 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1) : (i64) -> ()
}

-- a source known only in its first word: the copy's definedness and pointers, its first word
-- known and read
example (p q : Pointer) (s : GlobalState) (hwf : s.WF) (hp : Room s.mem p 128)
    (hq : Room s.mem q 128) (hq8 : Fits s.mem q 64) (hpq : p.id ≠ q.id) :
    copy16.call (copy16.args (.value p) (.value q)) s =
      .value
        (.cons (.value ((s.mem.readAt q 128).setWidth 64)) .nil,
          { s with
            mem :=
              s.mem.storeCopy p (s.mem.readAt q 128) (s.mem.definedAt q 128)
                (s.mem.ptrsIn q 128) }) := by
  func_init
  block_init
  step_pure
  step_memcpy
  guard_hyp hfits_p : Fits S.mem p 64
  step_load with v
  finish_block
  rw [hS, hv]

-- a source whose definedness leaves no 64-bit window undefined: no pointer to copy, a `storeDef`
example (p q : Pointer) (s : GlobalState) (hwf : s.WF) (hp : Room s.mem p 128)
    (hq : Room s.mem q 128) (hq8 : Fits s.mem q 64) (hpq : p.id ≠ q.id)
    (hd : s.mem.definedAt q 128 = 0xffffffffffffffffff#128) :
    copy16.call (copy16.args (.value p) (.value q)) s =
      .value
        (.cons (.value ((s.mem.readAt q 128).setWidth 64)) .nil,
          { s with mem := s.mem.storeDef p (s.mem.readAt q 128) (s.mem.definedAt q 128) }) := by
  func_init
  block_init
  step_pure
  step_memcpy
  step_load with v
  finish_block
  rw [hS, hv]

-- a source with no stored pointer over it (`PtrFree`): none to copy, a `storeDef`
example (p q : Pointer) (s : GlobalState) (hwf : s.WF) (hp : Room s.mem p 128)
    (hq : Room s.mem q 128) (hq8 : Fits s.mem q 64) (hpq : p.id ≠ q.id)
    (hpf : PtrFree s.mem q 128) :
    copy16.call (copy16.args (.value p) (.value q)) s =
      .value
        (.cons (.value ((s.mem.readAt q 128).setWidth 64)) .nil,
          { s with mem := s.mem.storeDef p (s.mem.readAt q 128) (s.mem.definedAt q 128) }) := by
  func_init
  block_init
  step_pure
  step_memcpy
  step_load with v
  finish_block
  rw [hS, hv]

-- bits stored leave no pointer over them; a fresh block has none
example (m : MemoryState) (p : Pointer) (x : BitVec 128) (h : Room m p 128) (ho : p.offset = 0) :
    PtrFree (m.storeAt p x) (p.add 8#64) 64 := by
  mem_fact

example (s : GlobalState) (x : BitVec 64) :
    PtrFree ((s.alloca 16).mem.storeAt (s.allocaPtr.add 8#64) x) s.allocaPtr 128 := by
  mem_fact

-- a word inside a copy: known from the source's, read as the source's
example (m : MemoryState) (p q : Pointer) (hp : Room m p 128) (hq : InBounds m q 128)
    (hpo : p.offset = 0) (hqo : q.offset = 0) :
    (m.storeDef p (m.readAt q 128) (m.definedAt q 128)).readAt (p.add 8#64) 64 =
      m.readAt (q.add 8#64) 64 :=
  MemoryState.readAt_storeDef_readAt_add hp hq (by rw [hpo]; decide) (by rw [hqo]; decide)
    (by decide) _

-- the same for a word inside: from the source's
example (m : MemoryState) (p q : Pointer) (hp : Room m p 128) (hq : Fits m (q.add 8#64) 64)
    (hpo : p.offset = 0) (hqo : q.offset = 0) :
    Fits (m.storeDef p (m.readAt q 128) (m.definedAt q 128)) (p.add 8#64) 64 := by
  mem_fact

/-! ## Globals with undefined members -/

/-- A pair whose second word is undefined. -/
mlir_const_def half := {
    %0 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %1 = "llvm.mlir.undef"() : () -> !llvm.struct<(i64, i64)>
    %2 = "llvm.insertvalue"(%1, %0) <{position = array<i64: 0>}> : (!llvm.struct<(i64, i64)>, i64) -> !llvm.struct<(i64, i64)>
    "llvm.return"(%2) : (!llvm.struct<(i64, i64)>) -> ()
}

theorem half.value_eq (s : GlobalState) : half.value s = .value ((.value 7, .poison), s) :=
  GlobalInitializer.compute_value _ _ ⟨_, by with_unfolding_all rfl⟩

mlir_def readHalf := {
    %0 = "llvm.mlir.addressof"() <{global_name = @half}> : () -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1) : (i64) -> ()
} with @half := half

-- the block is live, its defined word is known and read back
example (s : GlobalState) (hwf : s.WF) (hgl : s.mem.Globals readHalf.globals) :
    readHalf.call readHalf.args s = .value (.cons (.value 7#64) .nil, s) := by
  func_init
  block_init
  step_addressof half.value_eq with g
  fail_if_success have := b
  guard_hyp hg_live : Live S.mem g 128
  guard_hyp hg_fits : Fits S.mem g 64
  step_load with v
  finish_block
  subst hS
  subst hv
  rfl

theorem readHalf.call_eq (s : GlobalState) (hwf : s.WF) (hgl : s.mem.Globals readHalf.globals) :
    readHalf.call readHalf.args s = .value (.cons (.value 7#64) .nil, s) := by
  func_init
  block_init
  step_addressof with g
  step_load with v
  finish_block
  subst hS hv
  rfl

mlir_def callReadHalf := {
    %0 = "llvm.call"() <{callee = @readHalf}> : () -> i64
    "llvm.return"(%0) : (i64) -> ()
} with @readHalf := readHalf

-- a callee's globals, from the caller's
example (s : GlobalState) (hwf : s.WF) (hgl : s.mem.Globals callReadHalf.globals) :
    callReadHalf.call callReadHalf.args s = .value (.cons (.value 7#64) .nil, s) := by
  func_init
  block_init
  step_call using readHalf.call_eq
  finish_block
  rw [hS]

mlir_def readHalf2 := {
    %0 = "llvm.mlir.addressof"() <{global_name = @half}> : () -> !llvm.ptr
    %1 = "llvm.mlir.addressof"() <{global_name = @half}> : () -> !llvm.ptr
    %2 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %3 = "llvm.alloca"(%2) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %4 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %5 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %6 = "llvm.add"(%4, %5) : (i64, i64) -> i64
    "llvm.return"(%6) : (i64) -> ()
} with @half := half

-- the global twice, then a slot: the first's facts carried, no goals
example (s : GlobalState) (hwf : s.WF) (hgl : s.mem.Globals readHalf2.globals) :
    readHalf2.call readHalf2.args s =
      .value (.cons (.value 14#64) .nil, { s with alloc := ⟨s.alloc.nextFreeBlock + 1⟩ }) := by
  func_init
  block_init
  step_addressof half.value_eq with g
  step_addressof half.value_eq with g'
  guard_hyp hg_fits : Fits S.mem g 64
  step_pure
  step_alloca with t
  step_load with v
  step_load with v'
  step_pure
  finish_block
  subst hS
  erase_frame
  subst_vars
  rfl

-- the same with its value read off its block
example (s : GlobalState) (hwf : s.WF) (hgl : s.mem.Globals readHalf.globals) :
    readHalf.call readHalf.args s = .value (.cons (.value 7#64) .nil, s) := by
  func_init
  block_init
  step_addressof with g
  step_load with v
  finish_block
  subst hS
  subst hv
  rfl

/-- An array, then an undefined word. -/
mlir_const_def arrHalf := {
    %0 = "llvm.mlir.constant"() <{value = dense<[1, 2]> : tensor<2xi64>}> : () -> !llvm.array<2 x i64>
    %1 = "llvm.mlir.undef"() : () -> !llvm.struct<(array<2 x i64>, i64)>
    %2 = "llvm.insertvalue"(%1, %0) <{position = array<i64: 0>}> : (!llvm.struct<(array<2 x i64>, i64)>, !llvm.array<2 x i64>) -> !llvm.struct<(array<2 x i64>, i64)>
    "llvm.return"(%2) : (!llvm.struct<(array<2 x i64>, i64)>) -> ()
}

theorem arrHalf.value_eq (s : GlobalState) :
    arrHalf.value s = .value ((#v[.value 1, .value 2], .poison), s) :=
  GlobalInitializer.compute_value _ _ ⟨_, by with_unfolding_all rfl⟩

mlir_def readArrHalf := {
    %0 = "llvm.mlir.addressof"() <{global_name = @arrHalf}> : () -> !llvm.ptr
    %1 = "llvm.getelementptr"(%0) <{elem_type = i8, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%2) : (i64) -> ()
} with @arrHalf := arrHalf

-- an array member: its words known, read inside the block
example (s : GlobalState) (hwf : s.WF) (hgl : s.mem.Globals readArrHalf.globals) :
    readArrHalf.call readArrHalf.args s = .value (.cons (.value 2#64) .nil, s) := by
  func_init
  block_init
  step_addressof arrHalf.value_eq with g
  guard_hyp hg_fits : Fits S.mem g 128
  step_pure
  step_load with v
  finish_block
  subst hS
  subst hv
  rfl

/-! ## Distinct blocks by their order -/

-- through a bound between them
example (r z : Pointer) (b : Nat) (hrb : r.id.id < b) (hb : b ≤ z.id.id) : r.id ≠ z.id := by
  mem_fact

-- a slot above a pointer's bound
example (p : Pointer) (B : GlobalState) (h : p.id.id < B.alloc.nextFreeBlock + 3) :
    p.id ≠ (B.slot 200).id := by
  mem_fact

-- a named slot above a pointer's bound
example (p x : Pointer) (s : GlobalState) (hp : p.id.id < s.alloc.nextFreeBlock)
    (hx : x = s.slot 1) : x.id ≠ (p.add 8#64).id := by
  mem_fact

-- a pointer into a `WF` state's memory is below its counter
example (r : Pointer) (s : GlobalState) (hwf : s.WF) (hr : Room s.mem r 64) :
    r.id.id < s.alloc.nextFreeBlock := by
  mem_fact

/-! ## Arithmetic premises of transports -/

/-- `n` bits of `m` are tracked. -/
def Tracked (_m : MemoryState) (_n : Nat) : Prop :=
  True

theorem Tracked.storeAt (h : Tracked m n) (_hn : n ≤ 64) : Tracked (m.storeAt p x) n :=
  h

attribute [local mlir_transport] Tracked.storeAt

mlir_def put :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    "llvm.store"(%arg1, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

-- a literal bound in a transport premise
example (p : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Room s.mem p 64)
    (ht : Tracked s.mem 41) :
    put.call (put.args (.value p) (.value x)) s =
      .value (.nil, { s with mem := s.mem.storeAt p x }) := by
  func_init
  block_init
  step_store
  guard_hyp ht : Tracked S.mem 41
  finish_block
  rw [hS]

/-! ## Lifetime markers -/

mlir_def twoSlots :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %2 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) : (!llvm.ptr) -> ()
    "llvm.store"(%arg1, %1) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%2) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%1) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%2) : (!llvm.ptr) -> ()
    %3 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%3) : (i64) -> ()
}

/-- `q` holds `y`. -/
def Holds (m : MemoryState) (q : Pointer) (y : BitVec 64) : Prop :=
  m.readAt q 64 = y

-- the argument's facts carried past the markers; the ended slot's dropped, as is a fact no lemma
-- carries past a marker
example (p : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 64) :
    twoSlots.call (twoSlots.args (.value p) (.value x)) s =
      .value
        (.cons (.value (s.mem.readAt p 64)) .nil,
          { s with alloc := ⟨s.alloc.nextFreeBlock + 2⟩ }) := by
  func_init
  block_init
  step_pure
  step_alloca
  step_alloca
  step_pure
  step_store
  have hh : Holds S.mem p (S.mem.readAt p 64) := rfl
  step_pure
  step_pure
  fail_if_success have : Fits S.mem v1 64 := by assumption
  fail_if_success have : Holds S.mem p (S.mem.readAt p 64) := by assumption
  guard_hyp hp : Fits S.mem p 64
  step_pure
  step_load with v
  finish_block
  subst hS
  erase_frame
  subst hv
  rfl

mlir_def lateStart :=
{
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.br"()[^bb1] : () -> ()
  ^bb1:
    "llvm.intr.lifetime.start"(%1) : (!llvm.ptr) -> ()
    "llvm.return"(%arg0) : (i64) -> ()
}

-- a marker on a register the env does not hold
/--
error: lifetime marker: its pointer operand is not known to be a value or poison
  E.read (%1)
a register the env does not hold?
-/
#guard_msgs (error, drop info) in
example (E : ⟪lateStart.Γ⟫) (S : GlobalState) (x : BitVec 64)
    (hArgs : E.args = (lateStart.args (.value x)).get) :
    lateStart.runFrom E ^bb1 S = .value (.cons (.value x) .nil, S) := by
  block_init
  step_pure
  finish_block
  rfl

/-! ## Loop lemmas' register premises -/

mlir_def jumpVal :=
{
  ^bb0(%arg0: i64):
    %0 = "llvm.add"(%arg0, %arg0) : (i64, i64) -> i64
    "llvm.br"()[^bb1] : () -> ()
  ^bb1:
    "llvm.return"(%0) : (i64) -> ()
}

/-- `^bb1`'s register. -/
abbrev Regs (E : ⟪jumpVal.Γ⟫) (x : BitVec 64) : Prop :=
  E ⊨ [%0 := x + x]

theorem jumpVal.at1 (x : BitVec 64) (E : ⟪jumpVal.Γ⟫) (S : GlobalState) (hR : Regs E x) :
    jumpVal.runFrom E ^bb1 S = .value (.cons (.value (x + x)) .nil, S) := by
  block_init
  finish_block
  rw [hR]

-- a premise abbreviating the env's reads: closed through the env
example (x : BitVec 64) (E : ⟪jumpVal.Γ⟫) (S : GlobalState)
    (hArgs : E.args = (jumpVal.args (.value x)).get) :
    jumpVal.runFrom E ^bb0 S = .value (.cons (.value (x + x)) .nil, S) := by
  block_init
  step_pure
  finish_block
  step_loop using jumpVal.at1 x

end

end MLIR.Tests.Syntax.Fresh
