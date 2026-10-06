/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.GlobalsProof
import SSA.Projects.Agave.LatticeHash.MLIR.OutputRead
import SSA.Projects.Agave.LatticeHash.PhysicalStaging

/-! Byte-backed caller memory for full-width compiled batch invocations.
The retained bytes are copied exactly, including stale bytes outside the padded
last block. No message hash or compression result is used to construct inputs. -/
namespace AgaveLatticeHash.MLIR.CallerMemory
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)

/-- Installing a fresh named allocation preserves a distinct earlier buffer. -/
theorem holdsGlobal_withGlobal_preserved {s : GlobalState} (hs : s.WF)
    {name name' : String} {p : Pointer} {w w' : Nat} {v : BitVec w}
    (h : HoldsGlobal s name p v) (value : BitVec w') (hne : name ≠ name') :
    HoldsGlobal (s.withGlobal name' value) name p v := by
  have hid : (⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ : Pointer).id ≠ p.id := by
    have := h.lt_nextFreeBlock hs
    intro e
    have he := congrArg BlockId.id e
    simp only at he
    omega
  have hlive : (s.withGlobal name' value).mem.live? p.id = s.mem.live? p.id := by
    unfold GlobalState.withGlobal
    rw [live?_splice_ne hid]
    exact live?_afterAlloca_of_fits hs w' h.2.1
  refine ⟨?_, ?_⟩
  · simpa only [GlobalPtr, GlobalState.withGlobal_ptr_ne s value hne] using h.1
  · exact (readWord_of_live?_eq hlive h.2.1).imp fun _ hv => hv.trans h.2.2

def sourceBytes (n : Nat) (p : AgavePhysicalStaging.Store) : Vector (BitVec 8) (1024*n) :=
  Vector.ofFn fun i => AgavePhysicalStaging.memoryAt p (i.val / 1024) (i.val % 1024)

def lengthWords (n : Nat) (p : AgavePhysicalStaging.Store) : Vector (BitVec 64) n :=
  Vector.ofFn fun i => BitVec.ofNat 64 (AgavePhysicalStaging.lengthAt p i.val)

def accumulatorWords (a : AgaveStaging.Value) : Vector (BitVec 16) 1024 := Vector.ofFn a

def sourceName := "agave.caller.source"
def lengthsName := "agave.caller.lengths"
def accumulatorName := "agave.caller.accumulator"
def panicName := "alloc_83bddfce772813ac48c9037cf7b0770f"

/-- Each call gets disjoint caller allocations; the compiled entry itself
allocates scratch above these five blocks. This is a memory image constructor,
not an additional implementation of the batch algorithm. -/
def image (base : GlobalState) (n : Nat) (p : AgavePhysicalStaging.Store)
    (a : AgaveStaging.Value) : GlobalState :=
  let s1 := base.withGlobal sourceName (packBits (sourceBytes n p))
  let s2 := s1.withGlobal lengthsName (packBits (lengthWords n p))
  let s3 := s2.withGlobal accumulatorName (packBits (accumulatorWords a))
  let s4 := s3.withGlobal panicName (0#8)
  s4.withGlobal scheduleGlobalName scheduleGlobalBits

def ptr (base : GlobalState) (index : Nat) : Pointer :=
  ⟨⟨base.alloc.nextFreeBlock + index⟩, 0⟩

structure Represents (state : GlobalState) (n : Nat) (src len out sched panic : Pointer)
    (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value) : Prop where
  wf : state.WF
  source : HoldsGlobal state sourceName src (packBits (sourceBytes n p))
  lengths : HoldsGlobal state lengthsName len (packBits (lengthWords n p))
  accumulator : HoldsGlobal state accumulatorName out (packBits (accumulatorWords a))
  schedule : ScheduleGlobal state sched
  panic : GlobalPtr state panicName panic
  src_zero : src.offset = 0
  len_zero : len.offset = 0
  out_zero : out.offset = 0
  source_lengths : src.id ≠ len.id
  source_output : src.id ≠ out.id
  source_schedule : src.id ≠ sched.id
  lengths_output : len.id ≠ out.id
  lengths_schedule : len.id ≠ sched.id
  output_schedule : out.id ≠ sched.id

/-- Every retained store and accumulator admits a concrete caller image. In
particular, memory validity is established without a correctness assumption. -/
theorem image_represents (base : GlobalState) (hbase : base.WF) (n : Nat)
    (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value) :
    Represents (image base n p a) n (ptr base 0) (ptr base 1) (ptr base 2)
      (ptr base 4) (ptr base 3) p a := by
  let s1 := base.withGlobal sourceName (packBits (sourceBytes n p))
  let s2 := s1.withGlobal lengthsName (packBits (lengthWords n p))
  let s3 := s2.withGlobal accumulatorName (packBits (accumulatorWords a))
  let s4 := s3.withGlobal panicName (0#8)
  have hs1 : s1.WF := hbase.withGlobal _ _
  have hs2 : s2.WF := hs1.withGlobal _ _
  have hs3 : s3.WF := hs2.withGlobal _ _
  have hs4 : s4.WF := hs3.withGlobal _ _
  have h1 : HoldsGlobal s1 sourceName (ptr base 0) (packBits (sourceBytes n p)) :=
    holdsGlobal_withGlobal base sourceName _
  have h2 : HoldsGlobal s2 lengthsName (ptr base 1) (packBits (lengthWords n p)) :=
    holdsGlobal_withGlobal s1 lengthsName _
  have h3 : HoldsGlobal s3 accumulatorName (ptr base 2) (packBits (accumulatorWords a)) := by
    simpa only [s2, s1, GlobalState.withGlobal_nextFreeBlock, ptr, Nat.add_assoc] using
      holdsGlobal_withGlobal s2 accumulatorName (packBits (accumulatorWords a))
  have h4 : HoldsGlobal s4 panicName (ptr base 3) (0#8) := by
    simpa only [s3, s2, s1, GlobalState.withGlobal_nextFreeBlock, ptr, Nat.add_assoc] using
      holdsGlobal_withGlobal s3 panicName (0#8)
  have h1 := holdsGlobal_withGlobal_preserved (name' := lengthsName) hs1 h1 (packBits (lengthWords n p)) (by decide)
  have h1 := holdsGlobal_withGlobal_preserved (name' := accumulatorName) hs2 h1 (packBits (accumulatorWords a)) (by decide)
  have h1 := holdsGlobal_withGlobal_preserved (name' := panicName) hs3 h1 (0#8) (by decide)
  have h1 := holdsGlobal_withGlobal_preserved (name' := scheduleGlobalName) hs4 h1 scheduleGlobalBits (by decide)
  have h2 := holdsGlobal_withGlobal_preserved (name' := accumulatorName) hs2 h2 (packBits (accumulatorWords a)) (by decide)
  have h2 := holdsGlobal_withGlobal_preserved (name' := panicName) hs3 h2 (0#8) (by decide)
  have h2 := holdsGlobal_withGlobal_preserved (name' := scheduleGlobalName) hs4 h2 scheduleGlobalBits (by decide)
  have h3 := holdsGlobal_withGlobal_preserved (name' := panicName) hs3 h3 (0#8) (by decide)
  have h3 := holdsGlobal_withGlobal_preserved (name' := scheduleGlobalName) hs4 h3 scheduleGlobalBits (by decide)
  have h4 := holdsGlobal_withGlobal_preserved (name' := scheduleGlobalName) hs4 h4 scheduleGlobalBits (by decide)
  refine ⟨hs4.withGlobal _ _, h1, h2, h3, ?_, h4.ptr, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [image, s4, s3, s2, s1, GlobalState.withGlobal_nextFreeBlock, ptr, Nat.add_assoc]
      using scheduleGlobal_withGlobal s4
  all_goals simp [ptr, BlockId.mk.injEq]

private theorem packBits_eq_packLanes {n w : Nat} (v : Vector (BitVec w) n) :
    packBits v = BitVec.packLanes v := by
  unfold packBits LLVM.Ty.flattenBV
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  change ((v.map PoisonOr.value)[i]).toOption.getD 0 = v[i]
  rw [Vector.getElem_map]
  rfl

/-- Every bounded contiguous run of bytes in a caller image is loaded verbatim.
The caller supplies a simple allocation bound, not per-load memory equalities. -/
theorem read_byte_run {state : GlobalState} {name : String} {p : Pointer}
    {n : Nat} {bytes : Vector (BitVec 8) n}
    (h : HoldsGlobal state name p (packBits bytes)) (hz : p.offset = 0)
    (count offset : Nat) (hbound : offset + count ≤ n) (hword : offset < 2^64) :
    readWord? (p.withOffset (BitVec.ofNat 64 offset)) (8*count) state.mem =
      some (packBits (Vector.ofFn fun i : Fin count => bytes[offset+i.val]'(by omega))) := by
  have hoff : (p.withOffset (BitVec.ofNat 64 offset)).offsetInBits =
      p.offsetInBits + 8*offset := by
    apply offsetInBits_withOffset_nat
    simpa [hz] using hword
  have hr := readWord?_extract (packBits bytes) h.2.1 (readWord?_eq_some h.2.1 h.2.2)
    (q := p.withOffset (BitVec.ofNat 64 offset)) rfl hoff
    (show 8*offset + 8*count ≤ 8*n by omega)
  rw [packBits_eq_packLanes, BitVec.extractLsb'_packLanes_run bytes count offset hbound] at hr
  simpa only [packBits_eq_packLanes] using hr

/-- Read any contiguous run within a retained lane. Stale suffix bytes are
preserved as well; padding validity comes from the separate staging invariant. -/
theorem Represents.read_source_run {state : GlobalState} {n : Nat}
    {src len out sched panic : Pointer} {p : AgavePhysicalStaging.Store}
    {a : AgaveStaging.Value} (h : Represents state n src len out sched panic p a)
    (hn : n ≤ 16) (lane : Fin n) (count offset : Nat) (hb : offset + count ≤ 1024) :
    readWord? (src.withOffset (BitVec.ofNat 64 (1024*lane.val+offset))) (8*count) state.mem =
      some (packBits (Vector.ofFn fun i : Fin count =>
        AgavePhysicalStaging.memoryAt p lane.val (offset+i.val))) := by
  have hlane := lane.isLt
  have hfull : 1024*lane.val+offset+count ≤ 1024*n := by omega
  have hr := read_byte_run h.source h.src_zero count (1024*lane.val+offset) hfull (by omega)
  rw [hr]
  congr 2
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, sourceBytes]
  congr 1 <;> omega

/-- The initialized accumulator is observed through its actual u16 loads. -/
theorem Represents.read_accumulator {state : GlobalState} {n : Nat}
    {src len out sched panic : Pointer} {p : AgavePhysicalStaging.Store}
    {a : AgaveStaging.Value} (h : Represents state n src len out sched panic p a)
    (i : Fin 1024) :
    readWord? (out.withOffset (BitVec.ofNat 64 (2*i.val))) 16 state.mem = some (a i) := by
  have hoff : (out.withOffset (BitVec.ofNat 64 (2*i.val))).offsetInBits =
      out.offsetInBits + i.val*16 := by
    rw [offsetInBits_withOffset_nat]
    · omega
    · rw [h.out_zero]
      change 0 + 2*i.val < 2^64
      omega
  have hr := readWord?_extract (packBits (accumulatorWords a)) h.accumulator.2.1
    (readWord?_eq_some h.accumulator.2.1 h.accumulator.2.2)
    (q := out.withOffset (BitVec.ofNat 64 (2*i.val))) rfl hoff
    (show i.val*16+16 ≤ 16*1024 by omega)
  rw [extract_packBits] at hr
  simpa only [accumulatorWords, Fin.getElem_fin, Vector.getElem_ofFn] using hr

/-- Read any contiguous group of length metadata cells, including the two
8-lane halves used by the compiled AVX512 entry. -/
theorem Represents.read_length_run {state : GlobalState} {n : Nat}
    {src len out sched panic : Pointer} {p : AgavePhysicalStaging.Store}
    {a : AgaveStaging.Value} (h : Represents state n src len out sched panic p a)
    (hn : n ≤ 16) (count offset : Nat) (hb : offset + count ≤ n) :
    readWord? (len.withOffset (BitVec.ofNat 64 (8*offset))) (64*count) state.mem =
      some (packBits (Vector.ofFn fun i : Fin count =>
        BitVec.ofNat 64 (AgavePhysicalStaging.lengthAt p (offset+i.val)))) := by
  have hoff : (len.withOffset (BitVec.ofNat 64 (8*offset))).offsetInBits =
      len.offsetInBits + 64*offset := by
    rw [offsetInBits_withOffset_nat]
    · omega
    · rw [h.len_zero]
      change 0 + 8*offset < 2^64
      omega
  have hr := readWord?_extract (packBits (lengthWords n p)) h.lengths.2.1
    (readWord?_eq_some h.lengths.2.1 h.lengths.2.2)
    (q := len.withOffset (BitVec.ofNat 64 (8*offset))) rfl hoff
    (show 64*offset+64*count ≤ 64*n by omega)
  rw [packBits_eq_packLanes,
    BitVec.extractLsb'_packLanes_run (lengthWords n p) count offset hb] at hr
  simpa only [packBits_eq_packLanes, lengthWords, Vector.getElem_ofFn] using hr

/-- An empty caller is a concrete witness, so materialization does not itself
require any environmental memory or allocator premise. -/
def emptyState : GlobalState := ⟨⟨0⟩, ⟨∅⟩, ∅⟩

theorem emptyState_wf : emptyState.WF := by
  intro q _
  have he : (⟨∅⟩ : MemoryState)[q]? = none := by
    change (∅ : Std.HashMap BlockId Block)[q]? = none
    simp
  simp only [emptyState, MemoryState.live?, he]

theorem materialization_exists (n : Nat) (p : AgavePhysicalStaging.Store)
    (a : AgaveStaging.Value) :
    ∃ state src len out sched panic, Represents state n src len out sched panic p a :=
  ⟨image emptyState n p a, ptr emptyState 0, ptr emptyState 1, ptr emptyState 2,
    ptr emptyState 4, ptr emptyState 3, image_represents emptyState emptyState_wf n p a⟩

end AgaveLatticeHash.MLIR.CallerMemory
