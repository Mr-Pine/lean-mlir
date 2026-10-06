/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CallerMemory

namespace AgaveLatticeHash.MLIR.CallerMemory
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)

/-- Four adjacent retained bytes form one little-endian compression word. -/
def wordsLE (n : Nat) (bytes : Nat → BitVec 8) : Vector (BitVec 32) n :=
  Vector.ofFn fun i => bytes (4*i.val+3) ++ bytes (4*i.val+2) ++
    bytes (4*i.val+1) ++ bytes (4*i.val)

private theorem packBits_as_packLanes {n w : Nat} (v : Vector (BitVec w) n) :
    packBits v = BitVec.packLanes v := by
  unfold packBits LLVM.Ty.flattenBV
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  change ((v.map PoisonOr.value)[i]).toOption.getD 0 = v[i]
  rw [Vector.getElem_map]
  rfl

private theorem bits_eq_of_words {n : Nat} (x y : BitVec (32*n))
    (h : ∀ i : Fin n, x.extractLsb' (i.val*32) 32 = y.extractLsb' (i.val*32) 32) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : k/32 < n := by omega
  have he := congrArg (fun z : BitVec 32 => z.getLsbD (k%32)) (h ⟨k/32, hi⟩)
  have hb : k%32 < 32 := by omega
  simpa only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    show k/32*32+k%32=k by omega] using he

/-- A byte-vector load and the grouped u32-vector load have the same bits.
This proof is generic in the number of words, including zero. -/
theorem pack_wordsLE (n : Nat) (bytes : Nat → BitVec 8) :
    packBits (wordsLE n bytes) =
      (packBits (Vector.ofFn fun i : Fin (4*n) => bytes i.val)).cast (by omega) := by
  apply bits_eq_of_words
  intro i
  rw [extract_packBits, BitVec.extractLsb'_cast, packBits_as_packLanes]
  rw [show i.val*32 = 8*(4*i.val) by omega,
    BitVec.extractLsb'_packLanes_run _ 4 (4*i.val) (by have := i.isLt; omega)]
  simp [wordsLE, BitVec.packLanes, Vector.tail_ofFn, Fin.succ, -Vector.tail_eq_cast_extract]
  rw [show (0#0 ++ bytes (4*i.val+3)) = bytes (4*i.val+3) from BitVec.zero_width_append _ _]

private theorem readWord_cast (m : MemoryState) (p : Pointer) {w w' : Nat} (he : w = w') :
    (readWord? p w m).map (BitVec.cast he) = readWord? p w' m := by
  cases he
  change (readWord? p w m).map id = readWord? p w m
  simp

/-- Read a row of little-endian u32 words directly from retained source bytes. -/
theorem Represents.read_source_words {state : GlobalState} {n : Nat}
    {src len out sched panic : Pointer} {p : AgavePhysicalStaging.Store}
    {a : AgaveStaging.Value} (h : Represents state n src len out sched panic p a)
    (hn : n ≤ 16) (lane : Fin n) (words offset : Nat) (hb : offset + 4*words ≤ 1024) :
    readWord? (src.withOffset (BitVec.ofNat 64 (1024*lane.val+offset))) (32*words) state.mem =
      some (packBits (wordsLE words (fun i => AgavePhysicalStaging.memoryAt p lane.val (offset+i)))) := by
  have hr := h.read_source_run hn lane (4*words) offset hb
  rw [pack_wordsLE]
  have hw : 8*(4*words) = 32*words := by omega
  have hc := congrArg (Option.map (BitVec.cast hw)) hr
  rw [readWord_cast, Option.map_some] at hc
  exact hc

/-- Existing retained-staging invariants supply the metadata and padding facts
needed by compiled batch calls. The ghost message list is not used to construct
caller bytes; it only specifies those independently retained bytes. -/
theorem represented_messages (n : Nat) (p : AgavePhysicalStaging.Store) (s : AgaveStaging.Impl)
    (hr : AgavePhysicalStaging.Represents p s) (hfull : p.count = n) (hs : AgaveStaging.PendingOK s) :
    let ms : Fin n → AgaveConcrete.Message := fun lane =>
      AgaveConcrete.toBytes (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hfull) lane)
    (∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length) ∧
    (∀ lane, (ms lane).length ≤ 1024) ∧
    (∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val)) := by
  let ms : Fin n → AgaveConcrete.Message := fun lane =>
    AgaveConcrete.toBytes (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hfull) lane)
  have hv := AgavePhysicalStaging.full_flush_valid p s n hr hfull hs
  change (∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length) ∧
    (∀ lane, (ms lane).length ≤ 1024) ∧
    (∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val))
  have hlen (lane : Fin n) : AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length := by
    simpa only [ms, AgaveConcrete.toBytes_length] using (hv lane).1
  refine ⟨hlen, ?_, ?_⟩
  · intro lane
    rw [← hlen lane]
    exact (hv lane).2.1
  · intro lane
    rw [← hlen lane]
    exact (hv lane).2.2

end AgaveLatticeHash.MLIR.CallerMemory
