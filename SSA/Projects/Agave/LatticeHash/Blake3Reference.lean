/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.OutputLog

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

/-!
An independent manual transcription of the unkeyed, one-shot, portable path in
the locked Rust `blake3` crate 1.8.7. `portable.rs` uses sequential assignments,
seven explicit round calls, and separate CV/XOF feed-forward. `ChunkState::update`
in `lib.rs` compresses while more than 64 input bytes remain and then buffers the
last block. `Output` adds CHUNK_END and ROOT; portable `xof_many` increments the
output counter. None of these definitions calls `AgaveConcrete.oneChunk`.

The theorem below is about the manually transcribed portable semantics. It is
not a Rust extraction or compiler theorem, and does not verify the upstream
crate's other runtime-dispatched implementations.
-/
namespace AgaveBlake3Reference

abbrev Byte := BitVec 8
abbrev Word := BitVec 32
abbrev Words := Fin 16 → Word
abbrev CV := Fin 8 → Word
abbrev Block := Fin 64 → Byte
abbrev Message := List Byte

def put (s : Words) (i : Fin 16) (v : Word) : Words :=
  fun j => if j = i then v else s j

/-- Literal state writes in `portable.rs::g`, in source order. -/
def g (s : Words) (a b c d : Fin 16) (x y : Word) : Words :=
  let s := put s a (s a + s b + x)
  let s := put s d ((s d ^^^ s a).rotateRight 16)
  let s := put s c (s c + s d)
  let s := put s b ((s b ^^^ s c).rotateRight 12)
  let s := put s a (s a + s b + y)
  let s := put s d ((s d ^^^ s a).rotateRight 8)
  let s := put s c (s c + s d)
  put s b ((s b ^^^ s c).rotateRight 7)

theorem g_eq (s : Words) (a b c d : Fin 16) (x y : Word)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    g s a b c d x y = Blake3Compression.gStep Blake3Compression.scalarG s a b c d x y := by
  funext i
  by_cases ha : i = a
  · subst i
    simp [g, put, Blake3Compression.gStep, Blake3Compression.scalarG,
      hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had,
      Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]
  by_cases hb : i = b
  · subst i
    simp [g, put, Blake3Compression.gStep, Blake3Compression.scalarG,
      hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had,
      Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]
  by_cases hc : i = c
  · subst i
    simp [g, put, Blake3Compression.gStep, Blake3Compression.scalarG,
      hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had,
      Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]
  by_cases hd : i = d
  · subst i
    simp [g, put, Blake3Compression.gStep, Blake3Compression.scalarG,
      hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had,
      Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]
  simp [g, put, Blake3Compression.gStep, ha, hb, hc, hd]

/-- A separate transcription of `lib.rs::MSG_SCHEDULE`. -/
def schedules : Vector (Vector (Fin 16) 16) 7 := #v[
  #v[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
  #v[2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8],
  #v[3,4,10,12,13,2,7,14,6,5,9,0,11,15,8,1],
  #v[10,7,12,9,14,3,13,15,4,0,11,2,5,8,1,6],
  #v[12,13,9,11,15,10,14,8,7,2,5,3,0,1,6,4],
  #v[9,14,11,5,8,12,15,1,13,3,0,10,2,6,4,7],
  #v[11,15,5,0,1,9,8,6,14,10,2,12,3,4,7,13]]

theorem schedules_eq : schedules = Blake3Compression.messageSchedule := by rfl

def round (s m : Words) (r : Fin 7) : Words :=
  let p := schedules.get r
  let s := g s 0 4 8 12 (m (p.get 0)) (m (p.get 1))
  let s := g s 1 5 9 13 (m (p.get 2)) (m (p.get 3))
  let s := g s 2 6 10 14 (m (p.get 4)) (m (p.get 5))
  let s := g s 3 7 11 15 (m (p.get 6)) (m (p.get 7))
  let s := g s 0 5 10 15 (m (p.get 8)) (m (p.get 9))
  let s := g s 1 6 11 12 (m (p.get 10)) (m (p.get 11))
  let s := g s 2 7 8 13 (m (p.get 12)) (m (p.get 13))
  g s 3 4 9 14 (m (p.get 14)) (m (p.get 15))

theorem round_eq (s m : Words) (r : Fin 7) :
    round s m r = Blake3Compression.roundFn Blake3Compression.scalarG s m r := by
  simp (discharger := decide) only [round, g_eq, schedules_eq,
    Blake3Compression.roundFn, Blake3Compression.schedule]

def load32 (b : Block) (w : Fin 16) : Word :=
  b ⟨4 * w.val + 3, by omega⟩ ++ b ⟨4 * w.val + 2, by omega⟩ ++
  b ⟨4 * w.val + 1, by omega⟩ ++ b ⟨4 * w.val, by omega⟩

def initial (cv : CV) (counter : BitVec 64) (len flags : Word) : Words :=
  fun i => (#v[cv 0, cv 1, cv 2, cv 3, cv 4, cv 5, cv 6, cv 7,
    0x6A09E667#32, 0xBB67AE85#32, 0x3C6EF372#32, 0xA54FF53A#32,
    counter.extractLsb' 0 32, counter.extractLsb' 32 32, len, flags]).get i

theorem initial_eq (cv : CV) (counter : BitVec 64) (len flags : Word) :
    initial cv counter len flags = Blake3Compression.scalarInit cv counter len flags := by
  funext i
  have hi := i.isLt
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

def compressPre (cv : CV) (b : Block) (len : Word) (counter : BitVec 64)
    (flags : Word) : Words :=
  let s := initial cv counter len flags
  let m := load32 b
  let s := round s m 0
  let s := round s m 1
  let s := round s m 2
  let s := round s m 3
  let s := round s m 4
  let s := round s m 5
  round s m 6

theorem compressPre_eq (cv : CV) (b : Block) (len : Word) (counter : BitVec 64)
    (flags : Word) :
    compressPre cv b len counter flags =
      Blake3Compression.scalarCompressPre cv (AgaveConcrete.decodeBlock b) counter len flags := by
  simp only [compressPre, round_eq, initial_eq]
  rfl

def compressInPlace (cv : CV) (b : Block) (len : Word) (counter : BitVec 64)
    (flags : Word) : CV :=
  let s := compressPre cv b len counter flags
  fun i => s ⟨i.val, by omega⟩ ^^^ s ⟨i.val + 8, by omega⟩

theorem compressInPlace_eq (cv : CV) (b : Block) (len : Word) (counter : BitVec 64)
    (flags : Word) :
    compressInPlace cv b len counter flags =
      Blake3Compression.scalarCompressCV cv (AgaveConcrete.decodeBlock b) counter len flags := by
  funext i
  simp [compressInPlace, compressPre_eq, Blake3Compression.scalarCompressCV,
    Blake3Compression.scalarCompress, Blake3Compression.feedForward, i.isLt]
  rfl

/-- The portable XOF's sixteen explicit feed-forward assignments. -/
def compressXofWords (cv : CV) (b : Block) (len : Word) (counter : BitVec 64)
    (flags : Word) : Words :=
  let s := compressPre cv b len counter flags
  fun i => (#v[
    s 0 ^^^ s 8, s 1 ^^^ s 9, s 2 ^^^ s 10, s 3 ^^^ s 11,
    s 4 ^^^ s 12, s 5 ^^^ s 13, s 6 ^^^ s 14, s 7 ^^^ s 15,
    s 8 ^^^ cv 0, s 9 ^^^ cv 1, s 10 ^^^ cv 2, s 11 ^^^ cv 3,
    s 12 ^^^ cv 4, s 13 ^^^ cv 5, s 14 ^^^ cv 6, s 15 ^^^ cv 7]).get i

theorem compressXofWords_eq (cv : CV) (b : Block) (len : Word) (counter : BitVec 64)
    (flags : Word) :
    compressXofWords cv b len counter flags =
      Blake3Compression.scalarCompress cv (AgaveConcrete.decodeBlock b) counter len flags := by
  funext i
  unfold compressXofWords
  simp only [compressPre_eq, Blake3Compression.scalarCompress, Blake3Compression.feedForward]
  have hi := i.isLt
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- Rust input slices are represented by a pointer-relative byte function and
    a remaining length. Bytes outside `len` are never read by a successful loop. -/
structure Input where
  data : Nat → Byte
  len : Nat

def input (m : Message) : Input := ⟨fun i => m[i]?.getD 0, m.length⟩

def advance64 (s : Input) : Input := ⟨fun i => s.data (64 + i), s.len - 64⟩
def firstBlock (s : Input) : Block := fun i => s.data i.val

/-- `fill_buf` on the fresh zero-filled buffer used on this one-shot path. -/
def fillBuf (s : Input) : Block := fun i => if i.val < s.len then s.data i.val else 0

structure ChunkState where
  cv : CV
  blocksCompressed : Nat
  buf : Block
  bufLen : Nat

def startFlag (blocks : Nat) : Word := if blocks = 0 then 1 else 0

/-- This is the `while input.len() > BLOCK_LEN` portion of `ChunkState::update`,
    followed by `fill_buf`. There are no incoming buffered bytes after reset.
    Fuel exhaustion is explicit and will be proved unreachable for short inputs. -/
def updateLoop : Nat → Input → CV → Nat → Option ChunkState
  | 0, s, cv, blocks =>
      if 64 < s.len then none else some ⟨cv, blocks, fillBuf s, s.len⟩
  | fuel + 1, s, cv, blocks =>
      if 64 < s.len then
        updateLoop fuel (advance64 s)
          (compressInPlace cv (firstBlock s) 64 0 (startFlag blocks)) (blocks + 1)
      else some ⟨cv, blocks, fillBuf s, s.len⟩

def iv : CV := fun i => (#v[
  0x6A09E667#32, 0xBB67AE85#32, 0x3C6EF372#32, 0xA54FF53A#32,
  0x510E527F#32, 0x9B05688C#32, 0x1F83D9AB#32, 0x5BE0CD19#32]).get i

theorem iv_eq : iv = AgaveConcrete.iv := by rfl

/-- Specialization of `Hasher::reset().update(m)` to an input that fits within
    the first chunk. No tree loop is entered; the CV stack remains empty. -/
def updateFresh (m : Message) : Option ChunkState := updateLoop 15 (input m) iv 0

def inputAt (m : Message) (j : Nat) : Input :=
  ⟨fun i => AgaveConcrete.bytes m (64 * j + i), m.length - 64 * j⟩

theorem input_eq (m : Message) : input m = inputAt m 0 := by
  unfold input inputAt
  simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_zero]
  congr 1
  funext i
  simp only [AgaveConcrete.bytes]
  by_cases hi : i < m.length
  · simp [hi]
  · simp [hi]

theorem advance64_eq (m : Message) (j : Nat) :
    advance64 (inputAt m j) = inputAt m (j + 1) := by
  unfold advance64 inputAt
  congr 1
  · funext i
    simp [advance64, inputAt, Nat.mul_add, Nat.add_assoc]

theorem firstBlock_eq (m : Message) (j : Nat)
    (hj : j < AgaveBatchControl.rootIndex m.length) :
    firstBlock (inputAt m j) =
      AgaveBatchControl.scalarBlock (AgaveConcrete.bytes m) m.length j := by
  have h := (AgaveBatchControl.rootIndex_before_last m.length j).mpr hj
  funext i
  simp only [firstBlock, inputAt, AgaveBatchControl.scalarBlock]
  have hi := i.isLt
  have hi' : 64 * j + i.val < m.length := by omega
  simp [hi']

theorem fillBuf_eq (m : Message) (j : Nat) (hj : 64 * j ≤ m.length) :
    fillBuf (inputAt m j) =
      AgaveBatchControl.scalarBlock (AgaveConcrete.bytes m) m.length j := by
  funext i
  have hc : i.val < m.length - 64 * j ↔ 64 * j + i.val < m.length := by omega
  simp [fillBuf, inputAt, AgaveBatchControl.scalarBlock, hc]

def finalChunk (m : Message) : ChunkState :=
  ⟨AgaveBatchControl.scalarPrefix AgaveConcrete.compress AgaveConcrete.iv
      (AgaveConcrete.bytes m) m.length (AgaveBatchControl.rootIndex m.length),
    AgaveBatchControl.rootIndex m.length,
    AgaveBatchControl.scalarBlock (AgaveConcrete.bytes m) m.length
      (AgaveBatchControl.rootIndex m.length),
    AgaveBatchControl.scalarRootSize m.length⟩

/-- Loop invariant: the slice pointer has advanced by exactly the compressed
    blocks, the CV is their scalar compression, and the final block is withheld. -/
theorem updateLoop_eq (m : Message) (fuel j : Nat)
    (hj : j ≤ AgaveBatchControl.rootIndex m.length)
    (hf : AgaveBatchControl.rootIndex m.length ≤ j + fuel) :
    updateLoop fuel (inputAt m j)
      (AgaveBatchControl.scalarPrefix AgaveConcrete.compress AgaveConcrete.iv
        (AgaveConcrete.bytes m) m.length j) j = some (finalChunk m) := by
  induction fuel generalizing j with
  | zero =>
    have he : j = AgaveBatchControl.rootIndex m.length := by omega
    subst j
    have hr := AgaveBatchControl.rootIndex_bounds m.length
    have hn : ¬64 < m.length - 64 * AgaveBatchControl.rootIndex m.length := by omega
    simp only [updateLoop, inputAt, hn, ↓reduceIte]
    rw [show fillBuf ⟨_, _⟩ = _ from fillBuf_eq m _ hr.1]
    unfold finalChunk
    congr 2
    have hsize := AgaveBatchControl.root_size m.length
    unfold AgaveBatchControl.blockSize at hsize
    have hs : m.length - 64 * AgaveBatchControl.rootIndex m.length ≤ 64 := by omega
    simpa [Nat.min_eq_left hs] using hsize
  | succ fuel ih =>
    by_cases ha : j < AgaveBatchControl.rootIndex m.length
    · have hl := (AgaveBatchControl.rootIndex_before_last m.length j).mpr ha
      have hp : 64 < (inputAt m j).len := by simp only [inputAt]; omega
      simp only [updateLoop, hp, ↓reduceIte]
      rw [advance64_eq, compressInPlace_eq, firstBlock_eq m j ha]
      have hc : Blake3Compression.scalarCompressCV
          (AgaveBatchControl.scalarPrefix AgaveConcrete.compress AgaveConcrete.iv
            (AgaveConcrete.bytes m) m.length j)
          (AgaveConcrete.decodeBlock
            (AgaveBatchControl.scalarBlock (AgaveConcrete.bytes m) m.length j))
          0 64 (startFlag j) =
          AgaveBatchControl.scalarPrefix AgaveConcrete.compress AgaveConcrete.iv
            (AgaveConcrete.bytes m) m.length (j + 1) := by
        simp only [AgaveBatchControl.scalarPrefix, AgaveConcrete.compress,
          AgaveConcrete.counter, startFlag]
        split <;> rfl
      rw [hc]
      apply ih
      · omega
      · omega
    · have he : j = AgaveBatchControl.rootIndex m.length := by omega
      subst j
      have hr := AgaveBatchControl.rootIndex_bounds m.length
      have hn : ¬64 < (inputAt m (AgaveBatchControl.rootIndex m.length)).len := by
        simp only [inputAt]
        omega
      simp only [updateLoop, hn, ↓reduceIte]
      rw [fillBuf_eq m _ hr.1]
      unfold finalChunk
      congr 2
      have hsize := AgaveBatchControl.root_size m.length
      unfold AgaveBatchControl.blockSize at hsize
      have hs : m.length - 64 * AgaveBatchControl.rootIndex m.length ≤ 64 := by omega
      simpa [inputAt, Nat.min_eq_left hs] using hsize

theorem updateFresh_eq (m : Message) (hm : m.length ≤ 1024) :
    updateFresh m = some (finalChunk m) := by
  unfold updateFresh
  rw [input_eq, iv_eq]
  apply updateLoop_eq
  · omega
  · have := AgaveBatchControl.rootIndex_lt16 m.length hm
    omega

/-- The source's u8 fields and 64-byte buffer cannot overflow on this path. -/
theorem updateFresh_source_bounds (m : Message) (hm : m.length ≤ 1024)
    {s : ChunkState} (hs : updateFresh m = some s) :
    s.blocksCompressed ≤ 15 ∧ s.bufLen ≤ 64 ∧
      64 * s.blocksCompressed + s.bufLen = m.length := by
  rw [updateFresh_eq m hm] at hs
  cases Option.some.inj hs
  have hblocks := AgaveBatchControl.rootIndex_lt16 m.length hm
  have hsize := (AgaveBatchControl.root_size_bounds m.length).1
  have hb := AgaveBatchControl.rootIndex_bounds m.length
  have he := AgaveBatchControl.root_size m.length
  simp only [AgaveBatchControl.blockSize] at he
  simp only [finalChunk]
  omega


/-- The last-buffer output is `start_flag | CHUNK_END | ROOT`, with the
    original chunk counter (zero) replaced by each output-block counter. -/
def rootWords (s : ChunkState) (counter : Nat) : Words :=
  compressXofWords s.cv s.buf (BitVec.ofNat 32 s.bufLen) (BitVec.ofNat 64 counter)
    ((startFlag s.blocksCompressed ||| 2) ||| 8)

theorem rootFlags_eq (len : Nat) :
    ((startFlag (AgaveBatchControl.rootIndex len) ||| 2) ||| 8) =
      BitVec.ofNat 32 (AgaveBatchControl.scalarRootFlags len) := by
  by_cases h : len ≤ 64
  · have hz := (AgaveBatchControl.rootIndex_zero_iff len).mpr h
    simp [startFlag, hz, AgaveBatchControl.scalarRootFlags, h]
  · have hz : AgaveBatchControl.rootIndex len ≠ 0 := by
      intro hz
      exact h ((AgaveBatchControl.rootIndex_zero_iff len).mp hz)
    simp [startFlag, hz, AgaveBatchControl.scalarRootFlags, h]

theorem rootWords_eq (m : Message) (out : Fin 32) :
    rootWords (finalChunk m) out.val = AgaveConcrete.oneChunkWords m out := by
  simp only [rootWords, finalChunk, compressXofWords_eq, rootFlags_eq,
    AgaveConcrete.oneChunkWords, AgaveBatchControl.scalarXofAt,
    AgaveConcrete.xof, AgaveConcrete.counter, Nat.mul_zero, Nat.add_zero]


/-- `platform::le_bytes_from_words_64`, after portable feed-forward. -/
def serialize (s : Words) : Block := fun i =>
  (s ⟨i.val / 4, by omega⟩).extractLsb' (8 * (i.val % 4)) 8

def rootOutput (s : ChunkState) (counter : Nat) : Block := serialize (rootWords s counter)

/-- Portable `Platform::xof_many`: increment the counter after every 64-byte
    output block. `LtHash::with` requests exactly 32 such blocks. -/
def xofMany : Nat → Nat → ChunkState → List Block
  | 0, _, _ => []
  | n + 1, counter, s => rootOutput s counter :: xofMany n (counter + 1) s

@[simp] theorem xofMany_length (n counter : Nat) (s : ChunkState) :
    (xofMany n counter s).length = n := by
  induction n generalizing counter with
  | zero => rfl
  | succ n ih => simp [xofMany, ih]

theorem xofMany_get (n counter : Nat) (s : ChunkState) (i : Nat) (hi : i < n) :
    (xofMany n counter s)[i]'(by simp [hi]) = rootOutput s (counter + i) := by
  induction n generalizing counter i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [xofMany]
    | succ i =>
      simp only [xofMany, List.getElem_cons_succ]
      rw [ih _ i (by omega)]
      congr 1
      omega

/-- The fresh OutputReader begins at byte zero. Its 2048-byte request has 32
    full blocks and no leading/trailing partial block. -/
def readerFill (s : ChunkState) : Fin 2048 → Byte := fun i =>
  ((xofMany 32 0 s)[i.val / 64]'(by simp; omega)) ⟨i.val % 64, by omega⟩

theorem readerFill_eq (s : ChunkState) (i : Fin 2048) :
    readerFill s i = serialize (rootWords s (i.val / 64)) ⟨i.val % 64, by omega⟩ := by
  have h := xofMany_get 32 0 s (i.val / 64) (by omega)
  simpa only [readerFill, rootOutput, Nat.zero_add] using
    congrFun h ⟨i.val % 64, by omega⟩


/-- Agave writes the reader bytes into `[u16; 1024]`; x86 is little-endian. -/
def finishLtHash (s : ChunkState) : AgaveConcrete.Value := fun i =>
  readerFill s ⟨2 * i.val + 1, by omega⟩ ++ readerFill s ⟨2 * i.val, by omega⟩

def portableLtHash (m : Message) : Option AgaveConcrete.Value :=
  (updateFresh m).map finishLtHash

theorem twoBytes_eq_halfWord (x : Word) (half : Fin 2) :
    x.extractLsb' (8 * (2 * half.val + 1)) 8 ++
      x.extractLsb' (8 * (2 * half.val)) 8 = AgaveLattice.halfWord x half := by
  have hc : half = 0 ∨ half = 1 := by omega
  rcases hc with rfl | rfl
  · exact BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)
  · exact BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)


theorem finishLtHash_eq (m : Message) : finishLtHash (finalChunk m) = AgaveConcrete.oneChunk m := by
  funext i
  unfold finishLtHash
  rw [readerFill_eq, readerFill_eq]
  have ho1 : (2 * i.val + 1) / 64 = i.val / 32 := by omega
  have ho0 : (2 * i.val) / 64 = i.val / 32 := by omega
  simp only [ho1, ho0]
  rw [rootWords_eq m ⟨i.val / 32, by omega⟩]
  simp only [serialize, AgaveConcrete.oneChunk]
  have hw1 : (2 * i.val + 1) % 64 / 4 = i.val % 32 / 2 := by omega
  have hw0 : (2 * i.val) % 64 / 4 = i.val % 32 / 2 := by omega
  have hb1 : (2 * i.val + 1) % 64 % 4 = 2 * (i.val % 2) + 1 := by omega
  have hb0 : (2 * i.val) % 64 % 4 = 2 * (i.val % 2) := by omega
  simp only [hw1, hw0, hb1, hb0]
  exact twoBytes_eq_halfWord _ ⟨i.val % 2, by omega⟩

/-- For every short message, the independent portable-source model terminates
    and returns exactly the one-chunk oracle used by the AVX refinement. -/
theorem portableLtHash_eq_oneChunk (m : Message) (hm : m.length ≤ 1024) :
    portableLtHash m = some (AgaveConcrete.oneChunk m) := by
  simp only [portableLtHash, updateFresh_eq m hm, Option.map_some, finishLtHash_eq]

/-- A total reference hash for the surrounding lifecycle proof. The default
    value is unreachable on the short branch, as the preceding theorem proves.
    Long messages retain the same arbitrary shared serial implementation. -/
def referenceHash (longHash : Message → AgaveConcrete.Value) (m : Message) :
    AgaveConcrete.Value :=
  if m.length ≤ 1024 then (portableLtHash m).getD AgaveStaging.zero else longHash m

/-- Replaces the previously common short-message oracle by the independently
    structured portable-source program, with no additional caller premise. -/
theorem referenceHash_eq_scalarHash (longHash : Message → AgaveConcrete.Value) :
    referenceHash longHash = AgaveConcrete.scalarHash longHash := by
  funext m
  by_cases hm : m.length ≤ 1024
  · simp only [referenceHash, AgaveConcrete.scalarHash, hm, ↓reduceIte,
      portableLtHash_eq_oneChunk m hm, Option.getD_some]
  · simp only [referenceHash, AgaveConcrete.scalarHash, hm, ↓reduceIte]

/-- The scalar function used by the public lifecycle is exactly the portable
    reference above after the lossless `UInt8`-to-byte adapter. -/
theorem publicHash_eq_portableReference (longHash : Message → AgaveConcrete.Value) :
    AgaveConcrete.hash longHash =
      fun m => referenceHash longHash (AgaveConcrete.toBytes m) := by
  funext m
  unfold AgaveConcrete.hash
  exact (congrFun (referenceHash_eq_scalarHash longHash)
    (AgaveConcrete.toBytes m)).symm

/-- A direct corollary for every legal SIMD batch: each SIMD leaf can be replaced
    by the independently transcribed portable implementation. -/
theorem simdUpdate_eq_portableReference {n : Nat} (hn : 0 < n)
    {perm : AgaveLattice.Matrix} (hp : AgaveLattice.IsTranspose n perm)
    (ms : Fin n → Message) (hm : ∀ l, (ms l).length ≤ 1024)
    (a : AgaveConcrete.Value) :
    AgaveConcrete.simdUpdate hn perm ms a = (List.finRange n).foldl
      (fun z l => AgaveStaging.plus z ((portableLtHash (ms l)).getD AgaveStaging.zero)) a := by
  simp only [portableLtHash_eq_oneChunk _ (hm _), Option.getD_some]
  exact AgaveConcrete.simdUpdate_eq_fold hn hp ms hm a

/-- End-to-end source-shaped statement: any chronological event sequence
    accepted by the portable-reference specification has retained-memory
    executions at widths 1, 8 and 16, and all three produce exactly the same
    complete output log `out`. The sole premise is public API legality. -/
theorem every_legal_portable_trace (longHash : Message → AgaveConcrete.Value)
    (events : List AgaveOutputLog.Event) {r : AgaveMixed.Spec}
    {out : List AgaveConcrete.Value}
    (legal : AgaveOutputLog.specEval
      (fun m => referenceHash longHash (AgaveConcrete.toBytes m)) events = some (r, out)) :
    (∃ p s, AgaveOutputLog.Run longHash 1 (by decide) AgaveLattice.labels
      events p s r out) ∧
    (∃ p s, AgaveOutputLog.Run longHash 8 (by decide)
      (AgaveLattice.transpose8 AgaveLattice.labels) events p s r out) ∧
    (∃ p s, AgaveOutputLog.Run longHash 16 (by decide)
      (AgaveLattice.transpose16 AgaveLattice.labels) events p s r out) := by
  apply AgaveOutputLog.every_legal_trace longHash events
  rw [publicHash_eq_portableReference longHash]
  exact legal

/-- info: 'AgaveBlake3Reference.portableLtHash_eq_oneChunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms portableLtHash_eq_oneChunk
/-- info: 'AgaveBlake3Reference.referenceHash_eq_scalarHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms referenceHash_eq_scalarHash
/-- info: 'AgaveBlake3Reference.publicHash_eq_portableReference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms publicHash_eq_portableReference
/-- info: 'AgaveBlake3Reference.simdUpdate_eq_portableReference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms simdUpdate_eq_portableReference
/-- info: 'AgaveBlake3Reference.every_legal_portable_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms every_legal_portable_trace

end AgaveBlake3Reference
