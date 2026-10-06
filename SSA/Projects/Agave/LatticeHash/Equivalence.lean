/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.Compression
import SSA.Projects.Agave.LatticeHash.BatchControl
import SSA.Projects.Agave.LatticeHash.TransposeReduction
import SSA.Projects.Agave.LatticeHash.Staging

/-!
Concrete composition of the manually transcribed Agave lattice-hash models.
The one-chunk oracle is byte-level BLAKE3: exact IV, little-endian loads,
seven rounds, chunk flags, and 32 root output blocks decoded as 1024 u16s.
The batched program uses lane compression, the checked AVX transposes, the
early-exit/masked control loop, and wrapping u16 reduction. Long messages use
one common serial fallback supplied as data, with no correctness premise.
This is a theorem about these Lean semantic models, not Rust extraction or a
compiler/machine-code verification theorem.
-/
namespace AgaveConcrete

abbrev Byte := BitVec 8
abbrev Word := BitVec 32
abbrev Message := List Byte
abbrev CV := Blake3Compression.CV Word
abbrev Value := AgaveStaging.Value

/-- BLAKE3's unkeyed initialization vector, in word order. -/
def iv : CV := fun i => (#v[
  0x6A09E667#32, 0xBB67AE85#32, 0x3C6EF372#32, 0xA54FF53A#32,
  0x510E527F#32, 0x9B05688C#32, 0x1F83D9AB#32, 0x5BE0CD19#32]).get i

/-- A list's live bytes followed by zero-filled storage. -/
def bytes (m : Message) (i : Nat) : Byte :=
  if h : i < m.length then m[i] else 0

theorem bytes_valid (m : Message) :
    AgaveBatchControl.ValidStaging m.length (AgaveBatchControl.paddedBytes m.length) (bytes m) (bytes m) := by
  refine ⟨Nat.le_refl _, fun _ _ => rfl, ?_⟩
  intro i hi _
  simp [bytes, Nat.not_lt.mpr hi]

/-- Exact little-endian u32 decoding of a 64-byte block. -/
def decodeBlock (b : AgaveBatchControl.Block) : Blake3Compression.State Word := fun w =>
  b ⟨4 * w.val + 3, by omega⟩ ++ b ⟨4 * w.val + 2, by omega⟩ ++
  b ⟨4 * w.val + 1, by omega⟩ ++ b ⟨4 * w.val, by omega⟩

def counter (lo hi : Nat) : Blake3Compression.Counter := BitVec.ofNat 64 (lo + 4294967296 * hi)

def compress : AgaveBatchControl.Compress CV := fun cv block lo hi size flags =>
  Blake3Compression.scalarCompressCV cv (decodeBlock block) (counter lo hi)
    (BitVec.ofNat 32 size) (BitVec.ofNat 32 flags)

/-- Flags already include ROOT at this interface (10 or 11). -/
def xof : AgaveBatchControl.Xof CV (Blake3Compression.State Word) := fun cv block lo hi size flags =>
  Blake3Compression.scalarCompress cv (decodeBlock block) (counter lo hi)
    (BitVec.ofNat 32 size) (BitVec.ofNat 32 flags)

def oneChunkWords (m : Message) (out : Fin 32) : Blake3Compression.State Word :=
  AgaveBatchControl.scalarXofAt compress xof iv (bytes m) m.length out

/-- Exact unkeyed one-chunk BLAKE3 XOF, interpreted as 1024 little-endian u16s.
    Its BLAKE3 interpretation applies to messages of length at most 1024. -/
def oneChunk (m : Message) : Value := fun i =>
  AgaveLattice.halfWord (oneChunkWords m ⟨i.val / 32, by omega⟩
    ⟨i.val % 32 / 2, by omega⟩) ⟨i.val % 2, by omega⟩

abbrev BatchState (n : Nat) := AgaveBatchControl.BatchState n CV

def cvVectors {n : Nat} (s : BatchState n) : Blake3Compression.CV (Blake3Compression.Lanes n) :=
  fun w lane => (s lane).cv w

/-- Decode each lane's current full block, then execute the input transpose.
    The zero offsets here are relative to the already selected full block. -/
def loaded {n : Nat} (perm : AgaveLattice.Matrix) (memory : Fin n → Nat → Byte)
    (s : BatchState n) : Blake3Compression.State (Blake3Compression.Lanes n) :=
  fun word lane => AgaveLattice.loadWords n perm
    (fun l w => if hl : l < n then
      if hw : w < 16 then
        decodeBlock (AgaveBatchControl.loadBlock (memory ⟨l, hl⟩) ((s ⟨l, hl⟩).off / 64)) ⟨w, hw⟩
      else 0
    else 0) (fun _ => 0) word lane

theorem loaded_project {n : Nat} (hn : 0 < n) {perm : AgaveLattice.Matrix}
    (hp : AgaveLattice.IsTranspose n perm) (memory : Fin n → Nat → Byte)
    (s : BatchState n) (lane : Fin n) :
    Blake3Compression.project (loaded perm memory s) lane =
      decodeBlock (AgaveBatchControl.loadBlock (memory lane) ((s lane).off / 64)) := by
  funext word
  unfold Blake3Compression.project loaded
  rw [AgaveLattice.loadWords_correct hn hp]
  simp [lane.isLt, word.isLt]

/-- The exact bit order produced by the AVX-512 mask-construction loop. -/
def activeBits (active : Fin 16 → Bool) : BitVec 16 :=
  (BitVec.ofBoolListLE (List.ofFn active)).cast (by simp)

theorem activeBits_get (active : Fin 16 → Bool) (i : Fin 16) :
    (activeBits active).getLsbD i = active i := by
  simp only [activeBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

/-- Source-level selection: AVX2 uses an all-zero/all-one VPBLENDVB mask;
    AVX-512 builds a k16 mask and applies VPBLENDMD. -/
def selectWord {n : Nat} (active : Fin n → Bool) (lane : Fin n)
    (ifActive ifInactive : Word) : Word :=
  if n = 8 then
    AgaveLattice.blendWord
      (if active lane then 0xffffffff#32 else 0#32) ifInactive ifActive
  else if hn : n = 16 then
    let a16 : Fin 16 → Bool := fun i => active ⟨i.val, by omega⟩
    if (AgaveLattice.mask16 (activeBits a16)).getLsbD lane then ifActive else ifInactive
  else if active lane then ifActive else ifInactive

theorem selectWord_eq {n : Nat} (active : Fin n → Bool) (lane : Fin n)
    (ifActive ifInactive : Word) :
    selectWord active lane ifActive ifInactive =
      if active lane then ifActive else ifInactive := by
  unfold selectWord
  split
  · exact AgaveLattice.avx2_mask_select _ _ _
  · split
    next hn =>
      subst n
      change (if (AgaveLattice.mask16 (activeBits active)).getLsbD lane
        then ifActive else ifInactive) = _
      rw [AgaveLattice.avx512_mask_select, activeBits_get]
    next => rfl

/-- Compute a lane-vector compression, select every CV word through the exact
    backend mask model, and advance only active offsets. -/
def simdStep {n : Nat} (perm : AgaveLattice.Matrix) (lengths : Fin n → Nat)
    (memory : Fin n → Nat → Byte) (s : BatchState n) : BatchState n :=
  let next := Blake3Compression.laneCompressCV (cvVectors s) (loaded perm memory s)
    (fun _ => counter 0 0)
    (fun l => BitVec.ofNat 32 (AgaveBatchControl.blockSize (lengths l) (s l).off))
    (fun l => BitVec.ofNat 32 (AgaveBatchControl.blockFlags (lengths l) (s l).off))
  let active : Fin n → Bool := fun l => decide ((s l).off + 64 < lengths l)
  fun l =>
    let cv := fun w => selectWord active l (next w l) ((s l).cv w)
    if active l then ⟨(s l).off + 64, cv⟩ else ⟨(s l).off, cv⟩

theorem simdStep_eq {n : Nat} (hn : 0 < n) {perm : AgaveLattice.Matrix}
    (hp : AgaveLattice.IsTranspose n perm) (lengths : Fin n → Nat)
    (memory : Fin n → Nat → Byte) (s : BatchState n) :
    simdStep perm lengths memory s = AgaveBatchControl.batchStep compress lengths memory s := by
  funext l
  unfold simdStep AgaveBatchControl.batchStep AgaveBatchControl.laneStep
  simp only [selectWord_eq]
  by_cases ha : (s l).off + 64 < lengths l
  · simp only [decide_eq_true ha, ↓reduceIte, Nat.not_le.mpr ha]
    congr 1
    funext w
    change Blake3Compression.project (Blake3Compression.laneCompressCV _ _ _ _ _) l w = _
    rw [Blake3Compression.laneCompressCV_project, loaded_project hn hp]
    rfl
  · have hi : lengths l ≤ (s l).off + 64 := by omega
    simp [decide_eq_false ha, hi]

def simdRun {n : Nat} (perm : AgaveLattice.Matrix) (lengths : Fin n → Nat)
    (memory : Fin n → Nat → Byte) : Nat → BatchState n → Option (BatchState n)
  | 0, s => if AgaveBatchControl.AllDone lengths s then some s else none
  | fuel + 1, s => if AgaveBatchControl.AllDone lengths s then some s else
      simdRun perm lengths memory fuel (simdStep perm lengths memory s)

theorem simdRun_eq {n : Nat} (hn : 0 < n) {perm : AgaveLattice.Matrix}
    (hp : AgaveLattice.IsTranspose n perm) (lengths : Fin n → Nat)
    (memory : Fin n → Nat → Byte) (fuel : Nat) (s : BatchState n) :
    simdRun perm lengths memory fuel s = AgaveBatchControl.batchRun compress lengths memory fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [simdRun, AgaveBatchControl.batchRun]
    split
    · rfl
    · rw [ih, simdStep_eq hn hp]

/-- All sixteen feed-forward words for one XOF output block in every lane. -/
def simdXofAt {n : Nat} (perm : AgaveLattice.Matrix) (lengths : Fin n → Nat)
    (memory : Fin n → Nat → Byte) (s : BatchState n)
    (out : Fin 32) : Blake3Compression.State (Blake3Compression.Lanes n) :=
  Blake3Compression.laneCompress (cvVectors s) (loaded perm memory s)
    (fun _ => counter out.val 0)
    (fun l => BitVec.ofNat 32 (AgaveBatchControl.blockSize (lengths l) (s l).off))
    (fun l => BitVec.ofNat 32 (AgaveBatchControl.blockFlags (lengths l) (s l).off))

theorem simdXofAt_project {n : Nat} (hn : 0 < n) {perm : AgaveLattice.Matrix}
    (hp : AgaveLattice.IsTranspose n perm) (lengths : Fin n → Nat)
    (memory : Fin n → Nat → Byte) (s : BatchState n)
    (out : Fin 32) (lane : Fin n) :
    Blake3Compression.project (simdXofAt perm lengths memory s out) lane =
      AgaveBatchControl.batchXofAt xof lengths memory s out lane := by
  unfold simdXofAt
  rw [Blake3Compression.laneCompress_project, loaded_project hn hp]
  have hc := AgaveBatchControl.xof_counter_words out
  simp only [AgaveBatchControl.batchXofAt, AgaveBatchControl.batchRootDescriptor, hc.2.1, hc.2.2]
  rfl

def rootState {n : Nat} (perm : AgaveLattice.Matrix) (ms : Fin n → Message) : BatchState n :=
  (simdRun perm (fun l => (ms l).length) (fun l => bytes (ms l)) 15
    (fun _ => ⟨0, iv⟩)).getD (fun _ => ⟨0, iv⟩)

theorem rootState_eq {n : Nat} (hn : 0 < n) {perm : AgaveLattice.Matrix}
    (hp : AgaveLattice.IsTranspose n perm) (ms : Fin n → Message)
    (hm : ∀ l, (ms l).length ≤ 1024) :
    rootState perm ms = fun l => AgaveBatchControl.scalarRootState compress iv (bytes (ms l)) (ms l).length := by
  unfold rootState
  rw [simdRun_eq hn hp,
    AgaveBatchControl.compress_batch_control_equiv compress iv hm (fun l => bytes_valid (ms l))]
  rfl

def batchXofWords {n : Nat} (perm : AgaveLattice.Matrix) (ms : Fin n → Message) : AgaveLattice.XofWords :=
  fun lane out word => if hl : lane < n then if ho : out < 32 then if hw : word < 16 then
    simdXofAt perm (fun l => (ms l).length) (fun l => bytes (ms l))
      (rootState perm ms) ⟨out, ho⟩ ⟨word, hw⟩ ⟨lane, hl⟩
    else 0 else 0 else 0

theorem batchXofWords_correct {n : Nat} (hn : 0 < n) {perm : AgaveLattice.Matrix}
    (hp : AgaveLattice.IsTranspose n perm) (ms : Fin n → Message)
    (hm : ∀ l, (ms l).length ≤ 1024) (lane : Fin n) (out : Fin 32) (word : Fin 16) :
    batchXofWords perm ms lane out word = oneChunkWords (ms lane) out word := by
  simp only [batchXofWords, lane.isLt, out.isLt, word.isLt, ↓reduceDIte]
  change Blake3Compression.project (simdXofAt _ _ _ _ _) lane word = _
  rw [simdXofAt_project hn hp, rootState_eq hn hp ms hm,
    AgaveBatchControl.root_xof_equiv compress xof iv (fun l => bytes_valid (ms l))]
  rfl

/-- Extend finite accumulator storage only to satisfy the reduction interface. -/
def extendAcc (a : Value) (i : Nat) : BitVec 16 :=
  if hi : i < 1024 then a ⟨i, hi⟩ else 0

def simdUpdate {n : Nat} (hn : 0 < n) (perm : AgaveLattice.Matrix)
    (ms : Fin n → Message) (a : Value) : Value := fun i =>
  AgaveLattice.simdLtHash n hn perm (batchXofWords perm ms) (extendAcc a) i

theorem value_foldl_apply {α : Type} (xs : List α) (f : α → Value)
    (a : Value) (i : Fin 1024) :
    (xs.foldl (fun z m => AgaveStaging.plus z (f m)) a) i =
      xs.foldl (fun z m => z + f m i) (a i) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih, AgaveStaging.plus]

theorem simdUpdate_eq_fold {n : Nat} (hn : 0 < n) {perm : AgaveLattice.Matrix}
    (hp : AgaveLattice.IsTranspose n perm) (ms : Fin n → Message)
    (hm : ∀ l, (ms l).length ≤ 1024) (a : Value) :
    simdUpdate hn perm ms a = (List.finRange n).foldl
      (fun z lane => AgaveStaging.plus z (oneChunk (ms lane))) a := by
  funext i
  unfold simdUpdate
  rw [AgaveLattice.simdLtHash_eq_scalarLtHash hn hp,
    AgaveLattice.scalarLtHash_apply, value_foldl_apply]
  have hword (lane : Fin n) :
      AgaveLattice.scalarMessage (batchXofWords perm ms) lane i = oneChunk (ms lane) i := by
    unfold AgaveLattice.scalarMessage oneChunk
    rw [batchXofWords_correct hn hp ms hm lane ⟨i.val / 32, by omega⟩
      ⟨i.val % 32 / 2, by omega⟩]
  simp only [hword, extendAcc, i.isLt, ↓reduceDIte]

/-- Lossless adapter for the original staging model's UInt8 messages. -/
def toBytes (m : AgaveStaging.Message) : Message := m.map UInt8.toBitVec

@[simp] theorem toBytes_length (m : AgaveStaging.Message) : (toBytes m).length = m.length := by
  simp [toBytes]

/-- Shared scalar semantics. Only the long-message serial branch is a parameter. -/
def scalarHash (longHash : Message → Value) (m : Message) : Value :=
  if m.length ≤ 1024 then oneChunk m else longHash m

def hash (longHash : Message → Value) (m : AgaveStaging.Message) : Value :=
  scalarHash longHash (toBytes m)

theorem hash_short (longHash : Message → Value) (m : AgaveStaging.Message)
    (hm : m.length ≤ 1024) : hash longHash m = oneChunk (toBytes m) := by
  simp [hash, scalarHash, hm]

theorem hash_long (longHash : Message → Value) (m : AgaveStaging.Message)
    (hm : 1024 < m.length) : hash longHash m = longHash (toBytes m) := by
  simp [hash, scalarHash, Nat.not_le.mpr hm]

def messagesOf {α : Type} {n : Nat} (ms : List α) (h : ms.length = n) : Fin n → α :=
  fun i => ms[i.val]'(by omega)

theorem messagesOf_mem {α : Type} {n : Nat} (ms : List α) (h : ms.length = n) (i : Fin n) :
    messagesOf ms h i ∈ ms := List.mem_of_getElem rfl

theorem messagesOf_map {α : Type} {n : Nat} (ms : List α) (h : ms.length = n) :
    (List.finRange n).map (messagesOf ms h) = ms := by
  subst n
  simp [messagesOf, List.finRange, Function.comp_def]

/-- A full concrete SIMD batch. Ill-sized calls are outside Backend's contract. -/
def run (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix)
    (ms : List AgaveStaging.Message) (a : Value) : Value :=
  if h : ms.length = n then simdUpdate hn perm (fun l => toBytes (messagesOf ms h l)) a
  else a

theorem run_correct (longHash : Message → Value) (n : Nat) (hn : 0 < n)
    (perm : AgaveLattice.Matrix) (hp : AgaveLattice.IsTranspose n perm)
    (ms : List AgaveStaging.Message) (a : Value) (hlen : ms.length = n)
    (hm : ∀ m ∈ ms, m.length ≤ 1024) :
    run n hn perm ms a = AgaveStaging.plus a (AgaveStaging.scalar (hash longHash) ms) := by
  unfold run
  rw [dite_eq_left hlen]
  have hshort (l : Fin n) : (messagesOf ms hlen l).length ≤ 1024 :=
    hm _ (messagesOf_mem ms hlen l)
  rw [simdUpdate_eq_fold hn hp _ (fun l => by simpa using hshort l)]
  have hh (l : Fin n) : oneChunk (toBytes (messagesOf ms hlen l)) =
      hash longHash (messagesOf ms hlen l) := (hash_short longHash _ (hshort l)).symm
  simp only [hh]
  rw [← List.foldl_map (f := messagesOf ms hlen)
    (g := fun z m => AgaveStaging.plus z (hash longHash m)),
    messagesOf_map, AgaveStaging.scalar_foldl]

/-- The backend correctness field is discharged by the composition theorem. -/
def backend (longHash : Message → Value) (n : Nat) (hn : 0 < n)
    (perm : AgaveLattice.Matrix) (hp : AgaveLattice.IsTranspose n perm) :
    AgaveStaging.Backend (hash longHash) n where
  run := run n hn perm
  correct := run_correct longHash n hn perm hp

def avx2 (longHash : Message → Value) : AgaveStaging.Backend (hash longHash) 8 :=
  backend longHash 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels)
    AgaveLattice.avx2_isTranspose

def avx512 (longHash : Message → Value) : AgaveStaging.Backend (hash longHash) 16 :=
  backend longHash 16 (by decide) (AgaveLattice.transpose16 AgaveLattice.labels)
    AgaveLattice.avx512_isTranspose

/-- The width-one path always flushes through the shared serial implementation.
    Its `run` field is included for the common interface, but width one never
    selects the full-SIMD branch in `AgaveStaging.flush`. -/
def reference (longHash : Message → Value) : AgaveStaging.Backend (hash longHash) 1 where
  run ms a := AgaveStaging.plus a (AgaveStaging.scalar (hash longHash) ms)
  correct := by intro ms a _ _; rfl

/-- Every idle observation of the concrete width-one reference model. -/
theorem reference_observational_equivalence (longHash : Message → Value)
    {s : AgaveStaging.Impl} {r : AgaveStaging.Spec}
    (trace : AgaveStaging.Run (hash longHash) 1 (reference longHash) s r)
    (idle : r.active = none) :
    (AgaveStaging.take (hash longHash) 1 (reference longHash) s).1 =
      AgaveStaging.scalar (hash longHash) r.committed :=
  AgaveStaging.observational_equivalence _ _ _ (by decide) trace idle

/-- Every idle observation of the concrete width-eight normal-lifecycle model. -/
theorem avx2_observational_equivalence (longHash : Message → Value)
    {s : AgaveStaging.Impl} {r : AgaveStaging.Spec}
    (trace : AgaveStaging.Run (hash longHash) 8 (avx2 longHash) s r)
    (idle : r.active = none) :
    (AgaveStaging.take (hash longHash) 8 (avx2 longHash) s).1 =
      AgaveStaging.scalar (hash longHash) r.committed :=
  AgaveStaging.observational_equivalence _ _ _ (by decide) trace idle

/-- Every idle observation of the concrete width-sixteen normal-lifecycle model. -/
theorem avx512_observational_equivalence (longHash : Message → Value)
    {s : AgaveStaging.Impl} {r : AgaveStaging.Spec}
    (trace : AgaveStaging.Run (hash longHash) 16 (avx512 longHash) s r)
    (idle : r.active = none) :
    (AgaveStaging.take (hash longHash) 16 (avx512 longHash) s).1 =
      AgaveStaging.scalar (hash longHash) r.committed :=
  AgaveStaging.observational_equivalence _ _ _ (by decide) trace idle

/-- Same committed messages, arbitrary fragments/discards/drains/reuses and lengths.
    The only propositions supplied by clients describe legal lifecycle traces. -/
theorem avx2_eq_avx512 (longHash : Message → Value)
    {s8 s16 : AgaveStaging.Impl} {r : AgaveStaging.Spec}
    (trace8 : AgaveStaging.Run (hash longHash) 8 (avx2 longHash) s8 r)
    (trace16 : AgaveStaging.Run (hash longHash) 16 (avx512 longHash) s16 r)
    (idle : r.active = none) :
    (AgaveStaging.take (hash longHash) 8 (avx2 longHash) s8).1 =
      (AgaveStaging.take (hash longHash) 16 (avx512 longHash) s16).1 := by
  rw [avx2_observational_equivalence longHash trace8 idle,
    avx512_observational_equivalence longHash trace16 idle]

/-- The public result is identical for the reference, AVX2, and AVX-512
    implementations after any normally bracketed builder trace that represents
    the same committed messages. The trace type has no constructor for leaking
    an unfinished builder with `mem::forget`. -/
theorem reference_eq_avx2_eq_avx512 (longHash : Message → Value)
    {s1 s8 s16 : AgaveStaging.Impl} {r : AgaveStaging.Spec}
    (trace1 : AgaveStaging.Run (hash longHash) 1 (reference longHash) s1 r)
    (trace8 : AgaveStaging.Run (hash longHash) 8 (avx2 longHash) s8 r)
    (trace16 : AgaveStaging.Run (hash longHash) 16 (avx512 longHash) s16 r)
    (idle : r.active = none) :
    let referenceResult := (AgaveStaging.take (hash longHash) 1 (reference longHash) s1).1
    let avx2Result := (AgaveStaging.take (hash longHash) 8 (avx2 longHash) s8).1
    let avx512Result := (AgaveStaging.take (hash longHash) 16 (avx512 longHash) s16).1
    referenceResult = avx2Result ∧ avx2Result = avx512Result := by
  dsimp only
  rw [reference_observational_equivalence longHash trace1 idle,
    avx2_observational_equivalence longHash trace8 idle,
    avx512_observational_equivalence longHash trace16 idle]
  exact ⟨rfl, rfl⟩

end AgaveConcrete
