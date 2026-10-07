import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold

/-! Pure streaming invariant for Firedancer SHA-512. The state contains only
the chaining words, live buffer bytes and 128-bit counter observed in the C
context. Execution refinement is intentionally separate from these equations.
In particular, no digest or compression correctness premise occurs here. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.SHA512
open Agave.Ed25519.Verifier.Execution.Challenge

def complete (bytes : Bytes) : Bytes := bytes.take (128 * (bytes.length / 128))
def pending (bytes : Bytes) : Bytes := bytes.drop (128 * (bytes.length / 128))

theorem partition (bytes : Bytes) : complete bytes ++ pending bytes = bytes :=
  List.take_append_drop _ _

@[simp] theorem complete_length (bytes : Bytes) :
    (complete bytes).length = 128 * (bytes.length / 128) := by
  simp only [complete, List.length_take]
  exact Nat.min_eq_left (by omega)

@[simp] theorem complete_whole (bytes : Bytes) : (complete bytes).length % 128 = 0 := by
  rw [complete_length]
  omega

@[simp] theorem pending_length (bytes : Bytes) :
    (pending bytes).length = bytes.length % 128 := by
  simp only [pending, List.length_drop]
  omega

theorem pending_bound (bytes : Bytes) : (pending bytes).length < 128 := by
  rw [pending_length]
  omega

structure Context where
  chain : BitVec 512
  buffer : Bytes
  bitCount : BitVec 128

def initial : Context := ⟨initialWords, [], 0⟩

/-- A chunk transition compresses all complete buffered blocks, leaving the
remaining suffix untouched. Counter arithmetic is explicitly modulo 2^128. -/
def append (s : Context) (chunk : Bytes) : Context :=
  ⟨Spec.run s.chain (complete (s.buffer ++ chunk)),
   pending (s.buffer ++ chunk), s.bitCount + BitVec.ofNat 128 (8 * chunk.length)⟩

/-- The completed prefix is a ghost witness, not stored or recovered by the
implementation. Equality of the original bytes prevents reencoding R or A. -/
def Represents (s : Context) (message : Bytes) : Prop :=
  ∃ completed,
    completed ++ s.buffer = message ∧
    completed.length % 128 = 0 ∧ s.buffer.length < 128 ∧
    s.chain = Spec.run initialWords completed ∧
    s.bitCount = BitVec.ofNat 128 (8 * message.length)

theorem initial_represents : Represents initial [] := by
  refine ⟨[], rfl, by decide, by decide, ?_, rfl⟩
  simp [initial]

theorem append_represents (s : Context) (message chunk : Bytes)
    (h : Represents s message) : Represents (append s chunk) (message ++ chunk) := by
  obtain ⟨completed, hinput, hwhole, hbound, hchain, hcounter⟩ := h
  refine ⟨completed ++ complete (s.buffer ++ chunk), ?_, ?_, pending_bound _, ?_, ?_⟩
  · change (completed ++ complete (s.buffer ++ chunk)) ++ pending (s.buffer ++ chunk) = _
    rw [List.append_assoc, partition, ← List.append_assoc, hinput]
  · rw [List.length_append, Nat.add_mod, hwhole, complete_whole]
  · change Spec.run s.chain (complete (s.buffer ++ chunk)) = _
    rw [Spec.run_append _ _ _ hwhole, hchain]
  · change s.bitCount + BitVec.ofNat 128 (8 * chunk.length) = _
    rw [hcounter, ← BitVec.ofNat_add]
    congr 1
    simp [List.length_append, Nat.mul_add]

/-- Finalization reads this counter directly; no unbounded natural counter is
silently introduced into the machine observation. -/
def counterBytes (count : BitVec 128) : Bytes :=
  List.ofFn fun i : Fin 16 => count.extractLsb' (8 * (15 - i.val)) 8

@[simp] theorem counterBytes_length (count : BitVec 128) :
    (counterBytes count).length = 16 := by simp [counterBytes]

theorem counterBytes_ofNat (n : Nat) :
    counterBytes (BitVec.ofNat 128 (8 * n)) = lengthField n := rfl

/-- Exact one/two-block byte strings built by the C finalizer. -/
def finishBlocks (s : Context) : List Bytes :=
  if s.buffer.length < 112 then
    [s.buffer ++ [128] ++ List.replicate (111 - s.buffer.length) 0 ++ counterBytes s.bitCount]
  else
    [s.buffer ++ [128] ++ List.replicate (127 - s.buffer.length) 0,
     List.replicate 112 0 ++ counterBytes s.bitCount]

def finish (s : Context) : BitVec 512 :=
  serialize ((finishBlocks s).foldl Spec.run s.chain)

theorem finishBlocks_eq (s : Context) (message : Bytes) (h : Represents s message) :
    finishBlocks s = finalBlocks s.buffer message.length := by
  obtain ⟨_, _, _, _, _, hcounter⟩ := h
  simp only [finishBlocks, finalBlocks, onlyPaddingBlock, firstPaddingBlock,
    lastPaddingBlock, hcounter, counterBytes_ofNat]

theorem finishBlocks_whole (s : Context) (message : Bytes) (h : Represents s message) :
    ∀ block ∈ finishBlocks s, block.length = 128 := by
  rw [finishBlocks_eq s message h]
  obtain ⟨_, _, _, hbound, _, _⟩ := h
  exact finalBlocks_whole _ _ hbound

/-- The mathematical streaming model produces the shared concrete digest
for every transcript, with no size bound or assumed digest equality. -/
theorem finish_eq_digest (s : Context) (message : Bytes) (h : Represents s message) :
    finish s = digest Spec.compression message := by
  have hblocks := finishBlocks_eq s message h
  obtain ⟨completed, hinput, hwhole, hbound, hchain, _⟩ := h
  have hlen : message.length = completed.length + s.buffer.length := by
    rw [← hinput, List.length_append]
  unfold finish
  rw [hblocks, hchain, hlen]
  exact (finalize_eq_digest Spec.compression completed s.buffer hwhole hbound).trans
    (congrArg (digest Spec.compression) hinput)

def appendChunks (s : Context) (chunks : List Bytes) : Context := chunks.foldl append s

theorem appendChunks_represents (s : Context) (message : Bytes) (chunks : List Bytes)
    (h : Represents s message) :
    Represents (appendChunks s chunks) (message ++ chunks.flatten) := by
  induction chunks generalizing s message with
  | nil => simpa [appendChunks] using h
  | cons chunk chunks ih =>
    simpa only [appendChunks, List.foldl_cons, List.flatten_cons, List.append_assoc] using
      ih (append s chunk) (message ++ chunk) (append_represents s message chunk h)

theorem finish_appendChunks (chunks : List Bytes) :
    finish (appendChunks initial chunks) = digest Spec.compression chunks.flatten := by
  apply finish_eq_digest
  simpa using appendChunks_represents initial [] chunks initial_represents

/-- Digest equality is independent of where callers split the input stream. -/
theorem chunking_invariant (xs ys : List Bytes) (h : xs.flatten = ys.flatten) :
    finish (appendChunks initial xs) = finish (appendChunks initial ys) := by
  rw [finish_appendChunks, finish_appendChunks, h]

/-- The verifier's three updates preserve R || A || M in address order. -/
theorem transcript_represents (r a : BitVec 256) (message : Bytes) :
    Represents (append (append (append initial (bytesOf (n := 32) r)) (bytesOf (n := 32) a)) message)
      (transcript r a message) := by
  simpa [transcript] using append_represents _ _ message
    (append_represents _ _ (bytesOf (n := 32) a)
      (append_represents _ _ (bytesOf (n := 32) r) initial_represents))

theorem finish_transcript (r a : BitVec 256) (message : Bytes) :
    finish (append (append (append initial (bytesOf (n := 32) r)) (bytesOf (n := 32) a)) message) =
      digest Spec.compression (transcript r a message) :=
  finish_eq_digest _ _ (transcript_represents r a message)

end Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec
