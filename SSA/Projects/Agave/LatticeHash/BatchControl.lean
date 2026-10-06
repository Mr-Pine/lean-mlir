/- Released under Apache 2.0 license as described in the file LICENSE. -/
import Std

/-!
Control-flow refinement of Agave `lattice-hash/src/batch/arch.rs::compress_batch`.
Pinned toolchain: leanprover/lean4:nightly-2026-09-16.

This is a manually transcribed, parametric control-layer model. The compression
primitive and XOF feed-forward are arbitrary pure functions, used identically
by the batched and independent scalar programs. This file does not assert that
Rust/LLVM/x86 executes this model or that its abstract primitive is BLAKE3.
No theorem assumes the desired end-to-end equality.
-/
namespace AgaveBatchControl

abbrev Byte := BitVec 8
abbrev Block := Fin 64 → Byte

def rootIndex (len : Nat) : Nat := (len - 1) / 64
def paddedBytes (len : Nat) : Nat := 64 * (rootIndex len + 1)

theorem rootIndex_bounds (len : Nat) :
    64 * rootIndex len ≤ len ∧ len ≤ 64 * rootIndex len + 64 := by
  unfold rootIndex
  omega

theorem rootIndex_lt16 (len : Nat) (h : len ≤ 1024) : rootIndex len < 16 := by
  unfold rootIndex
  omega

theorem rootIndex_zero_iff (len : Nat) : rootIndex len = 0 ↔ len ≤ 64 := by
  unfold rootIndex
  omega

theorem rootIndex_before_last (len j : Nat) :
    64 * j + 64 < len ↔ j < rootIndex len := by
  unfold rootIndex
  omega

/-- Exactly the bytes that the control algorithm may read must be allocated;
    live bytes match the message and bytes after its end are zero. In particular,
    the empty message requires one allocated, zero-filled 64-byte block. -/
structure ValidStaging (len capacity : Nat) (message memory : Nat → Byte) : Prop where
  allocated : paddedBytes len ≤ capacity
  live : ∀ i, i < len → memory i = message i
  padding : ∀ i, len ≤ i → i < paddedBytes len → memory i = 0

def loadBlock (memory : Nat → Byte) (j : Nat) : Block :=
  fun w => memory (64 * j + w.val)

/-- Scalar processing forms each final block directly from message bytes. -/
def scalarBlock (message : Nat → Byte) (len j : Nat) : Block :=
  fun w => if 64 * j + w.val < len then message (64 * j + w.val) else 0

theorem load_in_bounds {len capacity : Nat} {message memory : Nat → Byte}
    (h : ValidStaging len capacity message memory) {j : Nat} (hj : j ≤ rootIndex len)
    (w : Fin 64) : 64 * j + w.val < capacity := by
  have hw := w.isLt
  have ha := h.allocated
  unfold paddedBytes at ha
  omega

theorem load_eq_scalarBlock {len capacity : Nat} {message memory : Nat → Byte}
    (h : ValidStaging len capacity message memory) {j : Nat} (hj : j ≤ rootIndex len) :
    loadBlock memory j = scalarBlock message len j := by
  funext w
  simp only [loadBlock, scalarBlock]
  split
  next hl => exact h.live _ hl
  next hl =>
    apply h.padding
    · omega
    · have hw := w.isLt
      unfold paddedBytes
      omega

theorem empty_staging_requires_block {capacity : Nat} {message memory : Nat → Byte}
    (h : ValidStaging 0 capacity message memory) :
    64 ≤ capacity ∧ ∀ i, i < 64 → memory i = 0 := by
  constructor
  · simpa [paddedBytes, rootIndex] using h.allocated
  · intro i hi
    apply h.padding i (Nat.zero_le i)
    simpa [paddedBytes, rootIndex] using hi

/-- Numeric values of the Rust bit flags: ROOT | CHUNK_END = 10, CHUNK_START = 1. -/
def blockFlags (len off : Nat) : Nat :=
  (if len ≤ off + 64 then 10 else 0) + (if off = 0 then 1 else 0)

def blockSize (len off : Nat) : Nat := min (len - off) 64

def scalarRootFlags (len : Nat) : Nat := if len ≤ 64 then 11 else 10

def scalarRootSize (len : Nat) : Nat := if len = 0 then 0 else (len - 1) % 64 + 1

theorem active_flags (len j : Nat) (ha : j < rootIndex len) :
    blockFlags len (64 * j) = if j = 0 then 1 else 0 := by
  have h := (rootIndex_before_last len j).mpr ha
  simp only [blockFlags]
  split <;> split <;> split <;> omega

theorem active_size (len j : Nat) (ha : j < rootIndex len) :
    blockSize len (64 * j) = 64 := by
  have h := (rootIndex_before_last len j).mpr ha
  unfold blockSize
  omega

theorem root_flags (len : Nat) :
    blockFlags len (64 * rootIndex len) = scalarRootFlags len := by
  have hb := rootIndex_bounds len
  have hz := rootIndex_zero_iff len
  simp only [blockFlags, scalarRootFlags]
  split <;> split <;> split <;> omega

theorem root_size (len : Nat) :
    blockSize len (64 * rootIndex len) = scalarRootSize len := by
  unfold blockSize scalarRootSize rootIndex
  split <;> omega

theorem root_size_bounds (len : Nat) :
    scalarRootSize len ≤ 64 ∧ (scalarRootSize len = 0 ↔ len = 0) := by
  unfold scalarRootSize
  split <;> omega

structure LaneState (CV : Type) where
  off : Nat
  cv : CV
  deriving DecidableEq

/-- Abstract compression with (low counter, high counter, block size, flags).
    Its return value is the low-eight-word chaining-value feed-forward. -/
abbrev Compress (CV : Type) := CV → Block → Nat → Nat → Nat → Nat → CV

/-- Scalar message compression: process exactly j complete non-root blocks. -/
def scalarPrefix {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Nat → Byte) (len : Nat) : Nat → CV
  | 0 => iv
  | j + 1 => compress (scalarPrefix compress iv message len j)
      (scalarBlock message len j) 0 0 64 (if j = 0 then 1 else 0)

/-- One batched iteration's lane projection. Inactive lanes preserve both
    their CV and offset; active lanes compress and advance by exactly 64. -/
def laneStep {CV : Type} (compress : Compress CV) (len : Nat)
    (memory : Nat → Byte) (s : LaneState CV) : LaneState CV :=
  if len ≤ s.off + 64 then s else
    ⟨s.off + 64, compress s.cv (loadBlock memory (s.off / 64))
      0 0 (blockSize len s.off) (blockFlags len s.off)⟩

def stateAt {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Nat → Byte) (len t : Nat) : LaneState CV :=
  ⟨64 * min t (rootIndex len),
    scalarPrefix compress iv message len (min t (rootIndex len))⟩

theorem stateAt_zero {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Nat → Byte) (len : Nat) :
    stateAt compress iv message len 0 = ⟨0, iv⟩ := by
  simp [stateAt, scalarPrefix]

theorem active_iff_before_root (len t : Nat) :
    ¬len ≤ 64 * min t (rootIndex len) + 64 ↔ t < rootIndex len := by
  have h := rootIndex_before_last len (min t (rootIndex len))
  omega

theorem stateAt_offset_le_len {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Nat → Byte) (len t : Nat) :
    (stateAt compress iv message len t).off ≤ len := by
  have hb := rootIndex_bounds len
  simp only [stateAt]
  omega

theorem laneStep_preserves_inactive {CV : Type} (compress : Compress CV)
    (len : Nat) (memory : Nat → Byte) (s : LaneState CV) (h : len ≤ s.off + 64) :
    laneStep compress len memory s = s := by
  simp [laneStep, h]

theorem laneStep_advances_active {CV : Type} (compress : Compress CV)
    (len : Nat) (memory : Nat → Byte) (s : LaneState CV) (h : s.off + 64 < len) :
    (laneStep compress len memory s).off = s.off + 64 ∧
    (laneStep compress len memory s).cv = compress s.cv
      (loadBlock memory (s.off / 64)) 0 0 (blockSize len s.off) (blockFlags len s.off) := by
  simp [laneStep, Nat.not_le.mpr h]

theorem laneStep_stateAt {CV : Type} (compress : Compress CV) (iv : CV)
    {len capacity : Nat} {message memory : Nat → Byte}
    (hstage : ValidStaging len capacity message memory) (t : Nat) :
    laneStep compress len memory (stateAt compress iv message len t) =
      stateAt compress iv message len (t + 1) := by
  by_cases ha : t < rootIndex len
  · have ht : min t (rootIndex len) = t := by omega
    have ht1 : min (t + 1) (rootIndex len) = t + 1 := by omega
    have hn : ¬len ≤ 64 * t + 64 := by
      have := (rootIndex_before_last len t).mpr ha
      omega
    have hload := load_eq_scalarBlock hstage (Nat.le_of_lt ha)
    simp only [stateAt, ht, ht1, laneStep, hn, ↓reduceIte,
      active_flags len t ha, active_size len t ha, Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
    rw [hload]
    simp [scalarPrefix, Nat.mul_add]
  · have ht : min t (rootIndex len) = rootIndex len := by omega
    have ht1 : min (t + 1) (rootIndex len) = rootIndex len := by omega
    have hf := (rootIndex_bounds len).2
    simp [stateAt, ht, ht1, laneStep, hf]


abbrev BatchState (n : Nat) (CV : Type) := Fin n → LaneState CV

def batchStep {n : Nat} {CV : Type} (compress : Compress CV)
    (lengths : Fin n → Nat) (memory : Fin n → Nat → Byte)
    (s : BatchState n CV) : BatchState n CV :=
  fun l => laneStep compress (lengths l) (memory l) (s l)

def AllDone {n : Nat} {CV : Type} (lengths : Fin n → Nat)
    (s : BatchState n CV) : Prop := ∀ l, lengths l ≤ (s l).off + 64

instance {n : Nat} {CV : Type} (lengths : Fin n → Nat)
    (s : BatchState n CV) : Decidable (AllDone lengths s) := by
  unfold AllDone
  infer_instance

/-- The Rust early-exit loop, with fuel measuring permitted CV updates.
    Exhaustion is observable (`none`), so termination is part of the theorem. -/
def batchRun {n : Nat} {CV : Type} (compress : Compress CV)
    (lengths : Fin n → Nat) (memory : Fin n → Nat → Byte) :
    Nat → BatchState n CV → Option (BatchState n CV)
  | 0, s => if AllDone lengths s then some s else none
  | fuel + 1, s => if AllDone lengths s then some s else
      batchRun compress lengths memory fuel (batchStep compress lengths memory s)

def batchStateAt {n : Nat} {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Fin n → Nat → Byte) (lengths : Fin n → Nat) (t : Nat) : BatchState n CV :=
  fun l => stateAt compress iv (message l) (lengths l) t

/-- Independent scalar processing never sees the other lanes. -/
def scalarRootState {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Nat → Byte) (len : Nat) : LaneState CV :=
  ⟨64 * rootIndex len, scalarPrefix compress iv message len (rootIndex len)⟩

theorem batchStep_stateAt {n : Nat} {CV : Type} (compress : Compress CV) (iv : CV)
    {lengths capacity : Fin n → Nat} {message memory : Fin n → Nat → Byte}
    (hstage : ∀ l, ValidStaging (lengths l) (capacity l) (message l) (memory l)) (t : Nat) :
    batchStep compress lengths memory (batchStateAt compress iv message lengths t) =
      batchStateAt compress iv message lengths (t + 1) := by
  funext l
  exact laneStep_stateAt compress iv (hstage l) t

theorem allDone_stateAt_iff {n : Nat} {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Fin n → Nat → Byte) (lengths : Fin n → Nat) (t : Nat) :
    AllDone lengths (batchStateAt compress iv message lengths t) ↔
      ∀ l, rootIndex (lengths l) ≤ t := by
  simp only [AllDone, batchStateAt, stateAt]
  constructor
  · intro h l
    have hh := active_iff_before_root (lengths l) t
    have hl := h l
    omega
  · intro h l
    have hh := active_iff_before_root (lengths l) t
    have hl := h l
    omega

theorem done_state_eq_scalar {n : Nat} {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Fin n → Nat → Byte) (lengths : Fin n → Nat) (t : Nat)
    (hdone : AllDone lengths (batchStateAt compress iv message lengths t)) :
    batchStateAt compress iv message lengths t =
      fun l => scalarRootState compress iv (message l) (lengths l) := by
  have h := (allDone_stateAt_iff compress iv message lengths t).mp hdone
  funext l
  have hm : min t (rootIndex (lengths l)) = rootIndex (lengths l) := by
    have := h l
    omega
  simp [batchStateAt, stateAt, scalarRootState, hm]

theorem run_from_stateAt {n : Nat} {CV : Type} (compress : Compress CV) (iv : CV)
    {lengths capacity : Fin n → Nat} {message memory : Fin n → Nat → Byte}
    (hstage : ∀ l, ValidStaging (lengths l) (capacity l) (message l) (memory l))
    (fuel t : Nat) (hbound : ∀ l, rootIndex (lengths l) ≤ t + fuel) :
    batchRun compress lengths memory fuel (batchStateAt compress iv message lengths t) =
      some (fun l => scalarRootState compress iv (message l) (lengths l)) := by
  induction fuel generalizing t with
  | zero =>
    have hd : AllDone lengths (batchStateAt compress iv message lengths t) :=
      (allDone_stateAt_iff compress iv message lengths t).mpr (by simpa using hbound)
    simp only [batchRun, hd, ↓reduceIte]
    exact congrArg some (done_state_eq_scalar compress iv message lengths t hd)
  | succ fuel ih =>
    by_cases hd : AllDone lengths (batchStateAt compress iv message lengths t)
    · simp only [batchRun, hd, ↓reduceIte]
      exact congrArg some (done_state_eq_scalar compress iv message lengths t hd)
    · simp only [batchRun, hd, ↓reduceIte]
      rw [batchStep_stateAt compress iv hstage]
      apply ih
      intro l
      have := hbound l
      omega

/-- Main control refinement: for every batch width and every mixture of lengths
    0..1024, the actual masked early-exit control loop terminates after at most
    fifteen CV updates and returns each independent scalar prefix at its root. -/
theorem compress_batch_control_equiv {n : Nat} {CV : Type}
    (compress : Compress CV) (iv : CV)
    {lengths capacity : Fin n → Nat} {message memory : Fin n → Nat → Byte}
    (hlengths : ∀ l, lengths l ≤ 1024)
    (hstage : ∀ l, ValidStaging (lengths l) (capacity l) (message l) (memory l)) :
    batchRun compress lengths memory 15 (fun _ => ⟨0, iv⟩) =
      some (fun l => scalarRootState compress iv (message l) (lengths l)) := by
  have hinit : (fun _ : Fin n => (⟨0, iv⟩ : LaneState CV)) =
      batchStateAt compress iv message lengths 0 := by
    funext l
    exact (stateAt_zero compress iv (message l) (lengths l)).symm
  rw [hinit]
  apply run_from_stateAt compress iv hstage
  intro l
  have := rootIndex_lt16 (lengths l) (hlengths l)
  omega

/-- Safe full-block reads include inactive lanes and the final loop test. -/
theorem all_iteration_loads_in_bounds {n : Nat} {CV : Type}
    (compress : Compress CV) (iv : CV)
    {lengths capacity : Fin n → Nat} {message memory : Fin n → Nat → Byte}
    (hstage : ∀ l, ValidStaging (lengths l) (capacity l) (message l) (memory l))
    (t : Nat) (l : Fin n) (w : Fin 64) :
    (batchStateAt compress iv message lengths t l).off + w.val < capacity l := by
  apply load_in_bounds (hstage l)
  omega


structure RootDescriptor (CV : Type) where
  cv : CV
  block : Block
  size : Nat
  flags : Nat

/-- Parameters captured when the batch loop breaks. -/
def batchRootDescriptor {CV : Type} (len : Nat) (memory : Nat → Byte)
    (s : LaneState CV) : RootDescriptor CV :=
  ⟨s.cv, loadBlock memory (s.off / 64), blockSize len s.off, blockFlags len s.off⟩

/-- Scalar root parameters, specified without the batch mask or global loop. -/
def scalarRootDescriptor {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Nat → Byte) (len : Nat) : RootDescriptor CV :=
  ⟨scalarPrefix compress iv message len (rootIndex len),
    scalarBlock message len (rootIndex len), scalarRootSize len, scalarRootFlags len⟩

theorem root_descriptor_equiv {CV : Type} (compress : Compress CV) (iv : CV)
    {len capacity : Nat} {message memory : Nat → Byte}
    (hstage : ValidStaging len capacity message memory) :
    batchRootDescriptor len memory (scalarRootState compress iv message len) =
      scalarRootDescriptor compress iv message len := by
  simp only [batchRootDescriptor, scalarRootState, scalarRootDescriptor,
    Nat.mul_div_cancel_left _ (by decide : 0 < 64), root_size, root_flags]
  rw [load_eq_scalarBlock hstage (Nat.le_refl _)]

/-- Abstract full 16-word XOF feed-forward, with the same parameter order as
    `Compress`. It is not constrained by, or assumed equivalent to, a hash spec. -/
abbrev Xof (CV Output : Type) := CV → Block → Nat → Nat → Nat → Nat → Output

def batchXofAt {n : Nat} {CV Output : Type} (xof : Xof CV Output)
    (lengths : Fin n → Nat) (memory : Fin n → Nat → Byte)
    (s : BatchState n CV) (counter : Fin 32) (l : Fin n) : Output :=
  let d := batchRootDescriptor (lengths l) (memory l) (s l)
  xof d.cv d.block (counter.val % 4294967296) (counter.val / 4294967296) d.size d.flags

def scalarXofAt {CV Output : Type} (compress : Compress CV) (xof : Xof CV Output)
    (iv : CV) (message : Nat → Byte) (len : Nat) (counter : Fin 32) : Output :=
  xof (scalarPrefix compress iv message len (rootIndex len))
    (scalarBlock message len (rootIndex len)) counter.val 0
    (scalarRootSize len) (scalarRootFlags len)

theorem xof_counter_words (counter : Fin 32) :
    counter.val ≤ 31 ∧ counter.val % 4294967296 = counter.val ∧
      counter.val / 4294967296 = 0 := by
  have := counter.isLt
  omega

theorem xof_counter_cast_exact (counter : Fin 32) :
    (BitVec.ofNat 32 counter.val).toNat = counter.val := by
  simp only [BitVec.toNat_ofNat]
  have := counter.isLt
  omega

theorem root_size_cast_exact (len : Nat) :
    (BitVec.ofNat 32 (scalarRootSize len)).toNat = scalarRootSize len := by
  simp only [BitVec.toNat_ofNat]
  have := (root_size_bounds len).1
  omega

theorem root_flags_cast_exact (len : Nat) :
    (BitVec.ofNat 32 (scalarRootFlags len)).toNat = scalarRootFlags len := by
  simp only [BitVec.toNat_ofNat, scalarRootFlags]
  split <;> decide

theorem root_xof_equiv {n : Nat} {CV Output : Type}
    (compress : Compress CV) (xof : Xof CV Output) (iv : CV)
    {lengths capacity : Fin n → Nat} {message memory : Fin n → Nat → Byte}
    (hstage : ∀ l, ValidStaging (lengths l) (capacity l) (message l) (memory l))
    (counter : Fin 32) (l : Fin n) :
    batchXofAt xof lengths memory
      (fun k => scalarRootState compress iv (message k) (lengths k)) counter l =
      scalarXofAt compress xof iv (message l) (lengths l) counter := by
  unfold batchXofAt
  rw [root_descriptor_equiv compress iv (hstage l)]
  have hc := xof_counter_words counter
  simp [scalarRootDescriptor, scalarXofAt, hc.2.1, hc.2.2]

/-- All 32 root output blocks, for every lane, equal independent scalar
    processing under only bounded message lengths and valid byte staging.
    Compression and XOF primitives remain universally quantified. -/
theorem compress_batch_xof_equiv {n : Nat} {CV Output : Type}
    (compress : Compress CV) (xof : Xof CV Output) (iv : CV)
    {lengths capacity : Fin n → Nat} {message memory : Fin n → Nat → Byte}
    (hlengths : ∀ l, lengths l ≤ 1024)
    (hstage : ∀ l, ValidStaging (lengths l) (capacity l) (message l) (memory l)) :
    (batchRun compress lengths memory 15 (fun _ => ⟨0, iv⟩)).map
      (fun s => batchXofAt xof lengths memory s) =
      some (fun counter l => scalarXofAt compress xof iv (message l) (lengths l) counter) := by
  rw [compress_batch_control_equiv compress iv hlengths hstage]
  simp only [Option.map_some]
  apply congrArg some
  funext counter l
  exact root_xof_equiv compress xof iv hstage counter l

/-- Full scalar message bytes are partitioned into rootIndex complete prefix
    blocks and a final block of the exact declared root size. -/
theorem root_partition (len : Nat) :
    64 * rootIndex len + scalarRootSize len = len := by
  unfold rootIndex scalarRootSize
  split <;> omega

/-- The final block index is the ordinary ceiling block count minus one, with
    the required exceptional one-block representation of the empty message. -/
theorem staging_size_formula (len : Nat) :
    paddedBytes len = 64 * max 1 ((len + 63) / 64) := by
  unfold paddedBytes rootIndex
  congr 1
  omega

/-- Matches Rust's domain-separation bitwise OR, rather than relying on an
    unproved replacement of OR by addition in the control transcription. -/
theorem blockFlags_match_bitwise (len off : Nat) :
    blockFlags len off =
      ((if len ≤ off + 64 then (8 ||| 2) else 0) ||| (if off = 0 then 1 else 0)) := by
  unfold blockFlags
  split <;> split <;> decide

/-- The complete control arithmetic is bounded well below both u32 and usize
    limits; the subtraction in blockSize never underflows in a reachable state. -/
theorem reachable_arithmetic_bounds {CV : Type} (compress : Compress CV) (iv : CV)
    (message : Nat → Byte) (len t : Nat) (hlen : len ≤ 1024) :
    let off := (stateAt compress iv message len t).off
    off ≤ len ∧ off ≤ 960 ∧ off + 64 ≤ 1024 ∧ len - off ≤ 1024 := by
  have hroot := rootIndex_lt16 len hlen
  have hoff := stateAt_offset_le_len compress iv message len t
  simp only [stateAt] at *
  omega

/-- The sixteenth loop test (t=15, counting the initial test as t=0) is always
    the final test or later: there can be at most sixteen loads per lane. -/
theorem all_done_by_iteration_15 {n : Nat} {CV : Type}
    (compress : Compress CV) (iv : CV) (message : Fin n → Nat → Byte)
    (lengths : Fin n → Nat) (hlengths : ∀ l, lengths l ≤ 1024) :
    AllDone lengths (batchStateAt compress iv message lengths 15) := by
  apply (allDone_stateAt_iff compress iv message lengths 15).mpr
  intro l
  have := rootIndex_lt16 (lengths l) (hlengths l)
  omega

#print axioms reachable_arithmetic_bounds
#print axioms all_done_by_iteration_15
#print axioms compress_batch_control_equiv
#print axioms compress_batch_xof_equiv
#print axioms all_iteration_loads_in_bounds
#print axioms root_partition
#print axioms staging_size_formula
#print axioms empty_staging_requires_block

end AgaveBatchControl
