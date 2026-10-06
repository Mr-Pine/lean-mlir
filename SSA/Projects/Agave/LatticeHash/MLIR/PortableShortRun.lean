/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableShortXof
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceProof

/-! A continuous-memory execution of the extracted portable compression
functions for every unkeyed message of at most 1024 bytes. The call sequence is
defined in Lean; no theorem here claims extraction of Rust `Hasher` control flow. -/
namespace AgaveLatticeHash.MLIR.PortableShort
open LeanMLIR SLLVM Firedancer AgaveBlake3Reference
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
attribute [local irreducible] agave_portable_compress_in_place portableCompressionMemory
  PortableInPlace.cvMemory Blake3Compression.scalarCompress Blake3Compression.scalarCompressCV
  AgaveBlake3Reference.compressInPlace CompressionExit.outputMem

def startFlags8 (j : Nat) : BitVec 8 := if j = 0 then 1 else 0

theorem startFlags8_extend (j : Nat) :
    (startFlags8 j).zeroExtend 32 = startFlag j := by
  by_cases h : j = 0 <;> simp [startFlags8, startFlag, h]

def prefixCV (m : Message) (j : Nat) : CV :=
  AgaveBatchControl.scalarPrefix AgaveConcrete.compress AgaveConcrete.iv
    (AgaveConcrete.bytes m) m.length j

theorem prefix_step (m : Message) (j : Nat) :
    Blake3Compression.scalarCompressCV (prefixCV m j) (AgaveConcrete.decodeBlock (block m j))
      0 64 (startFlag j) = prefixCV m (j+1) := by
  simp only [prefixCV, AgaveBatchControl.scalarPrefix, AgaveConcrete.compress,
    AgaveConcrete.counter, startFlag, block]
  split <;> rfl

/-- Actual extracted in-place calls in input order, withholding the last block. -/
inductive NonrootCalls (cvp src : Pointer) : Nat → GlobalState → GlobalState → Prop
  | nil (s) : NonrootCalls cvp src 0 s s
  | step {n s mid t} : NonrootCalls cvp src n s mid →
      StateT.run (agave_portable_compress_in_place.denote (Ctxt.Valuation.ofHVector
        [.value (startFlags8 n), .value (0#64), .value (64#8),
         .value (blockPtr src n), .value cvp]ₕ)) mid = .value ([]ₕ, t) →
      NonrootCalls cvp src (n+1) s t

/-- The physical CV after every nonroot call equals the scalar prefix. Only the
CV allocation changes, so the remaining input and output capacity survive. -/
theorem nonroot_calls (m : Message) (hm : m.length ≤ 1024)
    (s : GlobalState) (cvp src out : Pointer) (hl : Layout cvp src out)
    (h : Inputs s cvp src out m iv) (n : Nat) (hn : n ≤ (finalChunk m).blocksCompressed) :
    ∃ t : GlobalState, NonrootCalls cvp src n s t ∧
      Inputs t cvp src out m (prefixCV m n) ∧
      ∀ q, q ≠ cvp.id → t.mem.live? q = s.mem.live? q := by
  induction n with
  | zero => exact ⟨s, .nil s, h, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨mid, hc, hi, hf⟩ := ih (by omega)
    have hj : n < 16 := by
      have := AgaveBatchControl.rootIndex_lt16 m.length hm
      change n+1 ≤ AgaveBatchControl.rootIndex m.length at hn
      omega
    let msg := blockPtr src n
    let words := Blake3Compression.scalarCompress (prefixCV m n)
      (AgaveConcrete.decodeBlock (block m n)) 0 ((64#8).zeroExtend 32)
      ((startFlags8 n).zeroExtend 32)
    let t : GlobalState := {mid with mem := PortableInPlace.cvMemory mid.mem cvp words}
    have hrun := portable_in_place_run mid cvp msg (prefixCV m n)
      (AgaveConcrete.decodeBlock (block m n)) 0 64 (startFlags8 n) hi.cv_fits
      (blockPtr_fits (n := 16) hl.src_zero hi.src_fits n hj (by omega))
      (by rw [blockPtr_offset src hl.src_zero n (by omega)]; omega)
      hi.cv_read (hi.src_read ⟨n, hj⟩)
    have hframe (q : BlockId) (hq : q ≠ cvp.id) : t.mem.live? q = mid.mem.live? q := by
      simpa only [t, PortableInPlace.cvMemory] using
        CompressionExit.outputMem_frame cvp (fun i => #v[words i]) 8 mid.mem q hq
    refine ⟨t, .step hc hrun, ?_, fun q hq => (hframe q hq).trans (hf q hq)⟩
    refine ⟨?_, fits_of_live?_eq (hframe src.id hl.cv_src.symm) hi.src_fits,
      fits_of_live?_eq (hframe out.id hl.cv_out.symm) hi.out_fits, ?_, ?_⟩
    · simpa only [t, PortableInPlace.cvMemory] using
        CompressionExit.fits_outputMem cvp (fun i => #v[words i]) 8 hi.cv_fits
    · intro i
      have hr := PortableInPlace.outputMem_read_cv cvp words mid.mem hi.cv_fits
        (by rw [hl.cv_zero]; decide) 8 (by omega) (i.castAdd 8) i.isLt
      have hr' : readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 t.mem = some
        (Blake3Compression.scalarCompressCV (prefixCV m n)
          (AgaveConcrete.decodeBlock (block m n)) 0 ((64#8).zeroExtend 32)
          ((startFlags8 n).zeroExtend 32) i) := by
        simpa only [t, PortableInPlace.cvMemory, Blake3Compression.scalarCompressCV, words,
          Fin.val_castAdd] using hr
      rw [startFlags8_extend] at hr'
      change readWord? _ 32 t.mem = some
        (Blake3Compression.scalarCompressCV (prefixCV m n)
          (AgaveConcrete.decodeBlock (block m n)) 0 64 (startFlag n) i) at hr'
      rwa [prefix_step] at hr'
    · intro j i
      rw [readWord?_of_live?_eq (p := (blockPtr src j.val).withOffset (BitVec.ofNat 64 (4*i.val)))
        (hframe src.id hl.cv_src.symm)]
      exact hi.src_read j i

/-- Full actual helper-call trace, with no supplied root-CV or root-block
correctness premise. The descriptor is determined by message bytes and the
preceding actual CV writebacks. -/
def Executes (m : Message) (entry : GlobalState) (cvp src out : Pointer)
    (result : GlobalState) : Prop :=
  ∃ rootState : GlobalState,
    NonrootCalls cvp src (finalChunk m).blocksCompressed entry rootState ∧
    (∀ i : Fin 8,
      readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 rootState.mem =
        some ((finalChunk m).cv i)) ∧
    XofCalls cvp (blockPtr src (finalChunk m).blocksCompressed) out
      (BitVec.ofNat 8 (finalChunk m).bufLen) (rootFlags8 (finalChunk m).blocksCompressed)
      32 rootState result

/-- Every short message has a nonpoison, continuous-memory execution of all
actual portable calls, and all 2048 final bytes equal the independent reference. -/
theorem short_run (base : GlobalState) (hbase : base.WF) (m : Message) (hm : m.length ≤ 1024) :
    ∃ result : GlobalState,
      Executes m (image base m) (ptr base 0) (ptr base 1) (ptr base 2) result ∧
      ∀ i : Fin 2048,
        readWord? ((ptr base 2).withOffset (BitVec.ofNat 64 i.val)) 8 result.mem =
          some (readerFill (finalChunk m) i) := by
  obtain ⟨_, hl, h⟩ := image_inputs base hbase m
  obtain ⟨root, hc, hi, _⟩ := nonroot_calls m hm (image base m)
    (ptr base 0) (ptr base 1) (ptr base 2) hl h (finalChunk m).blocksCompressed (by omega)
  obtain ⟨result, hx, hr⟩ := xof_calls_all_bytes m hm root
    (ptr base 0) (ptr base 1) (ptr base 2) hl hi
  exact ⟨result, ⟨root, hc, hi.cv_read, hx⟩, hr⟩

/-- A little-endian LtHash limb observed by two real byte loads. -/
def readLimb (mem : MemoryState) (out : Pointer) (i : Fin 1024) : Option (BitVec 16) := do
  let lo ← readWord? (out.withOffset (BitVec.ofNat 64 (2*i.val))) 8 mem
  let hi ← readWord? (out.withOffset (BitVec.ofNat 64 (2*i.val+1))) 8 mem
  pure (hi ++ lo)

/-- Closed nonvacuity and reference endpoint: the empty caller needs no external
memory assumptions; actual result-byte loads yield every portable LtHash limb. -/
theorem short_run_exists (m : Message) (hm : m.length ≤ 1024) :
    ∃ result : GlobalState,
      Executes m (image CallerMemory.emptyState m)
        (ptr CallerMemory.emptyState 0) (ptr CallerMemory.emptyState 1)
        (ptr CallerMemory.emptyState 2) result ∧
      (∀ i : Fin 2048,
        readWord? ((ptr CallerMemory.emptyState 2).withOffset (BitVec.ofNat 64 i.val)) 8 result.mem =
          some (readerFill (finalChunk m) i)) ∧
      ∀ i : Fin 1024, readLimb result.mem (ptr CallerMemory.emptyState 2) i =
        (portableLtHash m).map (fun value => value i) := by
  obtain ⟨result, hc, hr⟩ := short_run CallerMemory.emptyState CallerMemory.emptyState_wf m hm
  refine ⟨result, hc, hr, ?_⟩
  intro i
  unfold readLimb
  rw [hr ⟨2*i.val, by omega⟩, hr ⟨2*i.val+1, by omega⟩]
  simp only [portableLtHash, updateFresh_eq m hm, Option.map_some,
    finishLtHash]
  rfl

end AgaveLatticeHash.MLIR.PortableShort
