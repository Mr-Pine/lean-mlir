/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofMemory
import SSA.Projects.Agave.LatticeHash.MLIR.BatchInputSuccessor
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootCopy
import SSA.Projects.Agave.LatticeHash.MLIR.MessageCopy

namespace AgaveLatticeHash.MLIR.BatchRootXof
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open BatchXofLoop BatchReduction
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def rootCV (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) : CV Words8 :=
  fun i => Vector.ofFn (BatchUpdate.stateCV8 ms t i)

noncomputable def copyVal (B : agave_batch_8.cfgCtx.Valuation)
    (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) : BatchRootCopy.Input18.Valuation :=
  Ctxt.Valuation.ofHVector (BatchInputSuccessor.rootAt ms t).args.reverse ++ B

theorem entry_init (s : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) :
    InitEnv (BatchEntry.entryVal8 s src len out sched panic lengths) := by
  constructor <;> rfl

theorem entry_output (s : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) :
    OutputEnv (BatchEntry.entryVal8 s src len out sched panic lengths) out := by
  constructor <;> rfl

theorem entry_round (s : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (cv : CV Words8) (blockLen flags : Words8)
    (counter : Nat) :
    CompressionRound.RoundEnv8
      (sourceVal (BatchEntry.entryVal8 s src len out sched panic lengths)
        (extras cv blockLen flags (out.withOffset 32) counter))
      (BatchEntry.scratch s 1) sched := by
  constructor <;> rfl

theorem next18_root (B : agave_batch_8.cfgCtx.Valuation)
    (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) (out : Pointer)
    (hz : B ⟨65, rfl⟩ = PoisonOr.value 0#64) :
    BatchRootCopy.next18 (copyVal B ms t) out =
      rootTarget (rootCV ms t) (BatchInputSuccessor.sizes ms t)
        (BatchInputSuccessor.flags ms t) (out.withOffset 32) 0 := by
  have cv (i : Fin 8) : BatchRootCopy.cvWords
      ((packCV8 (BatchUpdate.stateCV8 ms t i)).map PoisonOr.value) =
      (rootCV ms t i).map PoisonOr.value := BatchInit8.unpackCV_pack _
  have hz' : (copyVal B ms t) ⟨75, rfl⟩ = PoisonOr.value 0#64 := hz
  have hl : (copyVal B ms t) ⟨0, rfl⟩ = (BatchInputSuccessor.sizes ms t).map PoisonOr.value := rfl
  have hf : (copyVal B ms t) ⟨1, rfl⟩ = (BatchInputSuccessor.flags ms t).map PoisonOr.value := rfl
  have h0 : BatchRootCopy.cvWords ((copyVal B ms t) ⟨2, rfl⟩) =
      (rootCV ms t 0).map PoisonOr.value := cv 0
  have h1 : BatchRootCopy.cvWords ((copyVal B ms t) ⟨3, rfl⟩) =
      (rootCV ms t 1).map PoisonOr.value := cv 1
  have h2 : BatchRootCopy.cvWords ((copyVal B ms t) ⟨4, rfl⟩) =
      (rootCV ms t 2).map PoisonOr.value := cv 2
  have h3 : BatchRootCopy.cvWords ((copyVal B ms t) ⟨5, rfl⟩) =
      (rootCV ms t 3).map PoisonOr.value := cv 3
  have h4 : BatchRootCopy.cvWords ((copyVal B ms t) ⟨6, rfl⟩) =
      (rootCV ms t 4).map PoisonOr.value := cv 4
  have h5 : BatchRootCopy.cvWords ((copyVal B ms t) ⟨7, rfl⟩) =
      (rootCV ms t 5).map PoisonOr.value := cv 5
  have h6 : BatchRootCopy.cvWords ((copyVal B ms t) ⟨8, rfl⟩) =
      (rootCV ms t 6).map PoisonOr.value := cv 6
  have h7 : BatchRootCopy.cvWords ((copyVal B ms t) ⟨9, rfl⟩) =
      (rootCV ms t 7).map PoisonOr.value := cv 7
  unfold BatchRootCopy.next18
  rw [hz', hl, hf, h0, h1, h2, h3, h4, h5, h6, h7]
  rfl

/-- The retained root message is copied by the actual block18 before the
exact compiler XOF loop begins. -/
theorem copy_run (entry : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (s : GlobalState) (bytes : BitVec 4096)
    (fsrc : Fits s.mem (BatchEntry.scratch entry 0) 4096)
    (fdst : Fits s.mem (BatchEntry.scratch entry 1) 4096)
    (hread : readWord? (BatchEntry.scratch entry 0) 4096 s.mem = some bytes) :
    StateT.run (agave_batch_8.blocks.run
      (BatchEntry.entryVal8 entry src len out sched panic lengths)
      (BatchInputSuccessor.rootAt ms t)) s =
      StateT.run (agave_batch_8.blocks.run
        (BatchEntry.entryVal8 entry src len out sched panic lengths)
        (rootTarget (rootCV ms t) (BatchInputSuccessor.sizes ms t)
          (BatchInputSuccessor.flags ms t) (out.withOffset 32) 0))
        {s with mem := s.mem.splice (BatchEntry.scratch entry 1) bytes} := by
  let B := BatchEntry.entryVal8 entry src len out sched panic lengths
  rw [run_step_continue]
  denote_reduce_get
  change StateT.run (agave_batch_8.cfgBlock_18.denote (copyVal B ms t) >>=
    fun z => continueBatch B z.2) s = _
  rw [BatchRootCopy.block18_continue (copyVal B ms t) s
    (BatchEntry.scratch entry 0) (BatchEntry.scratch entry 1) out bytes
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) fsrc fdst hread]
  rw [next18_root B ms t out (by rfl)]
  rfl

private theorem messagePtr_eq (p : Pointer) (i : Fin 16) :
    CompressionRound.messagePtr8 p i = p.withOffset (BitVec.ofNat 64 (32*i.val)) := by
  unfold CompressionRound.messagePtr8
  rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_mul]
  rw [Nat.mul_comm i.val 32]

/-- The actual root copy supplies the XOF message invariant while preserving
all caller accumulator and schedule reads. -/
theorem initial_after_copy (entry s : GlobalState) (out sched : Pointer)
    (m : State Words8) (a : Vector (BitVec 16) 1024) (bytes : BitVec 4096)
    (hmsg : CompressionMessage s.mem (BatchEntry.scratch entry 0) m)
    (fdst : Fits s.mem (BatchEntry.scratch entry 1) 4096)
    (hread : readWord? (BatchEntry.scratch entry 0) 4096 s.mem = some bytes)
    (hsi : ∀ r i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hf : Fits s.mem out 16384) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (hr : readWord? out 16384 s.mem = some (packBits a))
    (hos : out.id ≠ sched.id) (hom : out.id ≠ (BatchEntry.scratch entry 1).id)
    (hms : (BatchEntry.scratch entry 1).id ≠ sched.id) :
    InitialMemory {s with mem := s.mem.splice (BatchEntry.scratch entry 1) bytes}
      out (BatchEntry.scratch entry 1) sched m (lowerSlice a) (upperSlice a) := by
  have hc := hmsg.copy fdst (by simp [BatchEntry.scratch])
    (by simp [BatchEntry.scratch]) bytes hread
  apply InitialMemory.ofPacked
  · intro r i
    exact fits_splice (hsi r i)
  · intro r i
    rw [readWord?_splice_ne (show (BatchEntry.scratch entry 1).id ≠
      (CompressionRound.schedulePtr sched r i).id from hms)]
    exact hsv r i
  · intro i
    rw [messagePtr_eq]
    exact compressionSlotFits8 hc.fits i.val i.isLt
  · intro i
    rw [messagePtr_eq]
    exact hc.read i
  · exact fits_splice hf
  · exact hw
  · rw [readWord?_splice_ne hom.symm]
    exact hr
  · exact hos
  · exact hom

/-- The canonical root path copies the retained message and executes all
32 output counters from initial byte-backed memory. -/
theorem run (entry : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (s : GlobalState) (m : State Words8) (a : Vector (BitVec 16) 1024) (bytes : BitVec 4096)
    (hmsg : CompressionMessage s.mem (BatchEntry.scratch entry 0) m)
    (fdst : Fits s.mem (BatchEntry.scratch entry 1) 4096)
    (hread : readWord? (BatchEntry.scratch entry 0) 4096 s.mem = some bytes)
    (hsi : ∀ r i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hf : Fits s.mem out 16384) (hw : out.offset.toNat + 2048 ≤ 2^64)
    (hr : readWord? out 16384 s.mem = some (packBits a))
    (hos : out.id ≠ sched.id) (hom : out.id ≠ (BatchEntry.scratch entry 1).id)
    (hms : (BatchEntry.scratch entry 1).id ≠ sched.id) :
    StateT.run (agave_batch_8.blocks.run
      (BatchEntry.entryVal8 entry src len out sched panic lengths)
      (BatchInputSuccessor.rootAt ms t)) s =
      .value (.nil, accumulatedState
        {s with mem := s.mem.splice (BatchEntry.scratch entry 1) bytes}
        out (out.withOffset 32) (rootCV ms t) (BatchInputSuccessor.sizes ms t)
        (BatchInputSuccessor.flags ms t) m (lowerSlice a) (upperSlice a) 32) := by
  rw [copy_run entry src len out sched panic lengths ms t s bytes hmsg.fits fdst hread]
  exact xof32_run_initial _ _ _ _ out (BatchEntry.scratch entry 1) sched
    (entry_init entry src len out sched panic lengths)
    (entry_output entry src len out sched panic lengths) _ m (lowerSlice a) (upperSlice a)
    (entry_round entry src len out sched panic lengths _ _ _ 0)
    (initial_after_copy entry s out sched m a bytes hmsg fdst hread hsi hsv hf hw hr hos hom hms)

end AgaveLatticeHash.MLIR.BatchRootXof
