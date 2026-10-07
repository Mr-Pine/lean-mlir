import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionContext

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge

variable {s : GlobalState} {q : Pointer} {n : Nat} {r a : BitVec 256}

def scratchSlot (s : GlobalState) : Pointer := s.allocaPtr
def contextSlot (s : GlobalState) : Pointer := (s.alloca 127).allocaPtr
def finalSlot (s : GlobalState) : Pointer := ((s.alloca 127).alloca 208).allocaPtr
def allocated (s : GlobalState) : GlobalState := ((s.alloca 127).alloca 208).alloca 208

theorem allocated_wf (hwf : s.WF) : (allocated s).WF := hwf.alloca.alloca.alloca

theorem allocated_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (allocated s).mem q n :=
  smallRange_alloca hwf.alloca.alloca (smallRange_alloca hwf.alloca (smallRange_alloca hwf hr))

theorem allocated_read (hwf : s.WF) (hr : SmallRange s.mem q n) (width : Nat) :
    (allocated s).mem.readAt q width = s.mem.readAt q width := by
  unfold allocated
  rw [MemoryState.readAt_alloca hwf.alloca.alloca
      (smallRange_alloca hwf.alloca (smallRange_alloca hwf hr)).fits,
    MemoryState.readAt_alloca hwf.alloca (smallRange_alloca hwf hr).fits,
    MemoryState.readAt_alloca hwf hr.fits]

theorem allocated_readBytes (hwf : s.WF) (hr : SmallRange s.mem q n) :
    readBytes (allocated s).mem q n = readBytes s.mem q n := by
  unfold allocated
  rw [readBytes_alloca _ _ _ _ hwf.alloca.alloca
      (smallRange_alloca hwf.alloca (smallRange_alloca hwf hr)),
    readBytes_alloca _ _ _ _ hwf.alloca (smallRange_alloca hwf hr),
    readBytes_alloca _ _ _ _ hwf hr]

theorem scratch_live (hwf : s.WF) : SmallRange (allocated s).mem (scratchSlot s) 127 :=
  smallRange_alloca hwf.alloca.alloca (smallRange_alloca hwf.alloca
    (smallRange_alloca_self s 127 (by decide)))

theorem context_live (hwf : s.WF) : SmallRange (allocated s).mem (contextSlot s) 208 :=
  smallRange_alloca hwf.alloca.alloca (smallRange_alloca_self (s.alloca 127) 208 (by decide))

theorem final_live (s : GlobalState) : SmallRange (allocated s).mem (finalSlot s) 208 :=
  smallRange_alloca_self ((s.alloca 127).alloca 208) 208 (by decide)

theorem scratch_ne_caller (hwf : s.WF) (hr : SmallRange s.mem q n) :
    (scratchSlot s).id ≠ q.id := (GlobalState.ne_allocaPtr_of_fits hwf hr.fits).symm

theorem context_ne_caller (hwf : s.WF) (hr : SmallRange s.mem q n) :
    (contextSlot s).id ≠ q.id :=
  (GlobalState.ne_allocaPtr_of_fits hwf.alloca (smallRange_alloca hwf hr).fits).symm

theorem final_ne_caller (hwf : s.WF) (hr : SmallRange s.mem q n) :
    (finalSlot s).id ≠ q.id :=
  (GlobalState.ne_allocaPtr_of_fits hwf.alloca.alloca
    (smallRange_alloca hwf.alloca (smallRange_alloca hwf hr)).fits).symm

theorem scratch_ne_context (s : GlobalState) : (scratchSlot s).id ≠ (contextSlot s).id := by
  simp [scratchSlot, contextSlot, GlobalState.allocaPtr, GlobalState.alloca]

theorem final_ne_context (s : GlobalState) : (finalSlot s).id ≠ (contextSlot s).id := by
  simp [finalSlot, contextSlot, GlobalState.allocaPtr, GlobalState.alloca]

def scratchR (s : GlobalState) (r : BitVec 256) : MemoryState :=
  (allocated s).mem.storeAt (scratchSlot s) r

def scratchRA (s : GlobalState) (r a : BitVec 256) : MemoryState :=
  (scratchR s r).storeAt ((scratchSlot s).add 32#64) a

def copiedRA (s : GlobalState) (r a : BitVec 256) : MemoryState :=
  (scratchRA s r a).storeAt (contextSlot s) ((scratchRA s r a).readAt (scratchSlot s) 1016)

def entryState (s : GlobalState) (r a : BitVec 256) : GlobalState :=
  {allocated s with mem := initContext (copiedRA s r a) (contextSlot s)}

theorem entry_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (entryState s r a).mem q n :=
  ((((((allocated_live hwf hr).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

theorem entry_wf (hwf : s.WF) : (entryState s r a).WF :=
  (allocated_wf hwf).storeAt.storeAt.storeAt.storeAt.storeAt.storeAt

theorem entry_context_live (hwf : s.WF) :
    SmallRange (entryState s r a).mem (contextSlot s) 208 :=
  ((((((context_live hwf).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

theorem entry_final_live (s : GlobalState) :
    SmallRange (entryState s r a).mem (finalSlot s) 208 :=
  ((((((final_live s).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

theorem scratch_readback (s : GlobalState) (hwf : s.WF) (r a : BitVec 256) :
    readBytes (scratchRA s r a) (scratchSlot s) 64 = bytesOf (n := 32) r ++ bytesOf (n := 32) a := by
  have hl := scratch_live hwf
  have hdis : (Range.of ((scratchSlot s).add 32#64) 256).Disjoint
      (Range.of (scratchSlot s) 256) := by
    simpa using smallRange_disjoint_offsets hl
      (i := 32) (countI := 32) (j := 0) (countJ := 32)
      (by decide) (by decide) (Or.inr (by decide))
  change readBytes (scratchRA s r a) (scratchSlot s) (32 + 32) = _
  rw [readBytes_append]
  dsimp only [scratchRA, scratchR]
  rw [readBytes_storeAt_disjoint _ _ _ _ _
      ((smallRange_mono hl (by decide)).storeAt _ _) hdis,
    readBytes_storeAt_self _ _ 32 (smallRange_mono hl (by decide)),
    readBytes_storeAt_self _ _ 32 (smallRange_add (hl.storeAt _ _) (k := 32) (by decide))]

theorem entry_context (sha : Sha512Model) (s : GlobalState) (hwf : s.WF)
    (r a : BitVec 256) :
    ContextRepresents sha (entryState s r a).mem (contextSlot s) [] (bytesOf (n := 32) r ++ bytesOf (n := 32) a) := by
  apply init_context sha (copiedRA s r a) (contextSlot s) _
    ((((context_live hwf).storeAt _ _).storeAt _ _).storeAt _ _)
  · simp [bytesOf]
  · unfold copiedRA
    exact (readBytes_copy_prefix (scratchRA s r a) (scratchSlot s) (contextSlot s) 127 64
      (((scratch_live hwf).storeAt _ _).storeAt _ _)
      (smallRange_mono (((context_live hwf).storeAt _ _).storeAt _ _) (by decide))
      (by decide)).trans (scratch_readback s hwf r a)

/-- All input observations survive the temporary allocations and context
initialization. No pairwise disjointness between caller inputs is required. -/
theorem entry_read (s : GlobalState) (hwf : s.WF) (r a : BitVec 256)
    (q : Pointer) (n width : Nat) (hr : SmallRange s.mem q n) :
    (entryState s r a).mem.readAt q width = s.mem.readAt q width := by
  have hs := scratch_ne_caller hwf hr
  have hc := context_ne_caller hwf hr
  unfold entryState initContext copiedRA scratchRA scratchR
  rw [readAt_storeAt_of_id_ne _ ((contextSlot s).add 192) q _ width hc,
    readAt_storeAt_of_id_ne _ ((contextSlot s).add 128) q _ width hc,
    readAt_storeAt_of_id_ne _ ((contextSlot s).add 127) q _ width hc,
    readAt_storeAt_of_id_ne _ (contextSlot s) q _ width hc,
    readAt_storeAt_of_id_ne _ ((scratchSlot s).add 32#64) q _ width hs,
    readAt_storeAt_of_id_ne _ (scratchSlot s) q _ width hs]
  exact allocated_read hwf hr width

theorem entry_readBytes (s : GlobalState) (hwf : s.WF) (r a : BitVec 256)
    (q : Pointer) (n : Nat) (hr : SmallRange s.mem q n) :
    readBytes (entryState s r a).mem q n = readBytes s.mem q n := by
  unfold readBytes
  congr 1
  funext i
  exact entry_read s hwf r a _ _ _ (smallRange_add hr (k := i.val) (count := 1) (by omega))

theorem context_internal (s : GlobalState) :
    s.alloc.nextFreeBlock ≤ (contextSlot s).id.id := by
  simp [contextSlot, GlobalState.allocaPtr, GlobalState.alloca]

theorem final_internal (s : GlobalState) :
    s.alloc.nextFreeBlock ≤ (finalSlot s).id.id := by
  simp [finalSlot, GlobalState.allocaPtr, GlobalState.alloca]
  omega

theorem allocated_frame (s : GlobalState) (hwf : s.WF) :
    (allocated s).mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  unfold allocated
  rw [GlobalState.eraseFrom_alloca_of_le (by simp [GlobalState.alloca]; omega),
    GlobalState.eraseFrom_alloca_of_le (by simp [GlobalState.alloca]),
    GlobalState.eraseFrom_alloca, hwf.eraseFrom]

theorem entry_frame (s : GlobalState) (hwf : s.WF) (r a : BitVec 256) :
    (entryState s r a).mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  have hc := context_internal s
  have hs : s.alloc.nextFreeBlock ≤ (scratchSlot s).id.id := Nat.le_refl _
  exact erase_internal_store _ _ _ _ _
    (erase_internal_store _ _ _ _ _
      (erase_internal_store _ _ _ _ _
        (erase_internal_store _ _ _ _ _
          (erase_internal_store _ _ _ _ _
            (erase_internal_store _ _ _ _ _ (allocated_frame s hwf) hs) hs) hc) hc) hc) hc

end Agave.Ed25519.Verifier.Execution.Challenge
