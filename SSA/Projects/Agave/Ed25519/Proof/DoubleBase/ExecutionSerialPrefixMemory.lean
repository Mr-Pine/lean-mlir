import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialStack
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialTotalNAF

/-! Memory and register invariants joining the actual serial entry, both NAF
emitters, and the descending scan. All fresh-object conditions are consequences
of the entry allocations. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

theorem PrefixEq.mono (h : PrefixEq E F n) (hm : m ≤ n) : PrefixEq E F m :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

theorem serialStack_counter (s : GlobalState) (n : Nat) :
    (serialStack s n).alloc.nextFreeBlock = s.alloc.nextFreeBlock + n := by
  induction n with
  | zero => simp [serialStack]
  | succ n ih => simp only [serialStack, GlobalState.alloca, ih, Nat.add_assoc]

theorem serialStackPtr_id (s : GlobalState) (n : Nat) :
    (serialStackPtr s n).id.id = s.alloc.nextFreeBlock + n := by
  exact serialStack_counter s n

theorem serialStack_separate (s : GlobalState) (i j : Nat) (hij : i ≠ j) :
    (serialStackPtr s i).id ≠ (serialStackPtr s j).id := by
  intro heq
  have hv := congrArg BlockId.id heq
  rw [serialStackPtr_id, serialStackPtr_id] at hv
  omega

/-- Subsequent allocations do not change the freshly allocated scalar buffer. -/
theorem serialStack_read_fresh (s : GlobalState) (hwf : s.WF)
    (i k bits : Nat) (hsize : serialStackSize i < 2 ^ 63) :
    (serialStack s (i + 1 + k)).mem.readAt (serialStackPtr s i) bits =
      ((serialStack s i).alloca (serialStackSize i)).mem.readAt
        (serialStackPtr s i) bits := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((serialStack s (i + 1 + k)).alloca _).mem.readAt _ _ = _
      rw [MemoryState.readAt_alloca (serialStack_wf hwf _)
        (serialStack_buffer hwf i (i + 1 + k) (by omega) hsize).fits, ih]

theorem serialStack_words_zero (s : GlobalState) (hwf : s.WF) (i : Fin 2) :
    (serialStack s 12).mem.readAt (serialStackPtr s i.val) 320 = 0 := by
  have hn : i.val + 1 + (11 - i.val) = 12 := by have := i.isLt; omega
  have hsize : serialStackSize i.val = 40 := by
    rcases (show i.val = 0 ∨ i.val = 1 by have := i.isLt; omega) with h | h <;>
      simp [h, serialStackSize]
  have hread := serialStack_read_fresh s hwf i.val (11 - i.val) 320 (by rw [hsize]; decide)
  rw [hn, hsize] at hread
  exact hread.trans (NAF.Memory.fresh_words_zero (serialStack s i.val))

theorem nafSetup_wf (hwf : s.WF) : (nafInitialized s digits scratch scalar).WF := by
  simpa only [nafInitialized, nafPadded, nafCleared, GlobalState.WF_storeAt] using hwf

/-- The scratch buffer starts zero because it is fresh; its fifth-word store
and scalar memcpy establish the exact 320-bit padded scalar. -/
theorem nafSetup_scalar_buffer (s : GlobalState) (digits scratch : Pointer)
    (scalar : BitVec 256) (hscratch : Buffer s.mem scratch 40)
    (hsd : scratch.id ≠ digits.id) (hzero : s.mem.readAt scratch 320 = 0) :
    (nafInitialized s digits scratch scalar).mem.readAt scratch 320 =
      NAF.WordWindow.scalarBuffer scalar := by
  have hc : (nafCleared s digits).mem.readAt scratch 320 = 0 := by
    unfold nafCleared
    rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hsd.symm), hzero]
  have hb : Buffer (nafCleared s digits).mem scratch 40 :=
    hscratch.storeAt digits (0 : BitVec 2048)
  have hp : (nafPadded s digits scratch).mem.readAt scratch 320 = 0 := by
    have hs := MemoryState.readAt_add_storeAt (off := 32#64) hb.fits
      (hb.offset_noOverflow 32 (by decide))
      (by decide : (32#64).toNat * 8 + 64 ≤ 320) (0#64)
    change ((nafCleared s digits).mem.storeAt (scratch.add 32#64) (0#64)).readAt scratch 320 = 0
    rw [hs, hc]
    simp [LeanMLIR.RIR.Memory.spliceBits]
  exact NAF.Memory.copy_scalar_words (hb.storeAt _ _) hp scalar

def emittedNAF (width : Nat) (s : GlobalState) (out : Pointer) (scalar : BitVec 256) :
    GlobalState :=
  {s with mem := NAF.Memory.storeLoop width out 256 0 ⟨scalar.toNat, 0⟩ s.mem}

theorem emittedNAF_buffer (h : Buffer s.mem q bytes) :
    Buffer (emittedNAF width s out scalar).mem q bytes :=
  NAF.Memory.storeLoop_buffer width out 256 0 ⟨scalar.toNat, 0⟩ s.mem h

theorem emittedNAF_read_other (s : GlobalState) (width : Nat) (out q : Pointer)
    (scalar : BitVec 256) (bits : Nat) (h : out.id ≠ q.id) :
    (emittedNAF width s out scalar).mem.readAt q bits = s.mem.readAt q bits :=
  NAF.Memory.storeLoop_preserves_other_block width out 256 0
    ⟨scalar.toNat, 0⟩ s.mem q bits h

theorem storeLoop_wf (width : Nat) (out : Pointer) (fuel pos : Nat)
    (state : NAF.State) (s : GlobalState) (hwf : s.WF) :
    ({s with mem := NAF.Memory.storeLoop width out fuel pos state s.mem} : GlobalState).WF := by
  induction fuel generalizing pos state s with
  | zero => exact hwf
  | succ fuel ih =>
      by_cases hp : pos < 256
      · rw [NAF.Memory.storeLoop, if_pos hp]
        dsimp only
        by_cases hd : (NAF.step width state).digit = 0
        · rw [if_pos hd]
          exact ih _ _ s hwf
        · rw [if_neg hd]
          exact ih _ _ {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos)) (BitVec.ofInt 8 (NAF.step width state).digit)}
            hwf.storeAt
      · simpa only [NAF.Memory.storeLoop, if_neg hp] using hwf

theorem emittedNAF_wf (hwf : s.WF) : (emittedNAF width s out scalar).WF :=
  storeLoop_wf width out 256 0 ⟨scalar.toNat, 0⟩ s hwf

theorem emittedNAF_sourceDigits (s : GlobalState) (width : Nat) (out : Pointer)
    (scalar : BitVec 256) (hw : NAF.Supported width) (hout : Buffer s.mem out 256)
    (hzero : s.mem.readAt out 2048 = 0) (i : Fin 256) :
    (emittedNAF width s out scalar).mem.readAt (out.add (BitVec.ofNat 64 i.val)) 8 =
      BitVec.ofInt 8 (NAF.sourceDigits width scalar.toNat i) :=
  NAF.Memory.storeLoop_sourceDigits width hw scalar.toNat out s.mem hout hzero i

def serialNAFState5 (s : GlobalState) (a : BitVec 256) : GlobalState :=
  emittedNAF 5 (nafInitialized (serialStack s 12) (serialStackPtr s 11)
    (serialStackPtr s 1) a) (serialStackPtr s 11) a

def serialNAFState8 (s : GlobalState) (a b : BitVec 256) : GlobalState :=
  emittedNAF 8 (nafInitialized (serialNAFState5 s a) (serialStackPtr s 10)
    (serialStackPtr s 0) b) (serialStackPtr s 10) b

theorem serialNAFState5_buffer (h : Buffer (serialStack s 12).mem q bytes) :
    Buffer (serialNAFState5 s a).mem q bytes :=
  emittedNAF_buffer (nafSetup_buffer h)

theorem serialNAFState8_buffer (h : Buffer (serialStack s 12).mem q bytes) :
    Buffer (serialNAFState8 s a b).mem q bytes :=
  emittedNAF_buffer (nafSetup_buffer (serialNAFState5_buffer h))

theorem serialNAFState5_read_other (s : GlobalState) (a : BitVec 256) (q : Pointer)
    (bits : Nat) (hd : (serialStackPtr s 11).id ≠ q.id)
    (hs : (serialStackPtr s 1).id ≠ q.id) :
    (serialNAFState5 s a).mem.readAt q bits = (serialStack s 12).mem.readAt q bits := by
  unfold serialNAFState5
  rw [emittedNAF_read_other _ _ _ _ _ _ hd,
    nafSetup_read_other _ _ _ _ _ _ hd hs]

theorem serialNAFState8_read_other (s : GlobalState) (a b : BitVec 256)
    (q : Pointer) (bits : Nat)
    (h10 : (serialStackPtr s 10).id ≠ q.id)
    (h0 : (serialStackPtr s 0).id ≠ q.id) :
    (serialNAFState8 s a b).mem.readAt q bits = (serialNAFState5 s a).mem.readAt q bits := by
  unfold serialNAFState8
  rw [emittedNAF_read_other _ _ _ _ _ _ h10,
    nafSetup_read_other _ _ _ _ _ _ h10 h0]

theorem serialNAFState8_sourceDigits (s : GlobalState) (a b : BitVec 256) (hwf : s.WF) :
    (∀ i : Fin 256, (serialNAFState8 s a b).mem.readAt
      ((serialStackPtr s 11).add (BitVec.ofNat 64 i.val)) 8 =
        BitVec.ofInt 8 (NAF.sourceDigits 5 a.toNat i)) ∧
    (∀ i : Fin 256, (serialNAFState8 s a b).mem.readAt
      ((serialStackPtr s 10).add (BitVec.ofNat 64 i.val)) 8 =
        BitVec.ofInt 8 (NAF.sourceDigits 8 b.toNat i)) := by
  have hA : Buffer (serialStack s 12).mem (serialStackPtr s 11) 256 :=
    serialStack_buffer hwf 11 12 (by decide) (by decide)
  have hB : Buffer (serialStack s 12).mem (serialStackPtr s 10) 256 :=
    serialStack_buffer hwf 10 12 (by decide) (by decide)
  constructor
  · intro i
    rw [serialNAFState8_read_other _ _ _ _ _
      (by simpa only [Pointer.add_id] using serialStack_separate s 10 11 (by decide))
      (by simpa only [Pointer.add_id] using serialStack_separate s 0 11 (by decide))]
    apply emittedNAF_sourceDigits _ 5 _ a (Or.inl rfl) (nafSetup_buffer hA)
    exact nafSetup_digits_zero _ _ _ _ hA (serialStack_separate s 1 11 (by decide))
  · intro i
    apply emittedNAF_sourceDigits _ 8 _ b (Or.inr rfl)
      (nafSetup_buffer (serialNAFState5_buffer hB))
    exact nafSetup_digits_zero _ _ _ _ (serialNAFState5_buffer hB)
      (serialStack_separate s 0 10 (by decide))

end Agave.Ed25519.DoubleBase.RIR
