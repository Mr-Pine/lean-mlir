import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorState
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointRepresentation

/-! Exact word readback for the finite cofactor memory schedule. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR SerialPoint SerialPoint.Execution SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

/-- Four field arrays read at the ABI offsets. -/
def readWordPoint (s : GlobalState) (p : Pointer) : WordPoint :=
  ⟨readLimbs s p, readLimbs s (p.add 40#64), readLimbs s (p.add 80#64), readLimbs s (p.add 120#64)⟩

def xyz (P : WordPoint) : WordPoint := { P with T := fun _ => 0 }

@[simp] theorem doubleWord_xyz (P : WordPoint) : SerialPoint.doubleWord (xyz P) = SerialPoint.doubleWord P := rfl
@[simp] theorem twiceWord_xyz (P : WordPoint) : twiceWord (xyz P) = twiceWord P := rfl

/-- The two reader interfaces describe exactly the same twenty machine words. -/
theorem readWordPoint_eq (s : GlobalState) (p : Pointer) :
    readWordPoint s p = pointFromWords (readPointWords s p) := by
  apply PointArithmetic.Extended.ext <;> funext i <;> fin_cases i <;>
    simp [readWordPoint, readLimbs, pointFromWords, readPointWords, Pointer.add_add]

theorem readWordPoint_layout (s : GlobalState) (p : Pointer) (P : Verifier.Execution.Key.PointWords)
    (h : Verifier.Execution.Dalek.ReadBytes s p 160 P.bytes) :
    readWordPoint s p = keyWordPoint P := by
  have h0 := read_coordinate s p P h 0
  have h1 := read_coordinate s p P h 1
  have h2 := read_coordinate s p P h 2
  have h3 := read_coordinate s p P h 3
  apply PointArithmetic.Extended.ext
  · simpa [readWordPoint, keyWordPoint, coordinates] using h0
  · simpa [readWordPoint, keyWordPoint, coordinates] using h1
  · simpa [readWordPoint, keyWordPoint, coordinates] using h2
  · simpa [readWordPoint, keyWordPoint, coordinates] using h3

theorem mulState_range (h : SmallRange s.mem q n) (out a b : Pointer) :
    SmallRange (mulState s out a b).mem q n := smallRange_storeLimbs h _ _

theorem mulState_read_self (s : GlobalState) (out a b : Pointer)
    (h : SmallRange s.mem out 40) :
    readLimbs (mulState s out a b) out = machine (readLimbs s a) (readLimbs s b) :=
  readLimbs_storeLimbs s out _ h

theorem mulState_read_ne (s : GlobalState) (out a b q : Pointer)
    (h : out.id ≠ q.id) : readLimbs (mulState s out a b) q = readLimbs s q :=
  readLimbs_storeLimbs_ne s out q _ h

theorem mulState_read_frame (s : GlobalState) (out a b q : Pointer)
    (ho : SmallRange s.mem out 40) (hq : SmallRange s.mem q 40)
    (hd : (Range.of q 320).Disjoint (Range.of out 320)) :
    readLimbs (mulState s out a b) q = readLimbs s q :=
  readLimbs_storeLimbs_frame s out q _ ho hq hd

def convert3State (s : GlobalState) (out input : Pointer) : GlobalState :=
  let s := mulState s out input (input.add 120#64)
  let s := mulState s (out.add 40#64) (input.add 40#64) (input.add 80#64)
  mulState s (out.add 80#64) (input.add 80#64) (input.add 120#64)

theorem convert3State_range (h : SmallRange s.mem q n) (out input : Pointer) :
    SmallRange (convert3State s out input).mem q n :=
  mulState_range (mulState_range (mulState_range h _ _ _) _ _ _) _ _ _

/-- The first three products compute exactly the XYZ coordinates; no limb
bounds or arbitrary field-operation contracts occur in this memory lemma. -/
theorem convert3State_read (s : GlobalState) (out input : Pointer)
    (hout : SmallRange s.mem out 120) (hne : out.id ≠ input.id) :
    xyz (readWordPoint (convert3State s out input) out) =
      xyz (asExtendedWord (readWordPoint s input)) := by
  let s1 := mulState s out input (input.add 120#64)
  let s2 := mulState s1 (out.add 40#64) (input.add 40#64) (input.add 80#64)
  have ho1 : SmallRange s1.mem out 120 := mulState_range hout _ _ _
  have ho2 : SmallRange s2.mem out 120 := mulState_range ho1 _ _ _
  have h0 := smallRange_add hout (k := 0) (count := 40) (by decide)
  have h01 := smallRange_add ho1 (k := 0) (count := 40) (by decide)
  have h02 := smallRange_add ho2 (k := 0) (count := 40) (by decide)
  simp only [Pointer.add_zero] at h0 h01 h02
  have hd01 := subranges_disjoint hout (i := 0) (j := 40) (ni := 40) (nj := 40)
    (by decide) (by decide) (by decide)
  have hd02 := subranges_disjoint hout (i := 0) (j := 80) (ni := 40) (nj := 40)
    (by decide) (by decide) (by decide)
  have hd12 := subranges_disjoint hout (i := 40) (j := 80) (ni := 40) (nj := 40)
    (by decide) (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, Pointer.add_zero] at hd01 hd02 hd12
  have hn (i j : BitVec 64) : (out.add i).id ≠ (input.add j).id := hne
  apply PointArithmetic.Extended.ext
  · change readLimbs (mulState s2 (out.add 80#64) (input.add 80#64) (input.add 120#64)) out = _
    erw [mulState_read_frame s2 (out.add 80#64) (input.add 80#64) (input.add 120#64) out
      (smallRange_add ho2 (k := 80) (by decide)) h02 hd02,
      mulState_read_frame s1 (out.add 40#64) (input.add 40#64) (input.add 80#64) out
        (smallRange_add ho1 (k := 40) (by decide)) h01 hd01,
      mulState_read_self s out input (input.add 120#64) h0]
    rfl
  · change readLimbs (mulState s2 (out.add 80#64) (input.add 80#64) (input.add 120#64)) (out.add 40#64) = _
    erw [mulState_read_frame s2 (out.add 80#64) (input.add 80#64) (input.add 120#64) (out.add 40#64)
      (smallRange_add ho2 (k := 80) (by decide))
      (smallRange_add ho2 (k := 40) (by decide)) hd12,
      mulState_read_self s1 (out.add 40#64) (input.add 40#64) (input.add 80#64)
        (smallRange_add ho1 (k := 40) (by decide))]
    simp (disch := simpa only [Pointer.add_id] using hne) only [s1, mulState_read_ne]
    rfl
  · change readLimbs (mulState s2 (out.add 80#64) (input.add 80#64) (input.add 120#64)) (out.add 80#64) = _
    erw [mulState_read_self s2 (out.add 80#64) (input.add 80#64) (input.add 120#64)
      (smallRange_add ho2 (k := 80) (by decide))]
    simp (disch := simpa only [Pointer.add_id] using hne) only [s2, s1, mulState_read_ne]
    rfl
  · rfl


theorem doubleState_range (h : SmallRange s.mem q n) (out input : Pointer) :
    SmallRange (doubleState s out input).mem q n := smallRange_storePointWords h _ _

/-- Readback of the exact twenty stores of the imported double helper. -/
theorem doubleState_read (s : GlobalState) (out input : Pointer)
    (hout : SmallRange s.mem out 160) :
    readWordPoint (doubleState s out input) out = SerialPoint.doubleWord (readWordPoint s input) := by
  unfold doubleState
  rw [readWordPoint_eq, pointPost_readback s out _ 5 hout, doubleWordTrace_eq,
    pointFromWords_toWords, ← readWordPoint_eq]

def convert4State (s : GlobalState) (out input : Pointer) : GlobalState :=
  mulState (convert3State s out input) (out.add 120#64) input (input.add 40#64)

theorem convert3State_read_ne (s : GlobalState) (out input q : Pointer)
    (hne : out.id ≠ q.id) :
    readWordPoint (convert3State s out input) q = readWordPoint s q := by
  apply PointArithmetic.Extended.ext <;>
    simp (disch := simpa only [Pointer.add_id] using hne) only [readWordPoint, convert3State, mulState_read_ne]

theorem convert4State_read (s : GlobalState) (out input : Pointer)
    (hout : SmallRange s.mem out 160) (hne : out.id ≠ input.id) :
    readWordPoint (convert4State s out input) out = asExtendedWord (readWordPoint s input) := by
  have ho3 := convert3State_range hout out input
  have ho120 := smallRange_add hout (k := 0) (count := 120) (by decide)
  simp only [Pointer.add_zero] at ho120
  have h3 := convert3State_read s out input ho120 hne
  have hs := convert3State_read_ne s out input input hne
  have hd (k : Nat) (hk : k + 40 ≤ 120) :
      (Range.of (out.add (BitVec.ofNat 64 k)) 320).Disjoint (Range.of (out.add 120#64) 320) :=
    subranges_disjoint hout (i := k) (j := 120) (ni := 40) (nj := 40)
      (by omega) (by decide) (Or.inl hk)
  apply PointArithmetic.Extended.ext
  · change readLimbs (mulState (convert3State s out input) (out.add 120#64) input (input.add 40#64)) out = _
    have h0 := smallRange_add ho3 (k := 0) (count := 40) (by decide)
    have hd0 := hd 0 (by decide)
    simp only [Pointer.add_zero] at h0 hd0
    erw [mulState_read_frame _ _ _ _ _ (smallRange_add ho3 (k := 120) (by decide)) h0 hd0]
    exact congrArg PointArithmetic.Extended.X h3
  · change readLimbs (mulState (convert3State s out input) (out.add 120#64) input (input.add 40#64)) (out.add 40#64) = _
    erw [mulState_read_frame _ _ _ _ _ (smallRange_add ho3 (k := 120) (by decide))
      (smallRange_add ho3 (k := 40) (by decide)) (hd 40 (by decide))]
    exact congrArg PointArithmetic.Extended.Y h3
  · change readLimbs (mulState (convert3State s out input) (out.add 120#64) input (input.add 40#64)) (out.add 80#64) = _
    erw [mulState_read_frame _ _ _ _ _ (smallRange_add ho3 (k := 120) (by decide))
      (smallRange_add ho3 (k := 80) (by decide)) (hd 80 (by decide))]
    exact congrArg PointArithmetic.Extended.Z h3
  · change readLimbs (mulState (convert3State s out input) (out.add 120#64) input (input.add 40#64)) (out.add 120#64) = _
    erw [mulState_read_self _ _ _ _ (smallRange_add ho3 (k := 120) (by decide))]
    have hx := congrArg PointArithmetic.Extended.X hs
    have hy := congrArg PointArithmetic.Extended.Y hs
    change readLimbs (convert3State s out input) input = readLimbs s input at hx
    change readLimbs (convert3State s out input) (input.add 40#64) = readLimbs s (input.add 40#64) at hy
    rw [hx, hy]
    rfl

/-- The final conversion uses the same four products as the word formula. -/
theorem finalState_read (s : GlobalState) (out completed projective : Pointer)
    (hout : SmallRange s.mem out 160) (hcompleted : SmallRange s.mem completed 160)
    (hne : out.id ≠ completed.id) :
    readWordPoint (finalState s out completed projective) out = twiceWord (readWordPoint s projective) := by
  change readWordPoint (convert4State (doubleState s completed projective) out completed) out = _
  rw [convert4State_read _ out completed (doubleState_range hout _ _) hne,
    doubleState_read s completed projective hcompleted]
  rfl

theorem copyState_range (h : SmallRange s.mem q bytes) (out input : Pointer) (n : Nat) :
    SmallRange (copyState s out input n).mem q bytes := h.storeAt _ _

/-- A memcpy copies every complete five-limb coordinate inside its range. -/
theorem copyState_read_limbs (s : GlobalState) (out input : Pointer) (n k : Nat)
    (hout : SmallRange s.mem out n) (hin : SmallRange s.mem input n) (hk : k + 40 ≤ n) :
    readLimbs (copyState s out input n) (out.add (BitVec.ofNat 64 k)) =
      readLimbs s (input.add (BitVec.ofNat 64 k)) := by
  funext i
  have hoff : k + 8*i.val < 2^64 := by have := hout.offset_lt; omega
  have hbits : (BitVec.ofNat 64 (k + 8*i.val)).toNat * 8 + 64 ≤ 8*n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
    omega
  have hd := MemoryState.readAt_storeAt_add hout.fits
    (hout.no_wrap (k := k + 8*i.val) (by omega)) hbits (s.mem.readAt input (8*n))
  have hs := MemoryState.readAt_add_of_readAt hin.fits
    (hin.no_wrap (k := k + 8*i.val) (by omega)) hbits (rfl : s.mem.readAt input (8*n) = _)
  simpa only [copyState, readLimbs, Pointer.add_add, ← BitVec.ofNat_add] using hd.trans hs.symm


/-- The projective memcpy transports exactly the three coordinates used by
the next doubling; no fourth-coordinate read is required. -/
theorem copyState_xyz (s : GlobalState) (out input : Pointer)
    (hout : SmallRange s.mem out 120) (hin : SmallRange s.mem input 120) :
    xyz (readWordPoint (copyState s out input 120) out) = xyz (readWordPoint s input) := by
  have h0 := copyState_read_limbs s out input 120 0 hout hin (by decide)
  have h1 := copyState_read_limbs s out input 120 40 hout hin (by decide)
  have h2 := copyState_read_limbs s out input 120 80 hout hin (by decide)
  simp only [Pointer.add_zero] at h0
  apply PointArithmetic.Extended.ext
  · exact h0
  · exact h1
  · exact h2
  · rfl

theorem loopState_range (h : SmallRange s.mem q n) (completed projective temporary : Pointer) :
    SmallRange (loopState s completed projective temporary).mem q n :=
  copyState_range (convert3State_range (doubleState_range h _ _) _ _) _ _ _

/-- Exact word readback of one complete cofactor loop iteration. -/
theorem loopState_read (s : GlobalState) (completed projective temporary : Pointer)
    (hc : SmallRange s.mem completed 160) (hp : SmallRange s.mem projective 120)
    (ht : SmallRange s.mem temporary 120) (hne : temporary.id ≠ completed.id) :
    xyz (readWordPoint (loopState s completed projective temporary) projective) =
      xyz (twiceWord (readWordPoint s projective)) := by
  change xyz (readWordPoint (copyState (convert3State (doubleState s completed projective)
    temporary completed) projective temporary 120) projective) = _
  rw [copyState_xyz _ projective temporary
      (convert3State_range (doubleState_range hp _ _) _ _)
      (convert3State_range (doubleState_range ht _ _) _ _),
    convert3State_read _ temporary completed (doubleState_range ht _ _) hne,
    doubleState_read s completed projective hc]
  rfl

/-- Two projective iterations followed by the extended final block realize
exactly the three word doublings, despite the omitted intermediate T stores. -/
theorem threeDoublings_read (s : GlobalState) (out completedFinal completedLoop projective temporary : Pointer)
    (ho : SmallRange s.mem out 160) (hf : SmallRange s.mem completedFinal 160)
    (hc : SmallRange s.mem completedLoop 160) (hp : SmallRange s.mem projective 120)
    (ht : SmallRange s.mem temporary 120)
    (hneLoop : temporary.id ≠ completedLoop.id) (hneFinal : out.id ≠ completedFinal.id) :
    readWordPoint (finalState
      (loopState (loopState s completedLoop projective temporary) completedLoop projective temporary)
      out completedFinal projective) out = eightTimesWord (readWordPoint s projective) := by
  let s1 := loopState s completedLoop projective temporary
  let s2 := loopState s1 completedLoop projective temporary
  have h1 := loopState_read s completedLoop projective temporary hc hp ht hneLoop
  have h2 := loopState_read s1 completedLoop projective temporary
    (loopState_range hc _ _ _) (loopState_range hp _ _ _) (loopState_range ht _ _ _) hneLoop
  have ht1 : twiceWord (readWordPoint s1 projective) =
      twiceWord (twiceWord (readWordPoint s projective)) := by
    have h := congrArg twiceWord h1
    simpa only [twiceWord_xyz] using h
  have ht2 : twiceWord (readWordPoint s2 projective) =
      twiceWord (twiceWord (readWordPoint s1 projective)) := by
    have h := congrArg twiceWord h2
    simpa only [twiceWord_xyz] using h
  rw [finalState_read _ out completedFinal projective
    (loopState_range (loopState_range ho _ _ _) _ _ _)
    (loopState_range (loopState_range hf _ _ _) _ _ _) hneFinal]
  change twiceWord (readWordPoint s2 projective) = _
  rw [ht2, ht1]
  rfl


theorem copyState_read_ne (s : GlobalState) (out input q : Pointer) (n : Nat)
    (hne : out.id ≠ q.id) :
    readLimbs (copyState s out input n) q = readLimbs s q := by
  funext i
  apply MemoryState.readAt_storeAt_disjoint
  exact Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne)

theorem copyState_read_frame (s : GlobalState) (out input q : Pointer) (n : Nat)
    (hq : SmallRange s.mem q 40)
    (hd : (Range.of q 320).Disjoint (Range.of out (8*n))) :
    readLimbs (copyState s out input n) q = readLimbs s q := by
  funext i
  apply MemoryState.readAt_storeAt_disjoint
  exact (limb_disjoint_of_range hq hd.symm (8*i.val) (by omega)).symm

theorem initialState_range (h : SmallRange s.mem q n) (out input : Pointer) :
    SmallRange (initialState s out input).mem q n :=
  copyState_range (copyState_range (copyState_range h _ _ _) _ _ _) _ _ _

theorem initialState_read (s : GlobalState) (out input : Pointer)
    (hout : SmallRange s.mem out 120) (hin : SmallRange s.mem input 120)
    (hne : out.id ≠ input.id) :
    xyz (readWordPoint (initialState s out input) out) = xyz (readWordPoint s input) := by
  let s1 := copyState s (out.add 40#64) (input.add 40#64) 40
  let s2 := copyState s1 (out.add 80#64) (input.add 80#64) 40
  have ho1 : SmallRange s1.mem out 120 := copyState_range hout _ _ _
  have ho2 : SmallRange s2.mem out 120 := copyState_range ho1 _ _ _
  have hi1 : SmallRange s1.mem input 120 := copyState_range hin _ _ _
  have hi2 : SmallRange s2.mem input 120 := copyState_range hi1 _ _ _
  have ho0 := smallRange_add ho2 (k := 0) (count := 40) (by decide)
  have hi0 := smallRange_add hi2 (k := 0) (count := 40) (by decide)
  simp only [Pointer.add_zero] at ho0 hi0
  have hd (i j : Nat) (hi : i + 40 ≤ 120) (hj : j + 40 ≤ 120)
      (hij : i + 40 ≤ j ∨ j + 40 ≤ i) :
      (Range.of (out.add (BitVec.ofNat 64 i)) 320).Disjoint
        (Range.of (out.add (BitVec.ofNat 64 j)) 320) :=
    subranges_disjoint hout hi hj hij
  have hd10 := hd 40 0 (by decide) (by decide) (by decide)
  have hd20 := hd 80 0 (by decide) (by decide) (by decide)
  simp only [Pointer.add_zero] at hd10 hd20
  apply PointArithmetic.Extended.ext
  · change readLimbs (copyState s2 out input 40) out = _
    have h := copyState_read_limbs s2 out input 40 0 ho0 hi0 (by decide)
    simp only [Pointer.add_zero] at h
    rw [h]
    simp (disch := simpa only [Pointer.add_id] using hne) only [s2, s1, copyState_read_ne]
    rfl
  · change readLimbs (copyState s2 out input 40) (out.add 40#64) = _
    erw [copyState_read_frame _ out input (out.add 40#64) 40
      (smallRange_add ho2 (k := 40) (by decide)) hd10,
      copyState_read_frame s1 (out.add 80#64) (input.add 80#64) (out.add 40#64) 40
        (smallRange_add ho1 (k := 40) (by decide)) (hd 40 80 (by decide) (by decide) (by decide))]
    have h := copyState_read_limbs s (out.add 40#64) (input.add 40#64) 40 0
      (smallRange_add hout (k := 40) (by decide)) (smallRange_add hin (k := 40) (by decide)) (by decide)
    simpa only [Pointer.add_zero, s1, xyz, readWordPoint] using h
  · change readLimbs (copyState s2 out input 40) (out.add 80#64) = _
    erw [copyState_read_frame _ out input (out.add 80#64) 40
      (smallRange_add ho2 (k := 80) (by decide)) hd20]
    have h := copyState_read_limbs s1 (out.add 80#64) (input.add 80#64) 40 0
      (smallRange_add ho1 (k := 80) (by decide)) (smallRange_add hi1 (k := 80) (by decide)) (by decide)
    simp only [Pointer.add_zero] at h
    rw [h]
    simp (disch := simpa only [Pointer.add_id] using hne) only [s1, copyState_read_ne]
    rfl
  · rfl


theorem readWordPoint_alloca (s : GlobalState) (p : Pointer) (n : Nat)
    (hne : p.id ≠ s.allocaPtr.id) : readWordPoint (s.alloca n) p = readWordPoint s p := by
  have hr (q : Pointer) (h : q.id ≠ s.allocaPtr.id) :
      readLimbs (s.alloca n) q = readLimbs s q := by
    funext i
    apply readAt_alloca_ne
    simpa only [Pointer.add_id] using h
  apply PointArithmetic.Extended.ext <;> apply hr <;>
    simpa only [Pointer.add_id] using hne

theorem readWordPoint_erase (s : GlobalState) (p : Pointer) (mark : Nat)
    (h : p.id.id < mark) :
    readWordPoint {s with mem := s.mem.eraseFrom mark} p = readWordPoint s p := by
  have hr (q : Pointer) (hq : q.id.id < mark) :
      readLimbs {s with mem := s.mem.eraseFrom mark} q = readLimbs s q := by
    funext i
    apply Verifier.Execution.Key.erase_read
    simpa only [Pointer.add_id] using hq
  apply PointArithmetic.Extended.ext <;> apply hr <;>
    simpa only [Pointer.add_id] using h

/-- The complete finite cofactor memory schedule returns exactly the word
representative used by `timesEight`, including the caller-frame erasure. -/
theorem cofactorState_read (s : GlobalState) (out input : Pointer) (hwf : s.WF)
    (hout : SmallRange s.mem out 160) (hin : SmallRange s.mem input 120) :
    readWordPoint (cofactorState s out input) out = eightTimesWord (readWordPoint s input) := by
  let s1 := s.alloca 160
  let s2 := s1.alloca 120
  let s3 := s2.alloca 120
  let base := s3.alloca 160
  let completedFinal := s.allocaPtr
  let temporary := s1.allocaPtr
  let projective := s2.allocaPtr
  let completedLoop := s3.allocaPtr
  let initialized := initialState base projective input
  have wf1 : s1.WF := hwf.alloca
  have wf2 : s2.WF := wf1.alloca
  have wf3 : s3.WF := wf2.alloca
  have ho1 : SmallRange s1.mem out 160 := smallRange_alloca hwf hout
  have ho2 : SmallRange s2.mem out 160 := smallRange_alloca wf1 ho1
  have ho3 : SmallRange s3.mem out 160 := smallRange_alloca wf2 ho2
  have ho : SmallRange base.mem out 160 := smallRange_alloca wf3 ho3
  have hi1 : SmallRange s1.mem input 120 := smallRange_alloca hwf hin
  have hi2 : SmallRange s2.mem input 120 := smallRange_alloca wf1 hi1
  have hi3 : SmallRange s3.mem input 120 := smallRange_alloca wf2 hi2
  have hi : SmallRange base.mem input 120 := smallRange_alloca wf3 hi3
  have hf1 : SmallRange s1.mem completedFinal 160 := smallRange_alloca_self s 160 (by decide)
  have hf2 : SmallRange s2.mem completedFinal 160 := smallRange_alloca wf1 hf1
  have hf3 : SmallRange s3.mem completedFinal 160 := smallRange_alloca wf2 hf2
  have hf : SmallRange base.mem completedFinal 160 := smallRange_alloca wf3 hf3
  have ht2 : SmallRange s2.mem temporary 120 := smallRange_alloca_self s1 120 (by decide)
  have ht3 : SmallRange s3.mem temporary 120 := smallRange_alloca wf2 ht2
  have ht : SmallRange base.mem temporary 120 := smallRange_alloca wf3 ht3
  have hp3 : SmallRange s3.mem projective 120 := smallRange_alloca_self s2 120 (by decide)
  have hp : SmallRange base.mem projective 120 := smallRange_alloca wf3 hp3
  have hc : SmallRange base.mem completedLoop 160 := smallRange_alloca_self s3 160 (by decide)
  have hnpi : projective.id ≠ input.id :=
    (GlobalState.ne_allocaPtr_of_fits wf2 hi2.fits).symm
  have hntc : temporary.id ≠ completedLoop.id := GlobalState.ne_allocaPtr_of_fits wf3 ht3.fits
  have hnof : out.id ≠ completedFinal.id := GlobalState.ne_allocaPtr_of_fits hwf hout.fits
  have hinit := initialState_read base projective input hp hi hnpi
  have hreadBase : readWordPoint base input = readWordPoint s input := by
    rw [readWordPoint_alloca s3 input 160 (GlobalState.ne_allocaPtr_of_fits wf3 hi3.fits),
      readWordPoint_alloca s2 input 120 (GlobalState.ne_allocaPtr_of_fits wf2 hi2.fits),
      readWordPoint_alloca s1 input 120 (GlobalState.ne_allocaPtr_of_fits wf1 hi1.fits),
      readWordPoint_alloca s input 160 (GlobalState.ne_allocaPtr_of_fits hwf hin.fits)]
  have hinitTwice : twiceWord (readWordPoint initialized projective) =
      twiceWord (readWordPoint s input) := by
    have hh := congrArg twiceWord hinit
    simpa only [twiceWord_xyz, hreadBase] using hh
  change readWordPoint {finalState
    (loopState (loopState initialized completedLoop projective temporary) completedLoop projective temporary)
    out completedFinal projective with mem := (finalState
      (loopState (loopState initialized completedLoop projective temporary) completedLoop projective temporary)
      out completedFinal projective).mem.eraseFrom s.alloc.nextFreeBlock} out = _
  rw [readWordPoint_erase _ out _ (hwf.lt hout.fits.mem),
    threeDoublings_read initialized out completedFinal completedLoop projective temporary
      (initialState_range ho _ _) (initialState_range hf _ _) (initialState_range hc _ _)
      (initialState_range hp _ _) (initialState_range ht _ _) hntc hnof]
  unfold eightTimesWord
  rw [hinitTwice]

end Agave.Ed25519.SmallOrder.Execution
