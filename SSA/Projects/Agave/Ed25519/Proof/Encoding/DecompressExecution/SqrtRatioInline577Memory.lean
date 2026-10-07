import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Loads

/-! Exact state transformer and frames for the two serializers before pc947.
The sequential transformer allows overlapping input/output buffers; separation
is required only to relate both outputs to the original input words. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open Verifier.Execution.Dalek (ReadBytes)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes

def serialize (s : GlobalState) (r : Pointer) (x : Words) : GlobalState :=
  {s with mem := ToBytes.storeBytes s.mem r (ToBytes.machine x)}

def resultState (s : GlobalState) (a b r q : Pointer) : GlobalState :=
  let first := serialize s r (readLimbs s a)
  serialize first q (readLimbs first b)

theorem serialize_alloc (s : GlobalState) (r : Pointer) (x : Words) :
    (serialize s r x).alloc = s.alloc := by
  simp only [serialize]

theorem serialize_live (s : GlobalState) (r : Pointer) (x : Words)
    {p : Pointer} {n : Nat} (h : SmallRange s.mem p n) :
    SmallRange (serialize s r x).mem p n := ToBytes.smallRange_storeBytes h r _

theorem serialize_read (s : GlobalState) (r : Pointer) (x : Words)
    (p : Pointer) (w : Nat) (h : r.id ≠ p.id) :
    (serialize s r x).mem.readAt p w = s.mem.readAt p w :=
  ToBytes.readAt_storeBytes_of_ne s.mem r p _ w h

theorem serialize_words (s : GlobalState) (r : Pointer) (x : Words)
    (p : Pointer) (h : r.id ≠ p.id) :
    readLimbs (serialize s r x) p = readLimbs s p := by
  funext i
  exact serialize_read s r x (p.add _) 64 h

theorem serialize_wf (s : GlobalState) (r : Pointer) (x : Words) (h : s.WF) :
    (serialize s r x).WF := ToBytes.wf_storeBytes h r _

theorem serialize_canonical (s : GlobalState) (r : Pointer) (x : Words)
    (h : SmallRange s.mem r 32) :
    (serialize s r x).mem.readAt r 256 = canonicalWord x :=
  ToBytes.storeBytes_read256 s.mem r x h

theorem serialize_private (s : GlobalState) (r : Pointer) (x : Words)
    (mark : Nat) (h : mark ≤ r.id.id) :
    (serialize s r x).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  have step (m : MemoryState) (off : BitVec 64) (byte : BitVec 8) :
      (m.storeAt (r.add off) byte).eraseFrom mark = m.eraseFrom mark :=
    MemoryState.eraseFrom_storeAt.trans (MemoryState.storeAt_eraseFrom_of_le h)
  simp only [serialize,ToBytes.storeBytes,step]

theorem result_alloc (s : GlobalState) (a b r q : Pointer) :
    (resultState s a b r q).alloc = s.alloc := by
  simp only [resultState,serialize_alloc]

theorem result_wf (s : GlobalState) (a b r q : Pointer) (h : s.WF) :
    (resultState s a b r q).WF :=
  serialize_wf _ q _ (serialize_wf s r _ h)

theorem result_live (s : GlobalState) (a b r q : Pointer)
    {p : Pointer} {n : Nat} (h : SmallRange s.mem p n) :
    SmallRange (resultState s a b r q).mem p n :=
  serialize_live _ q _ (serialize_live s r _ h)

theorem result_read (s : GlobalState) (a b r q p : Pointer) (w : Nat)
    (hr : r.id ≠ p.id) (hq : q.id ≠ p.id) :
    (resultState s a b r q).mem.readAt p w = s.mem.readAt p w := by
  exact (serialize_read _ q _ p w hq).trans (serialize_read s r _ p w hr)

theorem result_words (s : GlobalState) (a b r q p : Pointer)
    (hr : r.id ≠ p.id) (hq : q.id ≠ p.id) :
    readLimbs (resultState s a b r q) p = readLimbs s p := by
  funext i
  exact result_read s a b r q (p.add _) 64 hr hq

theorem result_private (s : GlobalState) (a b r q : Pointer) (mark : Nat)
    (hr : mark ≤ r.id.id) (hq : mark ≤ q.id.id) :
    (resultState s a b r q).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  exact (serialize_private _ q _ mark hq).trans (serialize_private s r _ mark hr)

theorem result_first_canonical (s : GlobalState) (a b r q : Pointer)
    (hr : SmallRange s.mem r 32) (hqr : q.id ≠ r.id) :
    (resultState s a b r q).mem.readAt r 256 = canonicalWord (readLimbs s a) := by
  exact (serialize_read _ q _ r 256 hqr).trans (serialize_canonical s r _ hr)

theorem result_second_canonical (s : GlobalState) (a b r q : Pointer)
    (hq : SmallRange s.mem q 32) (hrb : r.id ≠ b.id) :
    (resultState s a b r q).mem.readAt q 256 = canonicalWord (readLimbs s b) := by
  rw [resultState,serialize_canonical _ q _ (serialize_live s r _ hq),
    serialize_words s r _ b hrb]

/-- Both byte-array arguments passed to the actual comparison at pc947. -/
theorem result_comparison_inputs (s : GlobalState) (a b r q : Pointer)
    (hr : SmallRange s.mem r 32) (hq : SmallRange s.mem q 32)
    (hqr : q.id ≠ r.id) (hrb : r.id ≠ b.id) :
    ReadBytes (resultState s a b r q) r 32 (canonicalWord (readLimbs s a)) ∧
    ReadBytes (resultState s a b r q) q 32 (canonicalWord (readLimbs s b)) :=
  ⟨⟨result_live s a b r q hr,result_first_canonical s a b r q hr hqr⟩,
    ⟨result_live s a b r q hq,result_second_canonical s a b r q hq hrb⟩⟩

/-- Canonical comparison is exactly field equality, for arbitrary u64 limbs. -/
theorem result_equal_iff (s : GlobalState) (a b r q : Pointer)
    (hr : SmallRange s.mem r 32) (hq : SmallRange s.mem q 32)
    (hqr : q.id ≠ r.id) (hrb : r.id ≠ b.id) :
    (resultState s a b r q).mem.readAt r 256 =
      (resultState s a b r q).mem.readAt q 256 ↔
      wordValue (readLimbs s a) = wordValue (readLimbs s b) := by
  rw [result_first_canonical s a b r q hr hqr,
    result_second_canonical s a b r q hq hrb,canonicalWord_eq_iff]

theorem result_ready (dg : Decode.Globals) (sg : Globals)
    (s : GlobalState) (a b r q : Pointer) (h : Ready dg sg s)
    (hrd : r.id ≠ dg.address0.id) (hqd : q.id ≠ dg.address0.id)
    (hri : r.id ≠ sg.address0.id) (hqi : q.id ≠ sg.address0.id) :
    Ready dg sg (resultState s a b r q) := by
  exact ⟨⟨result_live s a b r q h.curveD.1,
      (result_read s a b r q dg.address0 320 hrd hqd).trans h.curveD.2⟩,
    ⟨result_live s a b r q h.sqrtM1.1,
      (result_read s a b r q sg.address0 320 hri hqi).trans h.sqrtM1.2⟩⟩

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
