import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityCall
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointRepresentation

/-! Readback of the whole equality result as the four actual field products
and two canonical encodings, without reference to private scratch memory. -/
namespace Agave.Ed25519.SmallOrder.Execution.EqualityResult
open LeanMLIR.RIR Verifier.Execution.PointConstantTimeEq
open Verifier.Execution.Dalek (ReadOnlyFrame choiceByte)
open Reduce64.Execution (SmallRange)
open EqualityAllocation EqualityPhases EqualityCall SerialPoint.Execution
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

@[simp] theorem slot0_id (s : GlobalState) :
    (slot0 s).id.id = s.alloc.nextFreeBlock + 0 := by
  simp [slot0, state0, GlobalState.allocaPtr]

@[simp] theorem slot1_id (s : GlobalState) :
    (slot1 s).id.id = s.alloc.nextFreeBlock + 1 := by
  simp [slot1, state0, state1, GlobalState.alloca, GlobalState.allocaPtr]

@[simp] theorem slot2_id (s : GlobalState) :
    (slot2 s).id.id = s.alloc.nextFreeBlock + 2 := by
  simp [slot2, state0, state1, state2, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot3_id (s : GlobalState) :
    (slot3 s).id.id = s.alloc.nextFreeBlock + 3 := by
  simp [slot3, state0, state1, state2, state3, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot4_id (s : GlobalState) :
    (slot4 s).id.id = s.alloc.nextFreeBlock + 4 := by
  simp [slot4, state0, state1, state2, state3, state4, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot5_id (s : GlobalState) :
    (slot5 s).id.id = s.alloc.nextFreeBlock + 5 := by
  simp [slot5, state0, state1, state2, state3, state4, state5, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot6_id (s : GlobalState) :
    (slot6 s).id.id = s.alloc.nextFreeBlock + 6 := by
  simp [slot6, state0, state1, state2, state3, state4, state5, state6, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot7_id (s : GlobalState) :
    (slot7 s).id.id = s.alloc.nextFreeBlock + 7 := by
  simp [slot7, state0, state1, state2, state3, state4, state5, state6, state7, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

theorem caller_id_lt {s : GlobalState} {q : Pointer} {n : Nat} (hwf : s.WF) (h : SmallRange s.mem q n) :
    q.id.id < s.alloc.nextFreeBlock := by
  exact hwf.lt h.fits.mem

theorem different_id {a b : Pointer} (h : a.id.id ≠ b.id.id) : a.id ≠ b.id :=
  ne_of_apply_ne BlockId.id h

theorem serial_read (s : GlobalState) (r a q : Pointer) (w : Nat) (h : r.id ≠ q.id) :
    (serialPost s r a).mem.readAt q w = s.mem.readAt q w :=
  Encoding.Decompress.Execution.ToBytes.readAt_storeBytes_of_ne _ _ _ _ _ h

theorem serial_limbs (s : GlobalState) (r a q : Pointer) (h : r.id ≠ q.id) :
    SerialFieldMul.readLimbs (serialPost s r a) q = SerialFieldMul.readLimbs s q := by
  funext i
  exact serial_read s r a _ 64 (by simpa only [Pointer.add_id] using h)

theorem mul_read (s : GlobalState) (r a b q : Pointer) (w : Nat) (h : r.id ≠ q.id) :
    (mulPost s r a b).mem.readAt q w = s.mem.readAt q w :=
  readAt_storeLimbs_ne _ _ _ _ _ h

theorem mul_limbs (s : GlobalState) (r a b q : Pointer) (h : r.id ≠ q.id) :
    SerialFieldMul.readLimbs (mulPost s r a b) q = SerialFieldMul.readLimbs s q :=
  readLimbs_storeLimbs_ne _ _ _ _ h

theorem allocated_limbs (s : GlobalState) (q : Pointer) (hwf : s.WF)
    (hq : SmallRange s.mem q 40) :
    SerialFieldMul.readLimbs (allocated s) q = SerialFieldMul.readLimbs s q := by
  funext i
  exact state8_read s hwf (q.add (BitVec.ofNat 64 (8*i.val))) 8 64
    (smallRange_add hq (k := 8*i.val) (count := 8) (by omega))

theorem machineBytes_packed (a : Field.Serial) :
    Encoding.machineBytes a = Encoding.packedBytes (Encoding.tightWords a) := by
  unfold Encoding.machineBytes
  rw [Encoding.machine3_pack, Encoding.machine2_pack, Encoding.machine1_pack,
    Encoding.machine0_pack]
  rfl

/-- The second serializer preserves the first byte buffer, and its source
field was preserved by the first serializer. -/
theorem serial_pair (s : GlobalState) (dl dr al ar : Pointer)
    (hl : SmallRange s.mem dl 32) (hr : SmallRange s.mem dr 32)
    (hd : dr.id ≠ dl.id) (ha : dl.id ≠ ar.id) :
    let t := serialPost (serialPost s dl al) dr ar
    (t.mem.readAt dl 256 = t.mem.readAt dr 256) ↔
      Encoding.machineBytes (SerialFieldMul.readLimbs s al) =
      Encoding.machineBytes (SerialFieldMul.readLimbs s ar) := by
  dsimp only
  rw [serial_read _ dr ar dl 256 hd]
  change (Encoding.Decompress.Execution.ToBytes.storeBytes s.mem dl
    (Encoding.Decompress.Execution.ToBytes.machine (SerialFieldMul.readLimbs s al))).readAt dl 256 = _ ↔ _
  rw [Encoding.Decompress.Execution.ToBytes.storeBytes_read256 _ _ _ hl]
  change _ = (Encoding.Decompress.Execution.ToBytes.storeBytes (serialPost s dl al).mem dr
    (Encoding.Decompress.Execution.ToBytes.machine (SerialFieldMul.readLimbs (serialPost s dl al) ar))).readAt dr 256 ↔ _
  rw [Encoding.Decompress.Execution.ToBytes.storeBytes_read256 _ _ _ (serial_live s dl al dr 32 hr),
    serial_limbs _ _ _ _ ha]
  simp only [machineBytes_packed]

/-- Scratch allocations are disjoint from every readable caller coordinate. -/
theorem xCompared_limbs (s : GlobalState) (l r q : Pointer) (hwf : s.WF)
    (hq : SmallRange s.mem q 40) :
    SerialFieldMul.readLimbs (xCompared s l r) q = SerialFieldMul.readLimbs s q := by
  have hq' := caller_id_lt hwf hq
  have h2 : (slot2 s).id ≠ q.id := different_id (by simp only [slot2_id]; omega)
  have h3 : (slot3 s).id ≠ q.id := different_id (by simp only [slot3_id]; omega)
  have h6 : (slot6 s).id ≠ q.id := different_id (by simp only [slot6_id]; omega)
  have h7 : (slot7 s).id ≠ q.id := different_id (by simp only [slot7_id]; omega)
  change SerialFieldMul.readLimbs (xRight s l r) q = _
  rw [xRight, serial_limbs _ _ _ _ h2, xLeft, serial_limbs _ _ _ _ h3]
  rw [xProducts, productXState, mul_limbs _ _ _ _ _ h6, mul_limbs _ _ _ _ _ h7]
  exact allocated_limbs s q hwf hq

def rawResult (s : GlobalState) (l r : Pointer) : BitVec 8 :=
  let xl := SerialFieldMul.machine (SerialFieldMul.readLimbs s l) (SerialFieldMul.readLimbs s (r.add 80#64))
  let xr := SerialFieldMul.machine (SerialFieldMul.readLimbs s r) (SerialFieldMul.readLimbs s (l.add 80#64))
  let yl := SerialFieldMul.machine (SerialFieldMul.readLimbs s (l.add 40#64)) (SerialFieldMul.readLimbs s (r.add 80#64))
  let yr := SerialFieldMul.machine (SerialFieldMul.readLimbs s (r.add 40#64)) (SerialFieldMul.readLimbs s (l.add 80#64))
  choiceByte (decide (Encoding.machineBytes xl = Encoding.machineBytes xr) &&
    decide (Encoding.machineBytes yl = Encoding.machineBytes yr))

theorem result_eq_raw (s : GlobalState) (l r : Pointer) (hwf : s.WF)
    (hl : SmallRange s.mem l 160) (hr : SmallRange s.mem r 160) :
    result s l r = rawResult s l r := by
  have hl0 : SmallRange s.mem l 40 := by
    simpa only [Pointer.add_zero] using smallRange_add hl (k := 0) (count := 40) (by decide)
  have hr0 : SmallRange s.mem r 40 := by
    simpa only [Pointer.add_zero] using smallRange_add hr (k := 0) (count := 40) (by decide)
  have hl40 := smallRange_add hl (k := 40) (count := 40) (by decide)
  have hr40 := smallRange_add hr (k := 40) (count := 40) (by decide)
  have hl80 := smallRange_add hl (k := 80) (count := 40) (by decide)
  have hr80 := smallRange_add hr (k := 80) (count := 40) (by decide)
  have il := caller_id_lt hwf hl
  have ir := caller_id_lt hwf hr
  have lx : Live (allocated s) (xProducts s l r) := productsX_live _ _ _ _ _
  have ly : Live (allocated s) (yProducts s l r) :=
    live_trans (live_trans (live_trans lx (serial_live _ _ _)) (serial_live _ _ _))
      (productsY_live _ _ _ _ _)
  have hx := serial_pair (xProducts s l r) (slot3 s) (slot2 s) (slot7 s) (slot6 s)
    (lx _ _ (slot3_live s hwf)) (lx _ _ (slot2_live s hwf))
    (different_id (by simp only [slot2_id, slot3_id]; omega))
    (different_id (by simp only [slot3_id, slot6_id]; omega))
  have hy := serial_pair (yProducts s l r) (slot1 s) (slot0 s) (slot5 s) (slot4 s)
    (ly _ _ (slot1_live s hwf)) (ly _ _ (slot0_live s hwf))
    (different_id (by simp only [slot0_id, slot1_id]; omega))
    (different_id (by simp only [slot1_id, slot4_id]; omega))
  have hxl : SerialFieldMul.readLimbs (xProducts s l r) (slot7 s) =
      SerialFieldMul.machine (SerialFieldMul.readLimbs s l) (SerialFieldMul.readLimbs s (r.add 80#64)) := by
    rw [xProducts, productXState, mul_limbs _ _ _ _ _
      (different_id (by simp only [slot6_id, slot7_id]; omega)),
      mulPost_readback _ _ _ _ (slot7_live s hwf),
      allocated_limbs s l hwf hl0, allocated_limbs s (r.add 80#64) hwf hr80]
  have hxr : SerialFieldMul.readLimbs (xProducts s l r) (slot6 s) =
      SerialFieldMul.machine (SerialFieldMul.readLimbs s r) (SerialFieldMul.readLimbs s (l.add 80#64)) := by
    rw [xProducts, productXState, mulPost_readback _ _ _ _
      (mulPost_smallRange _ _ _ _ _ (slot6_live s hwf)),
      mul_limbs _ _ _ _ _ (different_id (by simp only [slot7_id]; omega)),
      mul_limbs _ _ _ _ _ (different_id (by simp only [slot7_id, Pointer.add_id]; omega)),
      allocated_limbs s r hwf hr0, allocated_limbs s (l.add 80#64) hwf hl80]
  have lyr : Live (allocated s) (xCompared s l r) :=
    live_trans (live_trans lx (serial_live _ _ _)) (serial_live _ _ _)
  have hyl : SerialFieldMul.readLimbs (yProducts s l r) (slot5 s) =
      SerialFieldMul.machine (SerialFieldMul.readLimbs s (l.add 40#64)) (SerialFieldMul.readLimbs s (r.add 80#64)) := by
    rw [yProducts, productYState, mul_limbs _ _ _ _ _
      (different_id (by simp only [slot4_id, slot5_id]; omega)),
      mulPost_readback _ _ _ _ (lyr _ _ (slot5_live s hwf)),
      xCompared_limbs s l r (l.add 40#64) hwf hl40, xCompared_limbs s l r (r.add 80#64) hwf hr80]
  have hyr : SerialFieldMul.readLimbs (yProducts s l r) (slot4 s) =
      SerialFieldMul.machine (SerialFieldMul.readLimbs s (r.add 40#64)) (SerialFieldMul.readLimbs s (l.add 80#64)) := by
    rw [yProducts, productYState, mulPost_readback _ _ _ _
      (mulPost_smallRange _ _ _ _ _ (lyr _ _ (slot4_live s hwf))),
      mul_limbs _ _ _ _ _ (different_id (by simp only [slot5_id, Pointer.add_id]; omega)),
      mul_limbs _ _ _ _ _ (different_id (by simp only [slot5_id, Pointer.add_id]; omega)),
      xCompared_limbs s l r (r.add 40#64) hwf hr40, xCompared_limbs s l r (l.add 80#64) hwf hl80]
  simp only [result, xEqual, yEqual, rawResult, xRight, xLeft, yRight, yLeft,
    hx, hy, hxl, hxr, hyl, hyr]

/-- Eight equality-frame allocations, two 33-allocation byte comparisons,
and the final one-allocation volatile black box. All 75 blocks are reclaimed. -/
theorem finished_alloc (s : GlobalState) (l r : Pointer) :
    (finished s l r).alloc = ⟨s.alloc.nextFreeBlock + 75⟩ := by
  simp [finished, yCompared, yRight, yLeft, yProducts, xCompared, xRight, xLeft,
    xProducts, advance, serialPost, productXState, productYState, mulPost,
    allocated, state8, state7, state6, state5, state4, state3, state2, state1,
    state0, GlobalState.alloca, Nat.add_assoc]

theorem call_raw_exact (s : GlobalState) (l r : Pointer) (hwf : s.WF)
    (hl : SmallRange s.mem l 160) (hr : SmallRange s.mem r 160) :
    equalityProgram.call (program.args (.value l) (.value r)) s =
      .value (.cons (.value (rawResult s l r)) .nil, advance s 75) := by
  simpa only [result_eq_raw s l r hwf hl hr, finished_alloc, advance] using
    call_exact s l r hwf hl hr

/-- Whole-call refinement with a result expressed solely in the input memory. -/
theorem call_raw (s : GlobalState) (l r : Pointer) (hwf : s.WF)
    (hl : SmallRange s.mem l 160) (hr : SmallRange s.mem r 160) :
    ∃ t, equalityProgram.call (program.args (.value l) (.value r)) s =
      .value (.cons (.value (rawResult s l r)) .nil, t) ∧ ReadOnlyFrame s t := by
  simpa only [result_eq_raw s l r hwf hl hr] using call_contract s l r hwf hl hr

end Agave.Ed25519.SmallOrder.Execution.EqualityResult
