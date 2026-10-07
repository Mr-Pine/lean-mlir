import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioHelperConnectors
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbReadState
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Ready

/-! Exact readback and caller frames for the helper connector states. Arithmetic
stays opaque; these facts identify complete fields, preserve unrelated allocation
records, and transport invocation-local initialized constants. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open SerialPoint.Execution
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
attribute [local irreducible] SerialFieldMul.machine ToBytes.machine

theorem serialize_wf (hwf : s.WF) (out input : Pointer) : (serialize s out input).WF :=
  ToBytes.wf_storeBytes hwf _ _

theorem serialize_live (h : SmallRange s.mem q n) (out input : Pointer) :
    SmallRange (serialize s out input).mem q n := ToBytes.smallRange_storeBytes h _ _

theorem serialize_read (s : GlobalState) (out input : Pointer) (h : SmallRange s.mem out 32) :
    (serialize s out input).mem.readAt out 256 = canonicalWord (readLimbs s input) :=
  ToBytes.storeBytes_read256 s.mem out _ h

theorem serialize_read_other (s : GlobalState) (out input q : Pointer) (w : Nat)
    (h : out.id ≠ q.id) : (serialize s out input).mem.readAt q w = s.mem.readAt q w :=
  ToBytes.readAt_storeBytes_of_ne s.mem out q _ w h

theorem serialize_allocation (s : GlobalState) (out input q : Pointer) (h : q.id ≠ out.id) :
    (serialize s out input).mem[q.id]? = s.mem[q.id]? := by
  have hs (m : MemoryState) (off : BitVec 64) (v : BitVec 8) :
      (m.storeAt (out.add off) v)[q.id]? = m[q.id]? :=
    MemoryState.getElem?_storeAt_ne h
  simp only [serialize, ToBytes.storeBytes, hs]

theorem serialize_private (s : GlobalState) (out input : Pointer) (mark : Nat)
    (h : mark ≤ out.id.id) :
    (serialize s out input).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  have hs (m : MemoryState) (off : BitVec 64) (v : BitVec 8) :
      (m.storeAt (out.add off) v).eraseFrom mark = m.eraseFrom mark := by
    rw [MemoryState.eraseFrom_storeAt,
      MemoryState.storeAt_eraseFrom_of_le (p := out.add off) h]
  simp only [serialize, ToBytes.storeBytes, hs]

theorem serialize_shape (s : GlobalState) (out input : Pointer) (id : BlockId) :
    ((serialize s out input).mem[id]?).map MemoryBlock.length =
      (s.mem[id]?).map MemoryBlock.length := by
  simp only [serialize, ToBytes.storeBytes, storeAt_allocationShape]

theorem multiply_wf (hwf : s.WF) (out a b : Pointer) : (multiply s out a b).WF :=
  wf_storeLimbs hwf _ _

theorem multiply_live (h : SmallRange s.mem q n) (out a b : Pointer) :
    SmallRange (multiply s out a b).mem q n := smallRange_storeLimbs h _ _

theorem multiply_readLimbs (s : GlobalState) (out a b : Pointer)
    (h : SmallRange s.mem out 40) :
    readLimbs (multiply s out a b) out = machine (readLimbs s a) (readLimbs s b) :=
  readLimbs_storeLimbs s out _ h

theorem multiply_read_other (s : GlobalState) (out a b q : Pointer) (w : Nat)
    (h : out.id ≠ q.id) : (multiply s out a b).mem.readAt q w = s.mem.readAt q w :=
  readAt_storeLimbs_ne s.mem out q _ w h

theorem multiply_allocation (s : GlobalState) (out a b q : Pointer) (h : q.id ≠ out.id) :
    (multiply s out a b).mem[q.id]? = s.mem[q.id]? := by
  have hs (m : MemoryState) (off : BitVec 64) (v : BitVec 64) :
      (m.storeAt (out.add off) v)[q.id]? = m[q.id]? :=
    MemoryState.getElem?_storeAt_ne h
  have hz (m : MemoryState) (v : BitVec 64) : (m.storeAt out v)[q.id]? = m[q.id]? :=
    MemoryState.getElem?_storeAt_ne h
  simp only [multiply, storeLimbs, hs, hz]

theorem multiply_private (s : GlobalState) (out a b : Pointer) (mark : Nat)
    (h : mark ≤ out.id.id) :
    (multiply s out a b).mem.eraseFrom mark = s.mem.eraseFrom mark :=
  eraseFrom_storeLimbs_fresh s.mem out _ mark h

theorem multiply_shape (s : GlobalState) (out a b : Pointer) (id : BlockId) :
    ((multiply s out a b).mem[id]?).map MemoryBlock.length =
      (s.mem[id]?).map MemoryBlock.length := storeLimbs_allocationShape _ _ _ _

private theorem pack_four (a b c d : BitVec 64) :
    BitVec.packLanes #v[a,b,c,d] = d ++ c ++ b ++ a := by
  change (((0#0 ++ d) ++ c) ++ b) ++ a = d ++ c ++ b ++ a
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero]
  grind only

private theorem negative_splices (old : BitVec 320) (x : Words) :
    Memory.spliceBits (Memory.spliceBits old 0 (x 0)) 64
      (BitVec.packLanes #v[x 1,x 2,x 3,x 4]) = limbBytes x := by
  rw [pack_four]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getLsbD_spliceBits, limbBytes, BitVec.getLsbD_append]
  grind only

theorem negativeState_read320 (s : GlobalState) (p : Pointer) (x : Words)
    (h : SmallRange s.mem p 40) : (negativeState s p x).mem.readAt p 320 = limbBytes x := by
  have h0 := MemoryState.readAt_add_storeAt (p := p) (off := 0#64)
    (v := 320) h.fits (h.no_wrap (k := 0) (by decide)) (by decide) (x 0)
  have h8 := MemoryState.readAt_add_storeAt (p := p) (off := 8#64)
    (v := 320) (m := s.mem.storeAt p (x 0)) h.fits.storeAt
    (h.no_wrap (k := 8) (by decide)) (by decide) (BitVec.packLanes #v[x 1,x 2,x 3,x 4])
  simp only [Pointer.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.zero_mul, Nat.reduceMul] at h0 h8
  change ((s.mem.storeAt p (x 0)).storeAt (p.add 8#64)
    (BitVec.packLanes #v[x 1,x 2,x 3,x 4])).readAt p 320 = _
  rw [h8, h0]
  exact negative_splices _ x

theorem negativeState_readLimbs (s : GlobalState) (p : Pointer) (x : Words)
    (h : SmallRange s.mem p 40) : readLimbs (negativeState s p x) p = x :=
  readLimbs_of_limbBytes _ p x (negativeState_live h p x) (negativeState_read320 s p x h)

theorem negativeState_read_other (s : GlobalState) (p q : Pointer) (x : Words) (w : Nat)
    (h : p.id ≠ q.id) : (negativeState s p x).mem.readAt q w = s.mem.readAt q w := by
  have h0 : (Range.of p 64).Disjoint (Range.of q w) := Or.inl h
  have h8 : (Range.of (p.add 8) 256).Disjoint (Range.of q w) := Or.inl h
  simp only [negativeState, MemoryState.readAt_storeAt_disjoint h8,
    MemoryState.readAt_storeAt_disjoint h0]

theorem negativeState_allocation (s : GlobalState) (p q : Pointer) (x : Words)
    (h : q.id ≠ p.id) : (negativeState s p x).mem[q.id]? = s.mem[q.id]? := by
  simp only [negativeState]
  rw [MemoryState.getElem?_storeAt_ne (p := p.add 8) h,
    MemoryState.getElem?_storeAt_ne (p := p) h]

theorem negativeState_private (s : GlobalState) (p : Pointer) (x : Words) (mark : Nat)
    (h : mark ≤ p.id.id) :
    (negativeState s p x).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  simp only [negativeState, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (p := p.add 8) h,
    MemoryState.storeAt_eraseFrom_of_le (p := p) h]

theorem negativeState_shape (s : GlobalState) (p : Pointer) (x : Words) (id : BlockId) :
    ((negativeState s p x).mem[id]?).map MemoryBlock.length =
      (s.mem[id]?).map MemoryBlock.length := by
  simp only [negativeState, storeAt_allocationShape]

theorem comparison_canonical (s : GlobalState) (a b : Pointer) (x y : Words)
    (hx : s.mem.readAt a 256 = canonicalWord x) (hy : s.mem.readAt b 256 = canonicalWord y) :
    comparison s a b = if wordValue x = wordValue y then 1#8 else 0#8 := by
  simp only [comparison, hx, hy, canonicalWord_eq_iff]

theorem comparison_equalWords (s : GlobalState) (a b : Pointer) (x y : Pow22501.TightWords)
    (hx : s.mem.readAt a 256 = canonicalWord x.limbs)
    (hy : s.mem.readAt b 256 = canonicalWord y.limbs) :
    comparison s a b = if equalWords x y then 1#8 else 0#8 := by
  simp only [comparison, hx, hy, equalWords, decide_eq_true_eq]

theorem correction_byte (a b : Bool) :
    ((if a then 1#8 else 0#8) ||| (if b then 1#8 else 0#8)) =
      if a || b then 1#8 else 0#8 := by
  cases a <;> cases b <;> decide

theorem comparison_zero_or_one (s : GlobalState) (a b : Pointer) :
    comparison s a b = 0#8 ∨ comparison s a b = 1#8 := by
  unfold comparison
  split <;> simp

theorem correction_zero_or_one (s : GlobalState) (a b : Pointer) (previous : BitVec 8)
    (h : previous = 0#8 ∨ previous = 1#8) :
    comparison s a b ||| previous = 0#8 ∨ comparison s a b ||| previous = 1#8 := by
  rcases comparison_zero_or_one s a b with hc | hc <;>
    rcases h with h | h <;> rw [hc, h] <;> decide

theorem advance_ready (h : Ready dg g s) (n : Nat) : Ready dg g (advance s n) := ⟨h.curveD, h.sqrtM1⟩

theorem serialize_ready (h : Ready dg g s) (out input : Pointer)
    (hd : out.id ≠ dg.address0.id) (hi : out.id ≠ g.address0.id) :
    Ready dg g (serialize s out input) :=
  ⟨⟨serialize_live h.curveD.1 _ _, (serialize_read_other s out input dg.address0 320 hd).trans h.curveD.2⟩,
    ⟨serialize_live h.sqrtM1.1 _ _, (serialize_read_other s out input g.address0 320 hi).trans h.sqrtM1.2⟩⟩

theorem multiply_ready (h : Ready dg g s) (out a b : Pointer)
    (hd : out.id ≠ dg.address0.id) (hi : out.id ≠ g.address0.id) :
    Ready dg g (multiply s out a b) :=
  ⟨⟨multiply_live h.curveD.1 _ _ _, (multiply_read_other s out a b dg.address0 320 hd).trans h.curveD.2⟩,
    ⟨multiply_live h.sqrtM1.1 _ _ _, (multiply_read_other s out a b g.address0 320 hi).trans h.sqrtM1.2⟩⟩

theorem negativeState_ready (h : Ready dg g s) (p : Pointer) (x : Words)
    (hd : p.id ≠ dg.address0.id) (hi : p.id ≠ g.address0.id) :
    Ready dg g (negativeState s p x) :=
  ⟨⟨negativeState_live h.curveD.1 _ _, (negativeState_read_other s p dg.address0 x 320 hd).trans h.curveD.2⟩,
    ⟨negativeState_live h.sqrtM1.1 _ _, (negativeState_read_other s p g.address0 x 320 hi).trans h.sqrtM1.2⟩⟩

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers
