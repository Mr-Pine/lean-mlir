module

public import MLIR.Semantics.Effectful.Memory.Pointers
import Std.Data.ExtHashMap.Lemmas

/-! Copies (`storeCopy`: `memcpy`'s and `memmove`'s write, the live pointers carried) and the bits
a load reads as known (`knownAt`). -/

namespace MLIR

open Memory

@[expose] public section

/-- A window of `d` all clear: no set bit in it. -/
theorem _root_.BitVec.extractLsb'_eq_zero_iff {d : BitVec w} {k n : Nat} :
    d.extractLsb' k n = 0 ↔ ¬∃ i < w, d.getLsbD i ∧ k ≤ i ∧ i < k + n := by
  constructor
  · rintro h ⟨i, hi, hd, hk, hn⟩
    have := congrArg (·.getLsbD (i - k)) h
    simp only [BitVec.getLsbD_extractLsb', show i - k < n by omega, decide_true, Bool.true_and,
      show k + (i - k) = i by omega] at this
    simp [this] at hd
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    by_cases hkj : k + j < w
    · cases hd : d.getLsbD (k + j)
      · simp
      · exact absurd ⟨k + j, hkj, hd, by omega, by omega⟩ h
    · simp [BitVec.getLsbD_of_ge d (k + j) (by omega)]

/-- The pointer at bit `off + k` of a block after a copy's write wholly over its 64 bits: the one
recorded there, live while the written bits there are undefined and hold its address. -/
theorem MemoryBlock.ptrAt_copy {blk : MemoryBlock} {off k w : Nat} {x d : BitVec w}
    {P : Nat → Option Pointer} (hk : k + 64 ≤ w) (hsz : off + w ≤ 8 * blk.length) :
    ({ blk with
        bytes := spliceBits blk.bytes off x
        defined := spliceBits blk.defined off d
        ptrs := MemoryBlock.copyPtrs blk.ptrs off d P } : MemoryBlock).ptrAt addr (off + k) =
      match P k with
      | some r =>
        if (spliceBits blk.defined off d).extractLsb' (off + k) 64 = 0 ∧
            (spliceBits blk.bytes off x).extractLsb' (off + k) 64 = r.addrBits addr then
          .value r
        else .poison
      | none => .poison := by
  simp only [MemoryBlock.ptrAt, MemoryBlock.copyPtrs, Nat.add_sub_cancel_left,
    show off ≤ off + k by omega, show off + k + 64 ≤ off + w by omega, true_and]
  cases hP : P k with
  | some r => simp
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false, MemoryBlock.clearPtrs]
    by_cases hd : d = BitVec.allOnes w
    · -- every bit defined: whatever entry stays, it loads as poison
      subst hd
      have hne :
          (spliceBits blk.defined off (BitVec.allOnes w)).extractLsb' (off + k) 64 ≠ 0#64 := by
        intro h0
        have := congrArg (·.getLsbD 0) h0
        simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero, Nat.add_zero,
          getLsbD_spliceBits, BitVec.getLsbD_allOnes] at this
        rw [ite_eq_left (by omega)] at this
        simp at this
        omega
      simp only [ite_true]
      cases blk.ptrs (off + k) with
      | none => rfl
      | some r => simp [hne]
    · simp only [hd, ite_false]
      rw [ite_eq_right (by omega)]

/-! ### `storeCopy` -/

section StoreCopy

variable {m : MemoryState} {p q : Pointer} {P : Nat → Option Pointer}

@[simp, mlir_mem, mlir_state]
theorem MemoryState.unspec_storeCopy {x d : BitVec w} : (m.storeCopy p x d P).unspec = m.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.addr_storeCopy {x d : BitVec w} : (m.storeCopy p x d P).addr = m.addr :=
  rfl

/-- `storeCopy` holds `storeDef`'s bits. -/
theorem MemoryState.sameBits_storeCopy {x d : BitVec w} :
    (m.storeCopy p x d P).SameBits (m.storeDef p x d) :=
  sameBits_modifyBlock_modifyBlock fun _ => rfl

theorem MemoryState.sameShape_storeCopy {x d : BitVec w} : (m.storeCopy p x d P).SameShape m :=
  sameShape_modifyBlock fun _ => rfl

theorem MemoryState.getElem?_storeCopy_ne {x d : BitVec w} (h : q.id ≠ p.id) :
    (m.storeCopy p x d P)[q.id]? = m[q.id]? :=
  getElem?_modifyBlock_ne h

/-- A copy of no pointers: `storeDef`. -/
theorem MemoryState.storeCopy_none {x d : BitVec w} :
    m.storeCopy p x d (fun _ => none) = m.storeDef p x d := by
  have hp (blk : MemoryBlock) :
      MemoryBlock.copyPtrs blk.ptrs p.offsetInBits d (fun _ => none) =
        MemoryBlock.clearPtrs blk.ptrs p.offsetInBits d := by
    funext o
    simp [MemoryBlock.copyPtrs]
  simp only [storeCopy, storeDef, hp]

/-- A copy of no pointers, every bit defined: a store. -/
theorem MemoryState.storeCopy_allOnes {x : BitVec w} :
    m.storeCopy p x (BitVec.allOnes w) (fun _ => none) = m.storeAt p x := by
  rw [storeCopy_none, storeAt_eq_storeDef]

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_storeCopy_self (hfits : Room m p w) (x d : BitVec w) :
    (m.storeCopy p x d P).readAt p w = x :=
  sameBits_storeCopy.readAt.trans (readAt_storeDef_self hfits x d)

theorem MemoryState.definedAt_storeCopy_self (hfits : Room m p w) (x d : BitVec w) :
    (m.storeCopy p x d P).definedAt p w = d :=
  sameBits_storeCopy.definedAt.trans (definedAt_storeDef_self hfits x d)

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_storeCopy_disjoint {v w : Nat}
    (h : (Range.of p v).Disjoint (Range.of q w)) (x d : BitVec v) :
    (m.storeCopy p x d P).readAt q w = m.readAt q w :=
  sameBits_storeCopy.readAt.trans (readAt_storeDef_disjoint h x d)

theorem MemoryState.definedAt_storeCopy_disjoint {v w : Nat}
    (h : (Range.of p v).Disjoint (Range.of q w)) (x d : BitVec v) :
    (m.storeCopy p x d P).definedAt q w = m.definedAt q w :=
  sameBits_storeCopy.definedAt.trans (definedAt_storeDef_disjoint h x d)

/-- A read inside a copy's write: the written bits. -/
theorem MemoryState.readAt_storeCopy_add {off : BitVec 64} (hfits : Room m p v)
    (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v) (x d : BitVec v) :
    (m.storeCopy p x d P).readAt (p.add off) w = x.extractLsb' (off.toNat * 8) w :=
  sameBits_storeCopy.readAt.trans (readAt_storeDef_add hfits hov hw x d)

/-- A read at a copy's start: the written bits' low ones. -/
theorem MemoryState.readAt_storeCopy_le (hfits : Room m p v) (hw : w ≤ v) (x d : BitVec v) :
    (m.storeCopy p x d P).readAt p w = x.extractLsb' 0 w :=
  sameBits_storeCopy.readAt.trans (readAt_storeDef_le hfits hw x d)

/-- A read inside a copy: the source's bits. -/
@[mlir_read]
theorem MemoryState.readAt_storeCopy_readAt_add {off : BitVec 64} (hp : Room m p v)
    (hq : InBounds m q v) (hov : ¬p.offset.uaddOverflow off) (hovq : ¬q.offset.uaddOverflow off)
    (hw : off.toNat * 8 + w ≤ v) (d : BitVec v) :
    (m.storeCopy p (m.readAt q v) d P).readAt (p.add off) w = m.readAt (q.add off) w :=
  sameBits_storeCopy.readAt.trans (readAt_storeDef_readAt_add hp hq hov hovq hw d)

/-- A read at a copy's start: the source's bits. -/
@[mlir_read]
theorem MemoryState.readAt_storeCopy_readAt_le (hp : Room m p v) (hw : w ≤ v) (d : BitVec v) :
    (m.storeCopy p (m.readAt q v) d P).readAt p w = m.readAt q w :=
  sameBits_storeCopy.readAt.trans (readAt_storeDef_readAt_le hp hw d)

-- after the source's: a copy's read inside it resolves to the written bits
attribute [mlir_read] MemoryState.readAt_storeCopy_add MemoryState.readAt_storeCopy_le

theorem InBounds.storeCopy_iff {x d : BitVec v} :
    InBounds (m.storeCopy q x d P) p w ↔ InBounds m p w :=
  ⟨.of_sameShape MemoryState.sameShape_storeCopy,
    .of_sameShape MemoryState.sameShape_storeCopy.symm⟩

theorem Room.storeCopy_iff {x d : BitVec v} : Room (m.storeCopy q x d P) p w ↔ Room m p w :=
  ⟨.of_sameShape MemoryState.sameShape_storeCopy,
    .of_sameShape MemoryState.sameShape_storeCopy.symm⟩

@[mlir_mem, mlir_transport]
theorem InBounds.storeCopy {x d : BitVec v} (h : InBounds m p w) :
    InBounds (m.storeCopy q x d P) p w :=
  InBounds.storeCopy_iff.2 h

@[mlir_mem, mlir_transport]
theorem Room.storeCopy {x d : BitVec v} (h : Room m p w) : Room (m.storeCopy q x d P) p w :=
  Room.storeCopy_iff.2 h

@[mlir_mem, mlir_transport]
theorem Live.storeCopy {x d : BitVec v} (h : Live m p w) : Live (m.storeCopy q x d P) p w :=
  h.of_sameShape MemoryState.sameShape_storeCopy.symm

@[mlir_mem, mlir_transport]
theorem Writable.storeCopy {x d : BitVec v} (h : Writable m p) : Writable (m.storeCopy q x d P) p :=
  h.of_sameShape MemoryState.sameShape_storeCopy.symm

/-- A copy elsewhere keeps known bits known. -/
@[mlir_transport]
theorem Fits.storeCopy_of_disjoint (hq : Fits m p w) (hd : (Range.of q v).Disjoint (Range.of p w))
    {x d : BitVec v} : Fits (m.storeCopy q x d P) p w :=
  MemoryState.sameBits_storeCopy.symm.fits (hq.storeDef_of_disjoint hd)

/-- A copy into a live block's room: a range inside it its mask defines is known. -/
theorem Fits.storeCopy_of_mask {x d : BitVec v} {off : BitVec 64} (h : Room m p v)
    (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v)
    (hd : d.extractLsb' (off.toNat * 8) w = BitVec.allOnes w) :
    Fits (m.storeCopy p x d P) (p.add off) w :=
  MemoryState.sameBits_storeCopy.symm.fits (Fits.storeDef_of_mask h hov hw hd)

/-- `storeCopy_of_mask` from the copy's start. -/
theorem Fits.storeCopy_of_mask_self {x d : BitVec v} (h : Room m p v) (hw : w ≤ v)
    (hd : d.extractLsb' 0 w = BitVec.allOnes w) : Fits (m.storeCopy p x d P) p w :=
  MemoryState.sameBits_storeCopy.symm.fits (Fits.storeDef_of_mask_self h hw hd)

/-- A copy's range known where its source's is. -/
theorem Fits.storeCopy_definedAt {x : BitVec v} {off : BitVec 64} (h : Room m p v)
    (hs : Fits m (q.add off) w) (hov : ¬p.offset.uaddOverflow off)
    (hovq : ¬q.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v) :
    Fits (m.storeCopy p x (m.definedAt q v) P) (p.add off) w :=
  MemoryState.sameBits_storeCopy.symm.fits (Fits.storeDef_definedAt h hs hov hovq hw)

/-- `storeCopy_definedAt` from the copy's start. -/
theorem Fits.storeCopy_definedAt_self {x : BitVec v} (h : Room m p v) (hs : Fits m q w)
    (hw : w ≤ v) : Fits (m.storeCopy p x (m.definedAt q v) P) p w :=
  MemoryState.sameBits_storeCopy.symm.fits (Fits.storeDef_definedAt_self h hs hw)

@[simp, mlir_mem]
theorem GlobalState.WF_storeCopy {s : GlobalState} {x d : BitVec v} :
    ({ s with mem := m.storeCopy p x d P } : GlobalState).WF ↔
      ({ s with mem := m } : GlobalState).WF :=
  WF_modifyBlock fun _ => ⟨rfl, rfl⟩

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.storeCopy {s : GlobalState} {x d : BitVec v} (h : s.WF) :
    { s with mem := s.mem.storeCopy p x d P }.WF :=
  GlobalState.WF_storeCopy.2 h

/-- `WF.storeCopy` for a state written as a constructor, which unifies first-order. -/
@[mlir_transport]
theorem GlobalState.WF.storeCopy_mk {a : AllocState} {x d : BitVec v}
    (h : (⟨a, m⟩ : GlobalState).WF) : (⟨a, m.storeCopy p x d P⟩ : GlobalState).WF :=
  GlobalState.WF.storeCopy (s := ⟨a, m⟩) h

/-- Erasing a frame commutes with a copy. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.eraseFrom_storeCopy {x d : BitVec w} :
    (m.storeCopy p x d P).eraseFrom n = (m.eraseFrom n).storeCopy p x d P :=
  eraseFrom_modifyBlock

/-- A copy into an erased block does nothing. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.storeCopy_eraseFrom_of_le {x d : BitVec w} (h : n ≤ p.id.id) :
    (m.eraseFrom n).storeCopy p x d P = m.eraseFrom n :=
  modifyBlock_eraseFrom_of_le h

/-- A copy in the frame, dropped before the erase moves past it. -/
@[mlir_erase high]
theorem MemoryState.eraseFrom_storeCopy_of_le {x d : BitVec w} (h : n ≤ p.id.id) :
    (m.storeCopy p x d P).eraseFrom n = m.eraseFrom n := by
  rw [eraseFrom_storeCopy, storeCopy_eraseFrom_of_le h]

/-- Known bits carry no live pointer. -/
theorem MemoryState.ptrsIn_of_fits (h : Fits m p w) : m.ptrsIn p w = fun _ => none := by
  obtain ⟨blk, hblk, -, -, hd⟩ := h
  funext o
  simp only [ptrsIn]
  split
  · rename_i ho
    simp only [ptrAt, hblk, MemoryBlock.ptrAt]
    split
    · have : blk.defined.extractLsb' (p.offsetInBits + o) 64 = BitVec.allOnes 64 := by
        have := congrArg (·.extractLsb' o 64) hd
        simpa only [BitVec.extractLsb'_extractLsb'_add ho, BitVec.extractLsb'_allOnes ho] using this
      simp [this]
      rfl
    · rfl
  · rfl

/-- Bits with no 64-bit window undefined carry no live pointer. -/
theorem MemoryState.ptrsIn_eq_none
    (h : ∀ o, o + 64 ≤ w → (m.definedAt q w).extractLsb' o 64 ≠ 0#64) :
    m.ptrsIn q w = fun _ => none := by
  funext o
  simp only [ptrsIn]
  split
  · rename_i ho
    simp only [ptrAt]
    split
    · rename_i b hb
      have hw := h o ho
      simp only [definedAt, hb, BitVec.extractLsb'_extractLsb'_add ho] at hw
      simp only [MemoryBlock.ptrAt]
      split
      · simp [hw]
        rfl
      · rfl
    · rfl
  · rfl

/-- A bit inside known bits at `q.add off`: defined, as `q`'s range reads it. -/
theorem MemoryState.getLsbD_definedAt_of_fits {off : BitVec 64} (hf : Fits m (q.add off) n)
    (hov : ¬q.offset.uaddOverflow off) (hj : off.toNat * 8 ≤ j) (hjn : j < off.toNat * 8 + n)
    (hjw : j < w) : (m.definedAt q w).getLsbD j = true := by
  obtain ⟨b, hb, -, -, hd⟩ := hf
  have hb' : m[q.id]? = some b := hb
  have := congrArg (·.getLsbD (j - off.toNat * 8)) hd
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_allOnes,
    show j - off.toNat * 8 < n by omega, decide_true, Bool.true_and,
    Pointer.offsetInBits_add hov] at this
  simp only [definedAt, hb', BitVec.getLsbD_extractLsb', hjw, decide_true, Bool.true_and]
  rw [← this]
  congr 1
  omega

/-- `getLsbD_definedAt_of_fits` from `q` itself. -/
theorem MemoryState.getLsbD_definedAt_of_fits_self (hf : Fits m q n) (hjn : j < n) (hjw : j < w) :
    (m.definedAt q w).getLsbD j = true :=
  getLsbD_definedAt_of_fits (off := 0#64) (by simpa using hf)
    (by simp [BitVec.uaddOverflow, q.offset.isLt]) (by simp) (by simpa using hjn) hjw

/-- No 64-bit window of `q`'s `w` bits without a defined bit: no live pointer among them. -/
theorem MemoryState.ptrsIn_eq_none_of_bits
    (h : ∀ o, o + 64 ≤ w → ∃ j, o ≤ j ∧ j < o + 64 ∧ (m.definedAt q w).getLsbD j = true) :
    m.ptrsIn q w = fun _ => none := by
  refine ptrsIn_eq_none fun o ho h0 => ?_
  obtain ⟨j, hj, hjo, hd⟩ := h o ho
  have := congrArg (·.getLsbD (j - o)) h0
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero, show j - o < 64 by omega,
    decide_true, Bool.true_and, show o + (j - o) = j by omega] at this
  simp [this] at hd

/-- `ptrsIn_eq_none` for a known mask `D`, its windows checked by `decide`. -/
theorem MemoryState.ptrsIn_eq_none_of_definedAt {D : BitVec w} (hd : m.definedAt q w = D)
    (hD : ∀ o < w + 1 - 64, D.extractLsb' o 64 ≠ 0#64) : m.ptrsIn q w = fun _ => none :=
  ptrsIn_eq_none fun o ho => hd ▸ hD o (by omega)

/-- A copy of the bits known at `q`: a store of them. -/
theorem MemoryState.storeCopy_of_fits (h : Fits m q w) :
    m.storeCopy p (m.readAt q w) (m.definedAt q w) (m.ptrsIn q w) = m.storeAt p (m.readAt q w) := by
  rw [ptrsIn_of_fits h, definedAt_of_fits h, storeCopy_allOnes]

/-- A copy of bits carrying no live pointer: `storeDef`. -/
theorem MemoryState.storeCopy_of_ptrsIn {x d : BitVec w} (h : m.ptrsIn q w = fun _ => none) :
    m.storeCopy p x d (m.ptrsIn q w) = m.storeDef p x d := by
  rw [h, storeCopy_none]

/-- A block's entry, definedness and bits at `o` past a copy's write disjoint from it. -/
theorem MemoryBlock.ptrAt_storeCopy {blk : MemoryBlock} {off o v : Nat} {y d : BitVec v}
    (h : o + 64 ≤ off ∨ off + v ≤ o) :
    ({ blk with
        bytes := spliceBits blk.bytes off y
        defined := spliceBits blk.defined off d
        ptrs := MemoryBlock.copyPtrs blk.ptrs off d P } : MemoryBlock).ptrAt addr o =
      blk.ptrAt addr o := by
  apply MemoryBlock.ptrAt_congr
  · simp only [MemoryBlock.copyPtrs, MemoryBlock.clearPtrs]
    rw [ite_eq_right (by omega)]
    split <;> simp [h]
  · exact extractLsb'_spliceBits_of_disjoint _ _ _ _ (by omega)
  · exact extractLsb'_spliceBits_of_disjoint _ _ _ _ (by omega)

@[mlir_mem, mlir_read]
theorem MemoryState.loadPtr_storeCopy_disjoint {v : Nat}
    (h : (Range.of p v).Disjoint (Range.of q 64)) (y d : BitVec v) :
    (m.storeCopy p y d P).loadPtr q = m.loadPtr q := by
  by_cases hid : q.id = p.id
  · simp only [Range.Disjoint, Range.of, hid, ne_eq, not_true_eq_false, false_or] at h
    exact loadPtr_modifyBlock fun _ => MemoryBlock.ptrAt_storeCopy (by omega)
  · simp only [loadPtr, ptrAt, storeCopy, getElem?_modifyBlock_ne hid]
    rfl

/-- A pointer copied, wholly inside the copy, loads back as at the source. -/
@[mlir_read]
theorem MemoryState.loadPtr_storeCopy_add {off : BitVec 64} (hp : Room m p v) (hr : InBounds m q v)
    (hov : ¬p.offset.uaddOverflow off) (hovq : ¬q.offset.uaddOverflow off)
    (hw : off.toNat * 8 + 64 ≤ v) :
    (m.storeCopy p (m.readAt q v) (m.definedAt q v) (m.ptrsIn q v)).loadPtr (p.add off) =
      m.loadPtr (q.add off) := by
  obtain ⟨blk, hblk, -, hsz, hwr⟩ := hp.block
  obtain ⟨b, hb, hbsz⟩ := hr
  unfold MemoryBlock.lengthInBits at hsz hbsz
  have hpo := Pointer.offsetInBits_add hov
  have hqo := Pointer.offsetInBits_add hovq
  have hnew : (m.storeCopy p (m.readAt q v) (m.definedAt q v) (m.ptrsIn q v))[(p.add off).id]? =
      some _ := getElem?_modifyBlock_of_writable hblk hwr
  rw [loadPtr_eq_of_block hnew, loadPtr_eq_of_block (p := q.add off) hb, addr_storeCopy, hpo,
    MemoryBlock.ptrAt_copy hw (by omega)]
  -- the written windows: the source's
  have hwin (z : BitVec (8 * blk.length)) (y : BitVec (8 * b.length)) :
      (spliceBits z p.offsetInBits (y.extractLsb' q.offsetInBits v)).extractLsb'
          (p.offsetInBits + off.toNat * 8) 64 = y.extractLsb' (q.add off).offsetInBits 64 := by
    rw [extractLsb'_spliceBits_of_subrange _ _ _ _ (by omega) (by omega) (by omega),
      BitVec.extractLsb'_extractLsb'_add (by omega), hqo]
    congr 1
    omega
  simp only [readAt, definedAt, hb, hwin, ptrsIn, hw, ite_true, ptrAt, ← hqo]
  simp only [MemoryBlock.ptrAt]
  cases b.ptrs (q.add off).offsetInBits with
  | none => rfl
  | some r =>
    by_cases hc :
        b.defined.extractLsb' (q.add off).offsetInBits 64 = 0#64 ∧
          b.bytes.extractLsb' (q.add off).offsetInBits 64 = r.addrBits m.addr
    · simp [hc]
    · simp [hc]

/-- A pointer copied from the copy's start loads back as at the source's. -/
@[mlir_read]
theorem MemoryState.loadPtr_storeCopy_self (hp : Room m p v) (hr : InBounds m q v) (hw : 64 ≤ v) :
    (m.storeCopy p (m.readAt q v) (m.definedAt q v) (m.ptrsIn q v)).loadPtr p = m.loadPtr q := by
  have h := loadPtr_storeCopy_add (off := 0#64) hp hr (by simp [BitVec.uaddOverflow, p.offset.isLt])
    (by simp [BitVec.uaddOverflow, q.offset.isLt]) (by simpa)
  simpa using h

end StoreCopy

/-- Integer bits stored over a pointer's start: it loads as poison, its bits defined. -/
theorem MemoryState.loadPtr_storeAt_self {m : MemoryState} {p : Pointer} {x : BitVec w}
    (h : Room m p w) (hw : 0 < w) : (m.storeAt p x).loadPtr p = .poison := by
  obtain ⟨blk, hblk, -, hsz, hwr⟩ := h.block
  unfold MemoryBlock.lengthInBits at hsz
  have hb : (m.storeAt p x)[p.id]? = _ := getElem?_storeAt_self hblk hwr
  rw [loadPtr_eq_of_block hb]
  simp only [MemoryBlock.ptrAt]
  split
  · rename_i q _
    have hne : (spliceBits blk.defined p.offsetInBits (BitVec.allOnes w)).extractLsb'
        p.offsetInBits 64 ≠ 0#64 := by
      intro h0
      have := congrArg (·.getLsbD 0) h0
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero, Nat.add_zero,
        getLsbD_spliceBits, BitVec.getLsbD_allOnes] at this
      rw [ite_eq_left (by omega)] at this
      simp [hw] at this
    simp [hne]
  · rfl

/-! ### `ptrsIn` through writes: what a copy carries, read like bits -/

section PtrsIn

variable {m : MemoryState} {p q : Pointer}

/-- The same block at `q`, the same addresses: the same pointers to copy. -/
theorem MemoryState.ptrsIn_congr {m' : MemoryState} (h : m'[q.id]? = m[q.id]?)
    (ha : m'.addr = m.addr) : m'.ptrsIn q w = m.ptrsIn q w := by
  funext o
  simp only [ptrsIn, ptrAt, h, ha]

/-- `ptrsIn` past a change of another block. -/
theorem MemoryState.ptrsIn_modifyBlock_ne {i : BlockId} {f : MemoryBlock → MemoryBlock}
    (h : q.id ≠ i) : (m.modifyBlock i f).ptrsIn q w = m.ptrsIn q w := by
  funext o
  simp only [ptrsIn, ptrAt, getElem?_modifyBlock_ne h, addr_modifyBlock]

/-- `ptrsIn` past a change of a block by `f` keeping the pointers at each offset of the range. -/
theorem MemoryState.ptrsIn_modifyBlock {i : BlockId} {f : MemoryBlock → MemoryBlock}
    (hf : ∀ (b : MemoryBlock) (o : Nat), o + 64 ≤ w →
      (f b).ptrAt m.addr (q.offsetInBits + o) = b.ptrAt m.addr (q.offsetInBits + o)) :
    (m.modifyBlock i f).ptrsIn q w = m.ptrsIn q w := by
  by_cases h : q.id = i
  · subst h
    funext o
    simp only [ptrsIn]
    split
    · rename_i ho
      simp only [ptrAt, getElem?_modifyBlock_self, addr_modifyBlock]
      cases m[q.id]? with
      | none => rfl
      | some b => by_cases hw : b.writable <;> simp [MemoryBlock.update, hw, hf b o ho]
    · rfl
  · exact ptrsIn_modifyBlock_ne h

/-- The offsets of a range disjoint from another in its block. -/
theorem Range.disjoint_offsets {v w o : Nat} (h : (Range.of p v).Disjoint (Range.of q w))
    (hid : q.id = p.id) (ho : o + 64 ≤ w) :
    q.offsetInBits + o + 64 ≤ p.offsetInBits ∨ p.offsetInBits + v ≤ q.offsetInBits + o := by
  simp only [Range.Disjoint, Range.of, hid, ne_eq, not_true_eq_false, false_or] at h
  omega

@[mlir_read]
theorem MemoryState.ptrsIn_storeDef_disjoint {v : Nat} (h : (Range.of p v).Disjoint (Range.of q w))
    (y d : BitVec v) : (m.storeDef p y d).ptrsIn q w = m.ptrsIn q w := by
  by_cases hid : q.id = p.id
  · exact ptrsIn_modifyBlock fun _ o ho =>
      MemoryBlock.ptrAt_storeDef (Range.disjoint_offsets h hid ho)
  · exact ptrsIn_modifyBlock_ne hid

@[mlir_read]
theorem MemoryState.ptrsIn_storeAt_disjoint {v : Nat} (h : (Range.of p v).Disjoint (Range.of q w))
    (y : BitVec v) : (m.storeAt p y).ptrsIn q w = m.ptrsIn q w := by
  rw [storeAt_eq_storeDef]; exact ptrsIn_storeDef_disjoint h y _

@[mlir_read]
theorem MemoryState.ptrsIn_overlay_disjoint {v : Nat} (h : (Range.of p v).Disjoint (Range.of q w))
    (y d : BitVec v) : (m.overlay p y d).ptrsIn q w = m.ptrsIn q w := by
  by_cases hid : q.id = p.id
  · refine ptrsIn_modifyBlock fun _ o ho => MemoryBlock.ptrAt_congr rfl ?_ ?_ <;>
      exact extractLsb'_spliceBits_of_disjoint _ _ _ _
        (by have := Range.disjoint_offsets h hid ho; omega)
  · exact ptrsIn_modifyBlock_ne hid

@[mlir_read]
theorem MemoryState.ptrsIn_storeCopy_disjoint {v : Nat} {P : Nat → Option Pointer}
    (h : (Range.of p v).Disjoint (Range.of q w)) (y d : BitVec v) :
    (m.storeCopy p y d P).ptrsIn q w = m.ptrsIn q w := by
  by_cases hid : q.id = p.id
  · exact ptrsIn_modifyBlock fun _ o ho =>
      MemoryBlock.ptrAt_storeCopy (Range.disjoint_offsets h hid ho)
  · exact ptrsIn_modifyBlock_ne hid

@[mlir_read]
theorem MemoryState.ptrsIn_storePtr_disjoint {x : Pointer}
    (h : (Range.of p 64).Disjoint (Range.of q w)) : (m.storePtr p x).ptrsIn q w = m.ptrsIn q w := by
  by_cases hid : q.id = p.id
  · refine ptrsIn_modifyBlock fun b o ho => ?_
    have hd := Range.disjoint_offsets h hid ho
    rw [← MemoryBlock.ptrAt_storeDef (blk := b) (y := x.addrBits m.addr) (d := 0#64)
      (off := p.offsetInBits) (o := q.offsetInBits + o) hd]
    refine MemoryBlock.ptrAt_congr ?_ rfl rfl
    simp only [show q.offsetInBits + o ≠ p.offsetInBits by omega, ite_false]
  · exact ptrsIn_modifyBlock_ne hid

@[mlir_read]
theorem MemoryState.ptrsIn_lifetimeStart (h : q.id ≠ p.id) :
    (m.lifetimeStart p).ptrsIn q w = m.ptrsIn q w :=
  ptrsIn_modifyBlock_ne h

@[mlir_read]
theorem MemoryState.ptrsIn_lifetimeEnd (h : q.id ≠ p.id) :
    (m.lifetimeEnd p).ptrsIn q w = m.ptrsIn q w :=
  ptrsIn_modifyBlock_ne h

@[mlir_read]
theorem MemoryState.ptrsIn_alloca {s : GlobalState} (hwf : s.WF) (h : InBounds s.mem q w') :
    (s.alloca n d).mem.ptrsIn q w = s.mem.ptrsIn q w := by
  funext o
  simp only [ptrsIn, ptrAt,
    GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_inBounds hwf h)]
  rfl

/-- `ptrsIn_alloca` with the copy's own width, which `ptrsIn_alloca`'s open width never matches. -/
@[mlir_read]
theorem MemoryState.ptrsIn_alloca_of_fits {s : GlobalState} (hwf : s.WF) (h : InBounds s.mem q w) :
    (s.alloca n d).mem.ptrsIn q w = s.mem.ptrsIn q w :=
  ptrsIn_alloca hwf h

/-- Bits stored carry no pointer. -/
@[mlir_read]
theorem MemoryState.ptrsIn_storeAt_self {x : BitVec w} (h : Room m p w) :
    (m.storeAt p x).ptrsIn p w = fun _ => none :=
  ptrsIn_of_fits (Fits.storeAt_self h)

/-- Bits stored carry no pointer, a range inside them none either. -/
@[mlir_read]
theorem MemoryState.ptrsIn_storeAt_add {x : BitVec v} {off : BitVec 64} (h : Room m p v)
    (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v) :
    (m.storeAt p x).ptrsIn (p.add off) w = fun _ => none :=
  ptrsIn_of_fits (Fits.storeAt_add_self h hov hw)

-- a copy of no pointers is a masked store
attribute [mlir_state] MemoryState.storeCopy_none

end PtrsIn

/-! ### `PtrFree`: no live pointer over a range, which a copy of it then carries none of -/

/-- No live pointer stored over any of the `w` bits at `q`. Integer writes keep it (none revives a
pointer), and a copy of the bits carries no pointer (`ptrsIn_of_ptrFree`). -/
structure PtrFree (m : MemoryState) (q : Pointer) (w : Nat) : Prop where
  poison : ∀ o, o < q.offsetInBits + w → q.offsetInBits < o + 64 → m.ptrAt q.id o = .poison

section PtrFree

variable {m : MemoryState} {p q : Pointer}

/-- Bits with no live pointer over them carry none. -/
@[mlir_no_ptrs]
theorem MemoryState.ptrsIn_of_ptrFree (h : PtrFree m q w) : m.ptrsIn q w = fun _ => none := by
  funext o
  simp only [ptrsIn]
  split
  · rw [h.poison _ (by omega) (by omega)]; rfl
  · rfl

/-- A block's pointer at `o` after a masked store over part of its 64 bits: poison. -/
theorem MemoryBlock.ptrAt_storeDef_overlap {blk : MemoryBlock} {off o v : Nat} {y d : BitVec v}
    (hsz : off + v ≤ 8 * blk.length) (hv : 0 < v) (h : ¬(o + 64 ≤ off ∨ off + v ≤ o)) :
    ({ blk with
        bytes := spliceBits blk.bytes off y
        defined := spliceBits blk.defined off d
        ptrs := MemoryBlock.clearPtrs blk.ptrs off d } : MemoryBlock).ptrAt addr o = .poison := by
  simp only [MemoryBlock.ptrAt, MemoryBlock.clearPtrs]
  by_cases hd : d = BitVec.allOnes v
  · subst hd
    simp only [ite_true]
    -- a bit of the window the store defines
    have hne : (spliceBits blk.defined off (BitVec.allOnes v)).extractLsb' o 64 ≠ 0#64 := by
      intro h0
      have := congrArg (·.getLsbD (max o off - o)) h0
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero, show max o off - o < 64 by omega,
        decide_true, Bool.true_and, getLsbD_spliceBits, BitVec.getLsbD_allOnes] at this
      rw [ite_eq_left (by omega)] at this
      simp at this
      omega
    cases blk.ptrs o with
    | none => rfl
    | some r => simp [hne]
  · simp only [hd, ite_false]
    rw [ite_eq_right (by omega)]

/-- `PtrFree` past a change of a block by `f` that keeps, or kills, each pointer over the range. -/
theorem PtrFree.modifyBlock {i : BlockId} {f : MemoryBlock → MemoryBlock} (h : PtrFree m q w)
    (hf : ∀ b : MemoryBlock, m[i]? = some b → i = q.id → ∀ o, o < q.offsetInBits + w →
      q.offsetInBits < o + 64 →
        (f b).ptrAt m.addr o = b.ptrAt m.addr o ∨ (f b).ptrAt m.addr o = .poison) :
    PtrFree (m.modifyBlock i f) q w := by
  refine ⟨fun o ho ho' => ?_⟩
  have h0 := h.poison o ho ho'
  by_cases hid : q.id = i
  · subst hid
    simp only [MemoryState.ptrAt, MemoryState.getElem?_modifyBlock_self,
      MemoryState.addr_modifyBlock] at h0 ⊢
    cases hb : m[q.id]? with
    | none => rfl
    | some b =>
      rw [hb] at h0
      by_cases hw : b.writable
      · simp only [Option.map_some, MemoryBlock.update, hw, ite_true]
        rcases hf b hb rfl o ho ho' with e | e <;> rw [e]
        exact h0
      · simpa [MemoryBlock.update, hw] using h0
  · simpa only [MemoryState.ptrAt, MemoryState.getElem?_modifyBlock_ne hid,
      MemoryState.addr_modifyBlock] using h0

/-- A block's pointer at `o` past a masked store of no bits: unchanged. -/
theorem MemoryBlock.ptrAt_storeDef_zero {blk : MemoryBlock} {off o : Nat} {y d : BitVec 0} :
    ({ blk with
        bytes := spliceBits blk.bytes off y
        defined := spliceBits blk.defined off d
        ptrs := MemoryBlock.clearPtrs blk.ptrs off d } : MemoryBlock).ptrAt addr o =
      blk.ptrAt addr o := by
  have hs (z : BitVec (8 * blk.length)) (x : BitVec 0) : spliceBits z off x = z := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_spliceBits, ite_eq_right (by omega)]
  refine MemoryBlock.ptrAt_congr ?_ (by simp only [hs]) (by simp only [hs])
  simp [MemoryBlock.clearPtrs, show d = BitVec.allOnes 0 from BitVec.eq_of_getLsbD_eq (by simp)]

/-- A masked store keeps `PtrFree`: it kills each pointer it meets. -/
@[mlir_transport]
theorem PtrFree.storeDef {v : Nat} {y d : BitVec v} (h : PtrFree m q w) (hb : InBounds m p v) :
    PtrFree (m.storeDef p y d) q w := by
  refine h.modifyBlock fun b hb' _ o _ _ => ?_
  obtain ⟨b', hb'', hsz⟩ := hb
  rw [hb''] at hb'
  cases hb'
  unfold MemoryBlock.lengthInBits at hsz
  by_cases hv : v = 0
  · subst hv; exact .inl MemoryBlock.ptrAt_storeDef_zero
  by_cases ho : o + 64 ≤ p.offsetInBits ∨ p.offsetInBits + v ≤ o
  · exact .inl (MemoryBlock.ptrAt_storeDef ho)
  · exact .inr (MemoryBlock.ptrAt_storeDef_overlap hsz (by omega) ho)

@[mlir_transport]
theorem PtrFree.storeAt {v : Nat} {y : BitVec v} (h : PtrFree m q w) (hb : InBounds m p v) :
    PtrFree (m.storeAt p y) q w := by
  rw [MemoryState.storeAt_eq_storeDef]; exact h.storeDef hb

/-- A masked store leaves no live pointer over a range inside it. -/
theorem PtrFree.storeDef_add_self {v : Nat} {y d : BitVec v} {off : BitVec 64}
    (hr : Room m p v) (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v)
    (hw0 : 0 < w) : PtrFree (m.storeDef p y d) (p.add off) w := by
  obtain ⟨b, hb', -, hsz, hwr⟩ := hr.block
  unfold MemoryBlock.lengthInBits at hsz
  refine ⟨fun o ho ho' => ?_⟩
  rw [Pointer.offsetInBits_add hov] at ho ho'
  have hn : (m.storeDef p y d)[(p.add off).id]? = _ :=
    MemoryState.getElem?_modifyBlock_of_writable hb' hwr
  simp only [MemoryState.ptrAt, hn, MemoryState.addr_storeDef]
  exact MemoryBlock.ptrAt_storeDef_overlap hsz (by omega) (by omega)

/-- `storeDef_add_self` from the store's start. -/
theorem PtrFree.storeDef_self {v : Nat} {y d : BitVec v} (hr : Room m p v) (hw : w ≤ v)
    (hw0 : 0 < w) : PtrFree (m.storeDef p y d) p w := by
  simpa using PtrFree.storeDef_add_self (off := 0#64) hr
    (by simp [BitVec.uaddOverflow, p.offset.isLt]) (by simpa) hw0

theorem PtrFree.storeAt_add_self {v : Nat} {y : BitVec v} {off : BitVec 64}
    (hr : Room m p v) (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v)
    (hw0 : 0 < w) : PtrFree (m.storeAt p y) (p.add off) w := by
  rw [MemoryState.storeAt_eq_storeDef]; exact PtrFree.storeDef_add_self hr hov hw hw0

theorem PtrFree.storeAt_self {v : Nat} {y : BitVec v} (hr : Room m p v) (hw : w ≤ v)
    (hw0 : 0 < w) : PtrFree (m.storeAt p y) p w := by
  rw [MemoryState.storeAt_eq_storeDef]; exact PtrFree.storeDef_self hr hw hw0



/-- A pointer stored outside the range keeps `PtrFree`. -/
@[mlir_transport]
theorem PtrFree.storePtr_of_disjoint {x : Pointer} (h : PtrFree m q w)
    (hd : (Range.of p 64).Disjoint (Range.of q w)) : PtrFree (m.storePtr p x) q w := by
  refine h.modifyBlock fun b _ hid o ho ho' => ?_
  simp only [Range.Disjoint, Range.of, hid, ne_eq, not_true_eq_false, false_or] at hd
  by_cases hov : o + 64 ≤ p.offsetInBits ∨ p.offsetInBits + 64 ≤ o
  · refine .inl ?_
    rw [← MemoryBlock.ptrAt_storeDef (blk := b) (y := x.addrBits m.addr) (d := 0#64)
      (off := p.offsetInBits) (o := o) hov]
    refine MemoryBlock.ptrAt_congr ?_ rfl rfl
    simp only [show o ≠ p.offsetInBits by omega, ite_false]
  · -- a pointer the store meets: dropped
    refine .inr ?_
    simp only [MemoryBlock.ptrAt, show o ≠ p.offsetInBits by omega, ite_false,
      MemoryBlock.clearPtrs, show (0#64 = BitVec.allOnes 64) = False by decide]
    rw [ite_eq_right hov]

/-- A copy outside the range keeps `PtrFree`: the pointers it records lie inside it, and it kills
each other one it meets. -/
@[mlir_transport]
theorem PtrFree.storeCopy_of_disjoint {v : Nat} {y d : BitVec v} {P : Nat → Option Pointer}
    (h : PtrFree m q w) (hd : (Range.of p v).Disjoint (Range.of q w)) (hb : InBounds m p v) :
    PtrFree (m.storeCopy p y d P) q w := by
  refine h.modifyBlock fun b hb' hid o ho ho' => ?_
  obtain ⟨b', hb'', hsz⟩ := hb
  rw [hb''] at hb'
  cases hb'
  unfold MemoryBlock.lengthInBits at hsz
  simp only [Range.Disjoint, Range.of, hid, ne_eq, not_true_eq_false, false_or] at hd
  -- not a recorded one: as the masked store leaves it
  have hc : ({ b with
        bytes := spliceBits b.bytes p.offsetInBits y
        defined := spliceBits b.defined p.offsetInBits d
        ptrs := MemoryBlock.copyPtrs b.ptrs p.offsetInBits d P } : MemoryBlock).ptrAt m.addr o =
      ({ b with
        bytes := spliceBits b.bytes p.offsetInBits y
        defined := spliceBits b.defined p.offsetInBits d
        ptrs := MemoryBlock.clearPtrs b.ptrs p.offsetInBits d } : MemoryBlock).ptrAt m.addr o := by
    refine MemoryBlock.ptrAt_congr ?_ rfl rfl
    simp only [MemoryBlock.copyPtrs]
    rw [ite_eq_right (by omega)]
  rw [hc]
  by_cases hv : v = 0
  · subst hv; exact .inl MemoryBlock.ptrAt_storeDef_zero
  by_cases hov : o + 64 ≤ p.offsetInBits ∨ p.offsetInBits + v ≤ o
  · exact .inl (MemoryBlock.ptrAt_storeDef hov)
  · exact .inr (MemoryBlock.ptrAt_storeDef_overlap hsz (by omega) hov)

/-- A lifetime marker keeps `PtrFree`: it drops every pointer of its object. -/
@[mlir_transport]
theorem PtrFree.lifetimeStart (h : PtrFree m q w) : PtrFree (m.lifetimeStart p) q w :=
  h.modifyBlock fun _ _ _ _ _ _ => .inr (by simp [MemoryBlock.ptrAt])

@[mlir_transport]
theorem PtrFree.lifetimeEnd (h : PtrFree m q w) : PtrFree (m.lifetimeEnd p) q w :=
  h.modifyBlock fun _ _ _ _ _ _ => .inr (by simp [MemoryBlock.ptrAt])

/-- An `alloca` keeps `PtrFree` of a range in bounds before it. -/
@[mlir_transport]
theorem PtrFree.alloca {s : GlobalState} (hwf : s.WF) (hb : InBounds s.mem q w)
    (h : PtrFree s.mem q w) : PtrFree (s.alloca n d).mem q w := by
  refine ⟨fun o ho ho' => ?_⟩
  simpa only [MemoryState.ptrAt, GlobalState.addr_alloca,
    GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_inBounds hwf hb)] using h.poison o ho ho'

theorem PtrFree.mono (hv : v ≤ w) (h : PtrFree m q w) : PtrFree m q v :=
  ⟨fun o ho ho' => h.poison o (by omega) ho'⟩

/-- A range inside `q`'s has no live pointer over it either. -/
theorem PtrFree.add_of_le {off : BitVec 64} (hov : ¬q.offset.uaddOverflow off)
    (hw : off.toNat * 8 + w ≤ v) (h : PtrFree m q v) : PtrFree m (q.add off) w := by
  refine ⟨fun o ho ho' => ?_⟩
  rw [Pointer.offsetInBits_add hov] at ho ho'
  exact h.poison o (by omega) (by omega)

/-- A copy of bits with no live pointer over them keeps `PtrFree`: it records none. -/
@[mlir_transport]
theorem PtrFree.storeCopy_ptrsIn {v : Nat} {y d : BitVec v} {r : Pointer} {m' : MemoryState}
    (h : PtrFree m q w) (hs : PtrFree m' r v) (hb : InBounds m p v) :
    PtrFree (m.storeCopy p y d (m'.ptrsIn r v)) q w := by
  rw [MemoryState.ptrsIn_of_ptrFree hs, MemoryState.storeCopy_none]
  exact h.storeDef hb

/-- The same block at `q`, the same addresses: the same `PtrFree`. -/
theorem PtrFree.of_getElem?_eq {m' : MemoryState} (h : PtrFree m q w) (he : m'[q.id]? = m[q.id]?)
    (ha : m'.addr = m.addr) : PtrFree m' q w := by
  refine ⟨fun o ho ho' => ?_⟩
  simpa only [MemoryState.ptrAt, he, ha] using h.poison o ho ho'

/-- A new block has no pointers. -/
theorem PtrFree.alloca_new {s : GlobalState} (h : q.id = s.allocaPtr.id) :
    PtrFree (s.alloca n d).mem q w := by
  refine ⟨fun o _ _ => ?_⟩
  simp [MemoryState.ptrAt, h, GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq,
    MemoryBlock.ptrAt]

theorem PtrFree.allocaPtr {s : GlobalState} : PtrFree (s.alloca n d).mem s.allocaPtr w :=
  PtrFree.alloca_new rfl

end PtrFree

/-! ### `knownAt`: the bits a load reads -/

section KnownAt

variable {m : MemoryState} {p x : Pointer}

theorem MemoryBlock.getLsbD_inPtrs {b : MemoryBlock} :
    (b.inPtrs addr o w).getLsbD i = (decide (i < w) && b.inPtr addr (o + i)) := by
  simp only [MemoryBlock.inPtrs, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  by_cases hi : i < w <;> simp [List.getD_eq_getElem?_getD, hi]

/-- The known bits of a block: the defined ones and a live stored pointer's. -/
theorem MemoryState.knownAt_of_block {b : MemoryBlock} (hb : m[p.id]? = some b) :
    m.knownAt p w =
      b.defined.extractLsb' p.offsetInBits w ||| b.inPtrs m.addr p.offsetInBits w := by
  simp only [knownAt, hb]
  split
  · rename_i h; rw [h, BitVec.allOnes_or]
  · rfl

/-- Defined bits are known. -/
theorem MemoryState.knownAt_of_definedAt (h : m.definedAt p w = BitVec.allOnes w) :
    m.knownAt p w = BitVec.allOnes w := by
  cases hb : m[p.id]? with
  | none => simp only [definedAt, hb] at h; simp only [knownAt, hb]; exact h
  | some b =>
    simp only [definedAt, hb] at h
    rw [knownAt_of_block hb, h, BitVec.allOnes_or]

/-- Known bits are. -/
theorem MemoryState.knownAt_of_fits (h : Fits m p w) : m.knownAt p w = BitVec.allOnes w :=
  knownAt_of_definedAt (definedAt_of_fits h)

/-- A live stored pointer's bits are known: its address. -/
theorem MemoryState.knownAt_add_of_loadPtr {q : Pointer} {off : BitVec 64}
    (h : m.loadPtr p = .value q) (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ 64) :
    m.knownAt (p.add off) w = BitVec.allOnes w := by
  unfold loadPtr ptrAt at h
  split at h
  · rename_i b hb
    have hb' : m[(p.add off).id]? = some b := hb
    rw [knownAt_of_block hb']
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_or, MemoryBlock.getLsbD_inPtrs, BitVec.getLsbD_allOnes]
    simp only [hi, decide_true, Bool.true_and, MemoryBlock.inPtr, List.any_eq_true,
      List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    refine .inr ⟨off.toNat * 8 + i, by omega, by rw [Pointer.offsetInBits_add hov]; omega, ?_⟩
    rw [Pointer.offsetInBits_add hov, show p.offsetInBits + off.toNat * 8 + i -
      (off.toNat * 8 + i) = p.offsetInBits by omega, h]
    rfl
  · exact absurd h (PoisonOr.poison_ne_value q)

/-- `knownAt_add_of_loadPtr` at the pointer's start. -/
theorem MemoryState.knownAt_of_loadPtr {q : Pointer} (h : m.loadPtr p = .value q) (hw : w ≤ 64) :
    m.knownAt p w = BitVec.allOnes w := by
  simpa using
    knownAt_add_of_loadPtr (off := 0#64) h (by simp [BitVec.uaddOverflow, p.offset.isLt]) (by simpa)

/-- A stored pointer's bits are known: its address. -/
theorem MemoryState.knownAt_storePtr_self (h : Room m p 64) :
    (m.storePtr p x).knownAt p 64 = BitVec.allOnes 64 :=
  knownAt_of_loadPtr (loadPtr_storePtr_self h) (Nat.le_refl _)

/-- Without a live pointer over them, the bits a load reads as known are the defined ones. -/
theorem MemoryState.knownAt_of_ptrFree (h : PtrFree m p w) : m.knownAt p w = m.definedAt p w := by
  cases hb : m[p.id]? with
  | none => simp only [knownAt, definedAt, hb]
  | some b =>
    rw [knownAt_of_block hb]
    simp only [definedAt, hb]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_or, MemoryBlock.getLsbD_inPtrs]
    suffices b.inPtr m.addr (p.offsetInBits + i) = false by simp [this]
    simp only [MemoryBlock.inPtr, List.any_eq_false, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true', not_and]
    intro k hk hkj
    have := h.poison (p.offsetInBits + i - k) (by omega) (by omega)
    simp only [ptrAt, hb] at this
    simp [this]

end KnownAt

end

end MLIR
