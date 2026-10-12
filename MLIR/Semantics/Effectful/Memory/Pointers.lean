module

public import MLIR.Semantics.Effectful.Memory.Operations
import Std.Data.ExtHashMap.Lemmas

/-! Stored pointers: memories equal but for them (`SameBits`), `overlay`, `storePtr`, `loadPtr`. -/

namespace MLIR

open Memory

@[expose] public section

/-! ### Memories with the same bits -/

/-- `b` without its stored pointers. -/
def MemoryBlock.bits (b : MemoryBlock) : MemoryBlock :=
  { b with ptrs := fun _ => none }

/-- `m` and `m'` hold the same blocks, bits and lifetimes, their stored pointers aside. -/
def MemoryState.SameBits (m m' : MemoryState) : Prop :=
  ∀ i : BlockId, (m[i]?).map MemoryBlock.bits = (m'[i]?).map MemoryBlock.bits

namespace MemoryState.SameBits

variable {m m' : MemoryState}

theorem symm (h : m.SameBits m') : m'.SameBits m :=
  fun i => (h i).symm

/-- Blocks with the same bits: their length, bits, definedness and lifetime. -/
theorem block {i : BlockId} (h : m.SameBits m') {b : MemoryBlock} (hb : m[i]? = some b) :
    ∃ b', m'[i]? = some b' ∧ b'.bits = b.bits := by
  have := h i
  rw [hb] at this
  cases hb' : m'[i]? with
  | none => simp [hb'] at this
  | some b' => exact ⟨b', rfl, by simpa [hb'] using this.symm⟩

theorem readAt (h : m.SameBits m') : m.readAt p w = m'.readAt p w := by
  unfold MemoryState.readAt
  cases hb : m[p.id]? with
  | none =>
    cases hb' : m'[p.id]? with
    | none => rfl
    | some b' =>
      obtain ⟨b, hb2, -⟩ := h.symm.block hb'
      simp [hb] at hb2
  | some b =>
    obtain ⟨b', hb', he⟩ := h.block hb
    rw [hb']
    cases b; cases b'
    simp only [MemoryBlock.bits, MemoryBlock.mk.injEq] at he
    obtain ⟨rfl, he, -⟩ := he
    cases eq_of_heq he
    rfl

theorem definedAt (h : m.SameBits m') : m.definedAt p w = m'.definedAt p w := by
  unfold MemoryState.definedAt
  cases hb : m[p.id]? with
  | none =>
    cases hb' : m'[p.id]? with
    | none => rfl
    | some b' =>
      obtain ⟨b, hb2, -⟩ := h.symm.block hb'
      simp [hb] at hb2
  | some b =>
    obtain ⟨b', hb', he⟩ := h.block hb
    rw [hb']
    cases b; cases b'
    simp only [MemoryBlock.bits, MemoryBlock.mk.injEq] at he
    obtain ⟨rfl, -, he, -⟩ := he
    cases eq_of_heq he
    rfl

theorem inBounds (h : m.SameBits m') (hq : InBounds m p w) : InBounds m' p w := by
  obtain ⟨b, hb, hw⟩ := hq
  obtain ⟨b', hb', he⟩ := h.block hb
  refine ⟨b', hb', ?_⟩
  have : b'.length = b.length := by simpa [MemoryBlock.bits] using congrArg MemoryBlock.length he
  simp only [MemoryBlock.lengthInBits] at hw ⊢
  omega

theorem room (h : m.SameBits m') (hq : Room m p w) : Room m' p w := by
  obtain ⟨b, hb, hl, hw⟩ := hq
  obtain ⟨b', hb', he⟩ := h.block hb
  refine ⟨b', hb', ?_, ?_⟩
  · rw [← hl]; simpa [MemoryBlock.bits] using congrArg MemoryBlock.live he
  · have : b'.length = b.length := by simpa [MemoryBlock.bits] using congrArg MemoryBlock.length he
    simp only [MemoryBlock.lengthInBits] at hw ⊢
    omega

theorem fits (h : m.SameBits m') (hq : Fits m p w) : Fits m' p w := by
  obtain ⟨b, hb, hl, hw, hd⟩ := hq
  obtain ⟨b', hb', he⟩ := h.block hb
  cases b; cases b'
  simp only [MemoryBlock.bits, MemoryBlock.mk.injEq] at he
  obtain ⟨rfl, -, he, rfl, -⟩ := he
  cases eq_of_heq he
  exact ⟨_, hb', hl, hw, hd⟩

theorem mem (h : m.SameBits m') : k ∈ m.mem ↔ k ∈ m'.mem := by
  have := h k
  simp only [Std.ExtHashMap.mem_iff_isSome_getElem?, ← MemoryState.getElem?_eq]
  cases hb : m[k]? <;> cases hb' : m'[k]? <;> simp_all

end MemoryState.SameBits

/-- Two changes of one block agreeing but for the stored pointers keep the same bits. -/
theorem MemoryState.sameBits_modifyBlock_modifyBlock {m : MemoryState}
    {f g : MemoryBlock → MemoryBlock} (hfg : ∀ b, (f b).bits = (g b).bits) :
    (m.modifyBlock i f).SameBits (m.modifyBlock i g) := by
  intro j
  rw [getElem?_modifyBlock, getElem?_modifyBlock]
  split
  · cases m[i]? <;> simp [hfg]
  · rfl

/-! ### `overlay` -/

section Overlay

variable {m : MemoryState} {p q : Pointer}

@[simp, mlir_mem, mlir_state]
theorem MemoryState.unspec_overlay {x d : BitVec w} : (m.overlay p x d).unspec = m.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.addr_overlay {x d : BitVec w} : (m.overlay p x d).addr = m.addr :=
  rfl

/-- `overlay` holds `storeDef`'s bits. -/
theorem MemoryState.sameBits_overlay {x d : BitVec w} :
    (m.overlay p x d).SameBits (m.storeDef p x d) :=
  sameBits_modifyBlock_modifyBlock fun _ => rfl

/-- `overlay` defining every bit: `storeAt`. -/
theorem MemoryState.overlay_allOnes {x : BitVec w} :
    m.overlay p x (BitVec.allOnes w) = m.storeAt p x :=
  rfl

theorem MemoryState.getElem?_overlay_self {x d : BitVec w} (h : m[p.id]? = some blk) :
    (m.overlay p x d)[p.id]? =
      some
        { blk with
          bytes := spliceBits blk.bytes p.offsetInBits x
          defined := spliceBits blk.defined p.offsetInBits d } := by
  simp [overlay, getElem?_modifyBlock_self, h]

theorem MemoryState.getElem?_overlay_ne {x d : BitVec w} (h : q.id ≠ p.id) :
    (m.overlay p x d)[q.id]? = m[q.id]? :=
  getElem?_modifyBlock_ne h

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_overlay_self (hfits : InBounds m p w) (x d : BitVec w) :
    (m.overlay p x d).readAt p w = x :=
  sameBits_overlay.readAt.trans (readAt_storeDef_self hfits x d)

theorem MemoryState.definedAt_overlay_self (hfits : InBounds m p w) (x d : BitVec w) :
    (m.overlay p x d).definedAt p w = d :=
  sameBits_overlay.definedAt.trans (definedAt_storeDef_self hfits x d)

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_overlay_disjoint {v w : Nat}
    (h : (Range.of p v).Disjoint (Range.of q w)) (x d : BitVec v) :
    (m.overlay p x d).readAt q w = m.readAt q w :=
  sameBits_overlay.readAt.trans (readAt_storeDef_disjoint h x d)

theorem MemoryState.definedAt_overlay_disjoint {v w : Nat}
    (h : (Range.of p v).Disjoint (Range.of q w)) (x d : BitVec v) :
    (m.overlay p x d).definedAt q w = m.definedAt q w :=
  sameBits_overlay.definedAt.trans (definedAt_storeDef_disjoint h x d)

/-- A read inside an overlay: the overlaid bits. -/
theorem MemoryState.readAt_overlay_add {off : BitVec 64} (hfits : InBounds m p v)
    (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v) (x d : BitVec v) :
    (m.overlay p x d).readAt (p.add off) w = x.extractLsb' (off.toNat * 8) w :=
  sameBits_overlay.readAt.trans (readAt_storeDef_add hfits hov hw x d)

/-- A read at an overlay's start: the overlaid bits' low ones. -/
theorem MemoryState.readAt_overlay_le (hfits : InBounds m p v) (hw : w ≤ v) (x d : BitVec v) :
    (m.overlay p x d).readAt p w = x.extractLsb' 0 w :=
  sameBits_overlay.readAt.trans (readAt_storeDef_le hfits hw x d)

-- after the disjoint read: an overlay's read inside it resolves to its bits
attribute [mlir_read] MemoryState.readAt_overlay_add MemoryState.readAt_overlay_le

theorem InBounds.overlay_iff {x d : BitVec v} :
    InBounds (m.overlay q x d) p w ↔ InBounds m p w :=
  ⟨fun h => InBounds.storeDef_iff.1 (MemoryState.sameBits_overlay.inBounds h), fun h =>
    MemoryState.sameBits_overlay.symm.inBounds (InBounds.storeDef_iff.2 h)⟩

theorem Room.overlay_iff {x d : BitVec v} : Room (m.overlay q x d) p w ↔ Room m p w :=
  ⟨fun h => Room.storeDef_iff.1 (MemoryState.sameBits_overlay.room h), fun h =>
    MemoryState.sameBits_overlay.symm.room (Room.storeDef_iff.2 h)⟩

@[mlir_mem, mlir_transport]
theorem InBounds.overlay {x d : BitVec v} (h : InBounds m p w) : InBounds (m.overlay q x d) p w :=
  InBounds.overlay_iff.2 h

@[mlir_mem, mlir_transport]
theorem Room.overlay {x d : BitVec v} (h : Room m p w) : Room (m.overlay q x d) p w :=
  Room.overlay_iff.2 h

/-- An overlay elsewhere keeps known bits known. -/
@[mlir_transport]
theorem Fits.overlay_of_disjoint (hq : Fits m p w) (hd : (Range.of q v).Disjoint (Range.of p w))
    {x d : BitVec v} : Fits (m.overlay q x d) p w :=
  MemoryState.sameBits_overlay.symm.fits (hq.storeDef_of_disjoint hd)

/-- An overlay into a live block's room: a range inside it its mask defines is known. -/
theorem Fits.overlay_of_mask {x d : BitVec v} {off : BitVec 64} (h : Room m p v)
    (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v)
    (hd : d.extractLsb' (off.toNat * 8) w = BitVec.allOnes w) :
    Fits (m.overlay p x d) (p.add off) w :=
  MemoryState.sameBits_overlay.symm.fits (Fits.storeDef_of_mask h hov hw hd)

/-- `overlay_of_mask` from the overlay's start. -/
theorem Fits.overlay_of_mask_self {x d : BitVec v} (h : Room m p v) (hw : w ≤ v)
    (hd : d.extractLsb' 0 w = BitVec.allOnes w) : Fits (m.overlay p x d) p w :=
  MemoryState.sameBits_overlay.symm.fits (Fits.storeDef_of_mask_self h hw hd)

/-- A copy's range known where its source's is, overlaid. -/
theorem Fits.overlay_definedAt {x : BitVec v} {off : BitVec 64} (h : Room m p v)
    (hs : Fits m (q.add off) w) (hov : ¬p.offset.uaddOverflow off)
    (hovq : ¬q.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v) :
    Fits (m.overlay p x (m.definedAt q v)) (p.add off) w :=
  MemoryState.sameBits_overlay.symm.fits (Fits.storeDef_definedAt h hs hov hovq hw)

/-- `overlay_definedAt` from the overlay's start. -/
theorem Fits.overlay_definedAt_self {x : BitVec v} (h : Room m p v) (hs : Fits m q w)
    (hw : w ≤ v) : Fits (m.overlay p x (m.definedAt q v)) p w :=
  MemoryState.sameBits_overlay.symm.fits (Fits.storeDef_definedAt_self h hs hw)

@[simp, mlir_mem]
theorem GlobalState.WF_overlay {s : GlobalState} {x d : BitVec v} :
    ({ s with mem := m.overlay p x d } : GlobalState).WF ↔
      ({ s with mem := m } : GlobalState).WF :=
  WF_modifyBlock

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.overlay {s : GlobalState} {x d : BitVec v} (h : s.WF) :
    { s with mem := s.mem.overlay p x d }.WF :=
  GlobalState.WF_overlay.2 h

/-- `WF.overlay` for a state written as a constructor, which unifies first-order. -/
@[mlir_transport]
theorem GlobalState.WF.overlay_mk {a : AllocState} {x d : BitVec v}
    (h : (⟨a, m⟩ : GlobalState).WF) : (⟨a, m.overlay p x d⟩ : GlobalState).WF :=
  GlobalState.WF.overlay (s := ⟨a, m⟩) h

/-- Erasing a frame commutes with an overlay. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.eraseFrom_overlay {x d : BitVec w} :
    (m.overlay p x d).eraseFrom n = (m.eraseFrom n).overlay p x d :=
  eraseFrom_modifyBlock

/-- An overlay of an erased block does nothing. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.overlay_eraseFrom_of_le {x d : BitVec w} (h : n ≤ p.id.id) :
    (m.eraseFrom n).overlay p x d = m.eraseFrom n :=
  modifyBlock_eraseFrom_of_le h

/-- An overlay in the frame, dropped before the erase moves past it. -/
@[mlir_erase high]
theorem MemoryState.eraseFrom_overlay_of_le {x d : BitVec w} (h : n ≤ p.id.id) :
    (m.overlay p x d).eraseFrom n = m.eraseFrom n := by
  rw [eraseFrom_overlay, overlay_eraseFrom_of_le h]

end Overlay

/-! ### `storePtr` -/

section StorePtr

variable {m : MemoryState} {p q x : Pointer}

@[simp, mlir_mem, mlir_state]
theorem MemoryState.unspec_storePtr : (m.storePtr p x).unspec = m.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.addr_storePtr : (m.storePtr p x).addr = m.addr :=
  rfl

/-- `storePtr` holds `storeDef`'s bits of an undefined pointer. -/
theorem MemoryState.sameBits_storePtr : (m.storePtr p x).SameBits (m.storeDef p 0#64 0#64) :=
  sameBits_modifyBlock_modifyBlock fun _ => rfl

/-- `storePtr` is `storeDef` of its undefined bits, then `x` recorded. -/
theorem MemoryState.storePtr_eq :
    m.storePtr p x = (m.storeDef p 0#64 0#64).recordPtr p.id p.offsetInBits x := by
  simp only [storePtr, recordPtr, storeDef, modifyBlock, MemoryState.mk.injEq, and_true]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_modify, beq_iff_eq]
  split
  · subst_vars
    cases m.mem[p.id]? <;> rfl
  · rfl

theorem MemoryState.getElem?_storePtr_ne (h : q.id ≠ p.id) : (m.storePtr p x)[q.id]? = m[q.id]? :=
  getElem?_modifyBlock_ne h

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_storePtr_disjoint (h : (Range.of p 64).Disjoint (Range.of q w)) :
    (m.storePtr p x).readAt q w = m.readAt q w :=
  sameBits_storePtr.readAt.trans (readAt_storeDef_disjoint h _ _)

theorem MemoryState.definedAt_storePtr_disjoint (h : (Range.of p 64).Disjoint (Range.of q w)) :
    (m.storePtr p x).definedAt q w = m.definedAt q w :=
  sameBits_storePtr.definedAt.trans (definedAt_storeDef_disjoint h _ _)

/-- A stored pointer's bits are undefined. -/
theorem MemoryState.definedAt_storePtr_self (h : InBounds m p 64) :
    (m.storePtr p x).definedAt p 64 = 0#64 :=
  sameBits_storePtr.definedAt.trans (definedAt_storeDef_self h _ _)

theorem InBounds.storePtr_iff : InBounds (m.storePtr q x) p w ↔ InBounds m p w :=
  ⟨fun h => InBounds.storeDef_iff.1 (MemoryState.sameBits_storePtr.inBounds h), fun h =>
    MemoryState.sameBits_storePtr.symm.inBounds (InBounds.storeDef_iff.2 h)⟩

theorem Room.storePtr_iff : Room (m.storePtr q x) p w ↔ Room m p w :=
  ⟨fun h => Room.storeDef_iff.1 (MemoryState.sameBits_storePtr.room h), fun h =>
    MemoryState.sameBits_storePtr.symm.room (Room.storeDef_iff.2 h)⟩

@[mlir_mem, mlir_transport]
theorem InBounds.storePtr (h : InBounds m p w) : InBounds (m.storePtr q x) p w :=
  InBounds.storePtr_iff.2 h

@[mlir_mem, mlir_transport]
theorem Room.storePtr (h : Room m p w) : Room (m.storePtr q x) p w :=
  Room.storePtr_iff.2 h

/-- A pointer stored elsewhere keeps known bits known. -/
@[mlir_transport]
theorem Fits.storePtr_of_disjoint (hq : Fits m p w) (hd : (Range.of q 64).Disjoint (Range.of p w)) :
    Fits (m.storePtr q x) p w :=
  MemoryState.sameBits_storePtr.symm.fits (hq.storeDef_of_disjoint hd)

@[simp, mlir_mem]
theorem GlobalState.WF_storePtr {s : GlobalState} :
    ({ s with mem := m.storePtr p x } : GlobalState).WF ↔
      ({ s with mem := m } : GlobalState).WF :=
  WF_modifyBlock

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.storePtr {s : GlobalState} (h : s.WF) :
    { s with mem := s.mem.storePtr p x }.WF :=
  GlobalState.WF_storePtr.2 h

/-- `WF.storePtr` for a state written as a constructor, which unifies first-order. -/
@[mlir_transport]
theorem GlobalState.WF.storePtr_mk {a : AllocState} (h : (⟨a, m⟩ : GlobalState).WF) :
    (⟨a, m.storePtr p x⟩ : GlobalState).WF :=
  GlobalState.WF.storePtr (s := ⟨a, m⟩) h

/-- Erasing a frame commutes with a pointer store. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.eraseFrom_storePtr :
    (m.storePtr p x).eraseFrom n = (m.eraseFrom n).storePtr p x :=
  eraseFrom_modifyBlock

/-- A pointer stored into an erased block does nothing. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.storePtr_eraseFrom_of_le (h : n ≤ p.id.id) :
    (m.eraseFrom n).storePtr p x = m.eraseFrom n :=
  modifyBlock_eraseFrom_of_le h

/-- A pointer store in the frame, dropped before the erase moves past it. -/
@[mlir_erase high]
theorem MemoryState.eraseFrom_storePtr_of_le (h : n ≤ p.id.id) :
    (m.storePtr p x).eraseFrom n = m.eraseFrom n := by
  rw [eraseFrom_storePtr, storePtr_eraseFrom_of_le h]

end StorePtr


/-! ### `recordPtrs`: a store's pointer leaves -/

/-- The pointers `ptrs` recorded as stored from `p` on, by their bit offsets from it. -/
def MemoryState.recordPtrs (m : MemoryState) (p : Pointer) (ptrs : List (Nat × Pointer)) :
    MemoryState :=
  ptrs.foldl (fun m (o, q) => m.recordPtr p.id (p.offsetInBits + o) q) m

@[simp]
theorem MemoryState.recordPtrs_nil {m : MemoryState} {p : Pointer} : m.recordPtrs p [] = m :=
  rfl

/-! ### `loadPtr`: the stored pointers, read back -/

section LoadPtr

variable {m : MemoryState} {p q x : Pointer}

/-- A block's stored pointer at bit `o`, by its entry and its 64 bits' definedness. -/
theorem MemoryBlock.ptrAt_congr {b b' : MemoryBlock} (hp : b'.ptrs o = b.ptrs o)
    (hd : b'.defined.extractLsb' o 64 = b.defined.extractLsb' o 64) : b'.ptrAt o = b.ptrAt o := by
  simp only [MemoryBlock.ptrAt, hp, hd]

/-- `loadPtr` by the block's entry and definedness at `p`. -/
theorem MemoryState.loadPtr_eq_of_block {b : MemoryBlock} (h : m[p.id]? = some b) :
    m.loadPtr p = b.ptrAt p.offsetInBits := by
  simp [loadPtr, ptrAt, h]

/-- A pointer stored in bounds loads back. -/
@[mlir_mem, mlir_read]
theorem MemoryState.loadPtr_storePtr_self (h : InBounds m p 64) :
    (m.storePtr p x).loadPtr p = .value x := by
  obtain ⟨blk, hblk, hsz⟩ := h
  unfold MemoryBlock.lengthInBits at hsz
  simp [loadPtr, ptrAt, storePtr, getElem?_modifyBlock_self, hblk, MemoryBlock.ptrAt,
    extractLsb'_spliceBits_self _ _ _ hsz]

/-- A block's entry and definedness at `o` past a masked store disjoint from it. -/
theorem MemoryBlock.ptrAt_storeDef {blk : MemoryBlock} {off o v : Nat} {y d : BitVec v}
    (h : o + 64 ≤ off ∨ off + v ≤ o) :
    ({ blk with
        bytes := spliceBits blk.bytes off y
        defined := spliceBits blk.defined off d
        ptrs := MemoryBlock.clearPtrs blk.ptrs off d } : MemoryBlock).ptrAt o = blk.ptrAt o := by
  apply MemoryBlock.ptrAt_congr
  · simp only [MemoryBlock.clearPtrs]
    split <;> simp [h]
  · exact extractLsb'_spliceBits_of_disjoint _ _ _ _ (by omega)

/-- `loadPtr` past a change of `p`'s block by `f`, which keeps the entry and definedness at `q`. -/
theorem MemoryState.loadPtr_modifyBlock {i : BlockId} {f : MemoryBlock → MemoryBlock}
    (hf : ∀ b : MemoryBlock, (f b).ptrAt q.offsetInBits = b.ptrAt q.offsetInBits) :
    (m.modifyBlock i f).loadPtr q = m.loadPtr q := by
  unfold loadPtr ptrAt
  rw [getElem?_modifyBlock]
  by_cases h : i = q.id
  · subst h
    simp only [ite_true]
    cases m[q.id]? <;> simp [hf]
  · simp [h]

@[mlir_mem, mlir_read]
theorem MemoryState.loadPtr_storeDef_disjoint {v : Nat}
    (h : (Range.of p v).Disjoint (Range.of q 64)) (y d : BitVec v) :
    (m.storeDef p y d).loadPtr q = m.loadPtr q := by
  by_cases hid : q.id = p.id
  · simp only [Range.Disjoint, Range.of, hid, ne_eq, not_true_eq_false, false_or] at h
    exact loadPtr_modifyBlock fun _ => MemoryBlock.ptrAt_storeDef (by omega)
  · simp only [loadPtr, ptrAt, storeDef, getElem?_modifyBlock_ne hid]

@[mlir_mem, mlir_read]
theorem MemoryState.loadPtr_storeAt_disjoint {v : Nat}
    (h : (Range.of p v).Disjoint (Range.of q 64)) (y : BitVec v) :
    (m.storeAt p y).loadPtr q = m.loadPtr q := by
  rw [storeAt_eq_storeDef]; exact loadPtr_storeDef_disjoint h y _

@[mlir_mem, mlir_read]
theorem MemoryState.loadPtr_overlay_disjoint {v : Nat}
    (h : (Range.of p v).Disjoint (Range.of q 64)) (y d : BitVec v) :
    (m.overlay p y d).loadPtr q = m.loadPtr q := by
  by_cases hid : q.id = p.id
  · simp only [Range.Disjoint, Range.of, hid, ne_eq, not_true_eq_false, false_or] at h
    refine loadPtr_modifyBlock fun _ => MemoryBlock.ptrAt_congr rfl ?_
    exact extractLsb'_spliceBits_of_disjoint _ _ _ _ (by omega)
  · simp only [loadPtr, ptrAt, overlay, getElem?_modifyBlock_ne hid]

@[mlir_mem, mlir_read]
theorem MemoryState.loadPtr_storePtr_disjoint (h : (Range.of p 64).Disjoint (Range.of q 64)) :
    (m.storePtr p x).loadPtr q = m.loadPtr q := by
  by_cases hid : q.id = p.id
  · simp only [Range.Disjoint, Range.of, hid, ne_eq, not_true_eq_false, false_or] at h
    refine loadPtr_modifyBlock fun b => ?_
    rw [← MemoryBlock.ptrAt_storeDef (blk := b) (y := 0#64) (d := 0#64) (off := p.offsetInBits)
      (o := q.offsetInBits) (by omega)]
    refine MemoryBlock.ptrAt_congr ?_ rfl
    simp only [show q.offsetInBits ≠ p.offsetInBits by omega, ite_false]
  · simp only [loadPtr, ptrAt, storePtr, getElem?_modifyBlock_ne hid]

/-- A lifetime marker of another object keeps the stored pointers. -/
@[mlir_mem, mlir_read]
theorem MemoryState.loadPtr_lifetimeStart (h : q.id ≠ p.id) :
    (m.lifetimeStart p).loadPtr q = m.loadPtr q := by
  simp only [loadPtr, ptrAt, lifetimeStart, setLifetime, getElem?_modifyBlock_ne h]

/-- A lifetime marker of another object keeps the stored pointers. -/
@[mlir_mem, mlir_read]
theorem MemoryState.loadPtr_lifetimeEnd (h : q.id ≠ p.id) :
    (m.lifetimeEnd p).loadPtr q = m.loadPtr q := by
  simp only [loadPtr, ptrAt, lifetimeEnd, setLifetime, getElem?_modifyBlock_ne h]

@[mlir_read]
theorem MemoryState.loadPtr_alloca {s : GlobalState} (hwf : s.WF) (h : InBounds s.mem q w') :
    (s.alloca n d).mem.loadPtr q = s.mem.loadPtr q := by
  simp only [loadPtr, ptrAt,
    GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_inBounds hwf h)]

/-- `loadPtr_alloca` with the pointer's own width, which `loadPtr_alloca`'s open width never
matches. -/
@[mlir_read]
theorem MemoryState.loadPtr_alloca_of_fits {s : GlobalState} (hwf : s.WF)
    (h : InBounds s.mem q 64) : (s.alloca n d).mem.loadPtr q = s.mem.loadPtr q :=
  loadPtr_alloca hwf h

/-- A load outside a new block: the load before it. -/
@[mlir_read]
theorem MemoryState.loadPtr_addBlock_of_id_ne {b : BlockId} {y : BitVec v} (h : q.id ≠ b) :
    (m.addBlock b n y).loadPtr q = m.loadPtr q := by
  have hget : (m.addBlock b n y)[q.id]? = m[q.id]? := by
    simp only [MemoryState.addBlock, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert]
    split
    · rename_i heq
      exact absurd (beq_iff_eq.mp heq).symm h
    · rfl
  simp only [loadPtr, ptrAt, hget]

/-- A load of a block in bounds before a new one: the load before it. -/
@[mlir_read]
theorem MemoryState.loadPtr_addBlock {s : GlobalState} {y : BitVec v} (hwf : s.WF)
    (h : InBounds s.mem q w') :
    (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n y).loadPtr q = s.mem.loadPtr q :=
  loadPtr_addBlock_of_id_ne (GlobalState.ne_allocaPtr_of_inBounds hwf h)

end LoadPtr

end

end MLIR
