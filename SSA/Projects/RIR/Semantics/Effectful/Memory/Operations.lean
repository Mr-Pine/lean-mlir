module

public import SSA.Projects.RIR.Semantics.Effectful.Memory
public import SSA.Projects.RIR.Memory.Range
public import SSA.Projects.RIR.Semantics.Effectful.Memory.Bits
public import SSA.Projects.RIR.Semantics.Effectful.Memory.Fits
public import SSA.Projects.RIR.SimpSets
import Std.Data.ExtHashMap.Lemmas

namespace LeanMLIR.RIR

open Memory

@[expose] public section

/-- Store bytes at a pointer. If the pointer does not reference a live block, this is a no-op. -/
def MemoryState.storeAt (m : MemoryState) (p : Pointer) {w : Nat} (b : BitVec w) : MemoryState :=
  match m[p.id]? with
  | some block =>
    let newBytes := spliceBits block.bytes p.offsetInBits b
    { m with mem := m.mem.insert p.id { block with bytes := newBytes } }
  | _ => m

/-- Read bytes at a pointer. Returns `0#w` if there is no block for the pointer. -/
def MemoryState.readAt (m : MemoryState) (p : Pointer) (w : Nat) : BitVec w :=
  match m[p.id]? with
  | some block => block.bytes.extractLsb' p.offsetInBits _
  | _ => 0

/-- The pointer the next `alloca` returns: offset 0 in the next free block. -/
def GlobalState.allocaPtr (s : GlobalState) : Pointer :=
  ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩

/-- Allocate a zeroed block of `bytes` bytes at `allocaPtr`, and bump the counter. -/
def GlobalState.alloca (s : GlobalState) (bytes : Nat) : GlobalState :=
  { alloc := ⟨s.alloc.nextFreeBlock + 1⟩,
    mem := ⟨s.mem.mem.insert ⟨s.alloc.nextFreeBlock⟩ ⟨bytes, 0⟩⟩ }

/-- Remove every block with id `n` or above: a returning callee's frame. -/
def MemoryState.eraseFrom (m : MemoryState) (n : Nat) : MemoryState :=
  { mem := m.mem.filter fun id _ => id.id < n }

section Theorems

/-- The an existing block is overwritten with `storeAt` -/
@[mlir_mem]
theorem MemoryState.getElem?_storeAt_self {m : MemoryState} (h : m[p.id]? = some blk) :
    (m.storeAt p x)[p.id]? = some { blk with bytes := spliceBits blk.bytes p.offsetInBits x } := by
  simp [storeAt, h, MemoryState.getElem?_eq]

/-- Other blocks are not modified by `storeAt` -/
@[mlir_mem]
theorem MemoryState.getElem?_storeAt_ne {m : MemoryState} {p q : Pointer} (hptr : q.id ≠ p.id) :
    (m.storeAt p x)[q.id]? = m[q.id]? := by
  simp [storeAt]
  cases m[p.id]? with
  | none => simp
  | some _ =>
    simp [MemoryState.getElem?_eq] at ⊢
    simp [Std.ExtHashMap.getElem?_insert, hptr.symm]

/-- `storeAt` does not change whether an id is allocated or not. -/
@[mlir_mem]
theorem MemoryState.getElem?_storeAt_isSome {m : MemoryState} {i : BlockId} :
    ((m.storeAt p x)[i]?).isSome = (m[i]?).isSome := by
  by_cases h : p.id = i
  · rw [← h]
    cases h : m[p.id]? with
    | none => simp [storeAt, h]
    | some blk => simp [getElem?_storeAt_self h]
  · cases h' : m[p.id]? with
    | none => simp [storeAt, h']
    | some blk => simp [storeAt, h', getElem?_eq, h]

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_storeAt_self (hfits : Fits m p w) (x : BitVec w) :
    (m.storeAt p x).readAt p w = x := by
  obtain ⟨blk, hblk, hsz⟩ := hfits
  unfold MemoryBlock.lengthInBits at hsz
  simp [readAt, getElem?_storeAt_self hblk, extractLsb'_spliceBits_self, hsz]

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_storeAt_disjoint {v w : Nat} {m : MemoryState}
    (h : (Range.of p v).Disjoint (Range.of q w)) (x : BitVec v) :
    (m.storeAt p x).readAt q w = m.readAt q w := by
  simp [readAt]
  by_cases hid : q.id = p.id
  · simp [Range.Disjoint, hid, Range.of] at h
    cases h' : m[q.id]? with
    | none => grind [getElem?_storeAt_isSome]
    | some blk =>
      simp [hid] at h' ⊢
      rw [getElem?_storeAt_self h']
      simp
      apply extractLsb'_spliceBits_of_disjoint
      omega
  · cases h' : m[q.id]? <;> grind [getElem?_storeAt_isSome, getElem?_storeAt_ne]

@[mlir_mem]
theorem MemoryState.readAt_storeAt_subrange (hfits : Fits m p v) (hid : q.id = p.id)
    (hle : p.offsetInBits ≤ q.offsetInBits) (hw : (q.offsetInBits - p.offsetInBits) + w' ≤ v)
    (x : BitVec v) :
    (m.storeAt p x).readAt q w' = x.extractLsb' (q.offsetInBits - p.offsetInBits) w' := by
  obtain ⟨blk, hblk, hsz⟩ := hfits
  simp [readAt, hid, getElem?_storeAt_self hblk]
  exact extractLsb'_spliceBits_of_subrange _ _ _ _ (by omega) hw hsz

/-- `p.add off`'s offset in bits, without overflow. -/
theorem Pointer.offsetInBits_add {p : Pointer} {off : BitVec 64}
    (hov : ¬p.offset.uaddOverflow off) :
    (p.add off).offsetInBits = p.offsetInBits + off.toNat * 8 := by
  simp only [Pointer.offsetInBits, Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hov]
  omega

/-- A range inside `p`'s fits too. -/
theorem Fits.add_of_le {off : BitVec 64} (hov : ¬p.offset.uaddOverflow off)
    (hw : off.toNat * 8 + w ≤ v) (h : Fits m p v) : Fits m (p.add off) w := by
  obtain ⟨blk, hblk, hsz⟩ := h
  exact
    ⟨blk, hblk, by
      rw [Pointer.offsetInBits_add hov]; omega⟩

/-- A read inside a store: the stored value's bits. -/
@[mlir_read]
theorem MemoryState.readAt_storeAt_add {off : BitVec 64} (hfits : Fits m p v)
    (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v) (x : BitVec v) :
    (m.storeAt p x).readAt (p.add off) w = x.extractLsb' (off.toNat * 8) w := by
  rw [readAt_storeAt_subrange (q := p.add off) hfits rfl
      (by
        rw [Pointer.offsetInBits_add hov]; omega)
      (by
        rw [Pointer.offsetInBits_add hov]; omega)]
  rw [Pointer.offsetInBits_add hov, Nat.add_sub_cancel_left]

/-- A read inside a known read: its bits. -/
theorem MemoryState.readAt_add_of_readAt {off : BitVec 64} (hfits : Fits m p v)
    (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v) (h : m.readAt p v = x) :
    m.readAt (p.add off) w = x.extractLsb' (off.toNat * 8) w := by
  subst h
  obtain ⟨blk, hblk, hsz⟩ := hfits
  have hblk' : m[(p.add off).id]? = some blk := hblk
  simp only [readAt, hblk, hblk', Pointer.offsetInBits_add hov]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  grind

/-- A read over a store inside it: the bits read before, with the stored ones spliced in. -/
@[mlir_read]
theorem MemoryState.readAt_add_storeAt {off : BitVec 64} (hfits : Fits m p v)
    (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v) (x : BitVec w) :
    (m.storeAt (p.add off) x).readAt p v = spliceBits (m.readAt p v) (off.toNat * 8) x := by
  obtain ⟨blk, hblk, hsz⟩ := hfits
  have hs :
    (m.storeAt (p.add off) x)[p.id]? =
      some { blk with bytes := spliceBits blk.bytes (p.add off).offsetInBits x } :=
    getElem?_storeAt_self (p := p.add off) hblk
  simp only [readAt, hs, hblk]
  unfold MemoryBlock.lengthInBits at hsz
  rw [Pointer.offsetInBits_add hov]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', getLsbD_spliceBits]
  grind

@[mlir_mem, mlir_transport]
theorem Fits.storeAt (hq : Fits m p w) : Fits (m.storeAt q x) p w := by
  unfold Fits
  obtain ⟨blk, hblk, hsz⟩ := hq
  grind [MemoryState.getElem?_storeAt_self, MemoryState.getElem?_storeAt_ne,
    MemoryBlock.lengthInBits]

@[mlir_mem]
theorem MemoryState.readAt_storeAt_disjoint_offset {m : MemoryState} {off} {x : BitVec w}
    (hoff : ¬(p.offset.uaddOverflow off)) (hoff' : off < 2 ^ 64 := by decide)
    (hdisj : off >= w := by decide) :
    (m.storeAt p x).readAt (p.add off) w = m.readAt (p.add off) w := by
  apply readAt_storeAt_disjoint
  dsimp at hoff
  simp [Range.of, Range.Disjoint, Pointer.add]
  simp only [Pointer.offsetInBits, BitVec.toNat_add_of_not_uaddOverflow hoff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hoff']
  omega

/-- A store keeps the set of blocks, so `WF` does not depend on it. -/
@[simp, mlir_mem]
theorem GlobalState.WF_storeAt {s : GlobalState} :
    ({ s with mem := m.storeAt p x } : GlobalState).WF ↔
      ({ s with mem := m } : GlobalState).WF := by
  simp only [GlobalState.WF, MemoryState.storeAt]
  split
  · rename_i blk hblk
    rw [MemoryState.getElem?_eq] at hblk
    constructor
    · intro h k hk
      exact h k (Std.ExtHashMap.mem_insert.2 (.inr hk))
    · intro h k hk
      rcases Std.ExtHashMap.mem_insert.1 hk with hk | hk
      · have : p.id = k := by simpa using hk
        subst this
        exact
          h _
            (Std.ExtHashMap.mem_iff_isSome_getElem?.2
              (by
                rw [hblk]; rfl))
      · exact h k hk
  · exact Iff.rfl

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.storeAt {s : GlobalState} (h : s.WF) :
    { s with mem := s.mem.storeAt p x }.WF := by
  unfold GlobalState.WF
  intro k hk
  dsimp at *
  simp only [MemoryState.storeAt] at hk
  split at hk
  case h_1 blk hblk =>
    dsimp at hk
    rw [Std.ExtHashMap.mem_insert] at hk
    rcases hk with hk | hk
    · simp at hk
      replace hk := hk.symm
      subst hk
      rw [MemoryState.getElem?_eq] at hblk
      replace hblk := Option.isSome_of_eq_some hblk
      simp at hblk
      refine h p.id hblk
    · exact h k hk
  case h_2 => exact h k hk

@[mlir_mem]
theorem GlobalState.eraseFrom_self {s : GlobalState} (hs : s.WF) :
    { s with mem := s.mem.eraseFrom s.alloc.nextFreeBlock } = s := by
  ext : 2 <;> dsimp
  rw [MemoryState.eraseFrom]
  dsimp
  rw [Std.ExtHashMap.filter_eq_self_iff]
  intro k hk
  simp
  exact hs k hk

/-! ### `alloca` and frames -/

/-- A block in memory has an id below the counter. -/
theorem GlobalState.WF.lt {s : GlobalState} (h : s.WF) (hq : q ∈ s.mem.mem) :
    q.id < s.alloc.nextFreeBlock :=
  h q hq

theorem Fits.mem (h : Fits m p w) : p.id ∈ m.mem := by
  obtain ⟨b, hb, _⟩ := h
  rw [MemoryState.getElem?_eq] at hb
  exact
    Std.ExtHashMap.mem_iff_isSome_getElem?.2
      (by
        rw [hb]; rfl)

/-- A pointer into memory is not the next `alloca`'s. -/
theorem GlobalState.ne_allocaPtr_of_fits {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w) :
    q.id ≠ s.allocaPtr.id := by
  intro heq
  have := hwf.lt h.mem
  simp [heq, GlobalState.allocaPtr] at this

/-- Advancing the block counter keeps a state well-formed: a callee's frames, freed again. -/
@[mlir_transport]
theorem GlobalState.WF.add_blocks {s : GlobalState} (h : s.WF) :
    (⟨⟨s.alloc.nextFreeBlock + k⟩, s.mem⟩ : GlobalState).WF := by
  intro b hb
  have := h b hb
  dsimp
  omega

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.alloca {s : GlobalState} (h : s.WF) : (s.alloca n).WF := by
  intro k hk
  simp only [GlobalState.alloca, Std.ExtHashMap.mem_insert] at hk ⊢
  rcases hk with hk | hk
  · have : (⟨s.alloc.nextFreeBlock⟩ : BlockId) = k := by simpa using hk
    subst this; simp
  · have := h k hk; omega

/-- `alloca` adds a block under a fresh id: the others are unchanged. -/
theorem GlobalState.getElem?_alloca {s : GlobalState} (hq : q ≠ s.allocaPtr.id) :
    (s.alloca n).mem[q]? = s.mem[q]? := by
  simp only [GlobalState.alloca, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert]
  split
  · rename_i h
    exact absurd (show s.allocaPtr.id = q by simpa [GlobalState.allocaPtr] using h) (Ne.symm hq)
  · rfl

@[mlir_transport]
theorem Fits.alloca {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w) :
    Fits (s.alloca n).mem q w := by
  obtain ⟨b, hb, hs⟩ := h
  refine ⟨b, ?_, hs⟩
  rw [GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_fits hwf ⟨b, hb, hs⟩)]
  exact hb

theorem Fits.allocaPtr {s : GlobalState} (hw : w ≤ 8 * n) :
    Fits (s.alloca n).mem s.allocaPtr w := by
  refine ⟨⟨n, 0⟩, ?_, ?_⟩
  · simp [GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
  · simp [Pointer.offsetInBits, GlobalState.allocaPtr, MemoryBlock.lengthInBits]; omega

@[mlir_read]
theorem MemoryState.readAt_alloca {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w') :
    (s.alloca n).mem.readAt q w = s.mem.readAt q w := by
  simp only [MemoryState.readAt,
    GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_fits hwf h)]

/-- Erasing a frame commutes with a store: a store into the frame is lost either way. -/
@[mlir_frame]
theorem MemoryState.eraseFrom_storeAt {m : MemoryState} {p : Pointer} {x : BitVec w} :
    (m.storeAt p x).eraseFrom n = (m.eraseFrom n).storeAt p x := by
  have hg : (m.eraseFrom n)[p.id]? = m[p.id]?.filter (fun _ => decide (p.id.id < n)) := by
    simp [MemoryState.eraseFrom, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_filter']
  unfold MemoryState.storeAt
  rw [hg]
  cases hm : m[p.id]? with
  | none => simp
  | some blk =>
    simp only [Option.filter_some]
    by_cases hlt : p.id.id < n
    · simp only [hlt, decide_true, ite_true, MemoryState.eraseFrom, MemoryState.mk.injEq]
      apply Std.ExtHashMap.ext_getElem?
      intro k
      simp only [Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_insert]
      split <;> simp_all
    · simp only [hlt, decide_false, Bool.false_eq_true, ite_false, MemoryState.eraseFrom,
        MemoryState.mk.injEq]
      apply Std.ExtHashMap.ext_getElem?
      intro k
      simp only [Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_insert]
      split
      · rename_i h; simp at h; subst h; simp [hlt, MemoryState.getElem?_eq] at hm ⊢
      · rfl

@[mlir_frame]
theorem GlobalState.eraseFrom_alloca {s : GlobalState} :
    (s.alloca b).mem.eraseFrom s.alloc.nextFreeBlock = s.mem.eraseFrom s.alloc.nextFreeBlock := by
  simp only [GlobalState.alloca, MemoryState.eraseFrom, MemoryState.mk.injEq]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_insert]
  split
  · rename_i h; simp at h; subst h; simp
  · rfl

/-- An `alloca` at or above `n` is gone once the frame from `n` is erased. -/
@[mlir_frame]
theorem GlobalState.eraseFrom_alloca_of_le {s : GlobalState} (h : n ≤ s.alloc.nextFreeBlock) :
    (s.alloca b).mem.eraseFrom n = s.mem.eraseFrom n := by
  simp only [GlobalState.alloca, MemoryState.eraseFrom, MemoryState.mk.injEq]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_insert]
  split
  · rename_i h'; simp at h'; subst h'; simp [show ¬s.alloc.nextFreeBlock < n by omega]
  · rfl

/-- A store into an erased block does nothing. -/
@[mlir_frame]
theorem MemoryState.storeAt_eraseFrom_of_le {m : MemoryState} {p : Pointer} {x : BitVec w}
    (h : n ≤ p.id.id) : (m.eraseFrom n).storeAt p x = m.eraseFrom n := by
  have : (m.eraseFrom n)[p.id]? = none := by
    simp [MemoryState.eraseFrom, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_filter']
    intro _ _; omega
  simp [MemoryState.storeAt, this]

/-- In a `WF` state nothing sits at or above the counter: erasing from it changes nothing. -/
@[mlir_frame]
theorem GlobalState.WF.eraseFrom {s : GlobalState} (h : s.WF) :
    s.mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  have := GlobalState.eraseFrom_self h
  exact congrArg GlobalState.mem this

/-- `WF.storeAt` for a state written as a constructor, which unifies first-order. -/
@[mlir_transport]
theorem GlobalState.WF.storeAt_mk {a : AllocState} {m : MemoryState}
    (h : (⟨a, m⟩ : GlobalState).WF) : (⟨a, m.storeAt p x⟩ : GlobalState).WF :=
  GlobalState.WF.storeAt (s := ⟨a, m⟩) h

/-- In a `WF` state there is no block at `allocaPtr` yet: a store there does nothing. -/
@[mlir_frame]
theorem GlobalState.WF.storeAt_allocaPtr {s : GlobalState} (h : s.WF) (hp : p.id = s.allocaPtr.id) :
    s.mem.storeAt p x = s.mem := by
  have : s.mem[p.id]? = none := by
    rw [MemoryState.getElem?_eq]
    apply Std.ExtHashMap.getElem?_eq_none
    intro hm
    have := h _ hm
    simp [hp, GlobalState.allocaPtr] at this
  simp [MemoryState.storeAt, this]

@[simp]
theorem GlobalState.alloca_alloc {s : GlobalState} :
    (s.alloca n).alloc = ⟨s.alloc.nextFreeBlock + 1⟩ :=
  rfl

@[simp]
theorem GlobalState.allocaPtr_id_id {s : GlobalState} : s.allocaPtr.id.id = s.alloc.nextFreeBlock :=
  rfl

@[simp]
theorem GlobalState.allocaPtr_offset {s : GlobalState} : s.allocaPtr.offset = 0 :=
  rfl

/-- A store keeps every block and its length. -/
@[simp]
theorem Fits.storeAt_iff {m : MemoryState} {x : BitVec v} :
    Fits (m.storeAt q x) p w ↔ Fits m p w := by
  unfold Fits MemoryState.storeAt
  split
  · rename_i blk hblk
    simp only [MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert]
    split
    · rename_i h
      have : q.id = p.id := by simpa using h
      rw [MemoryState.getElem?_eq] at hblk
      rw [← this, hblk]
      simp [MemoryBlock.lengthInBits]
    · rfl
  · rfl

/-- The new block holds `8 * n` bits from its start. -/
@[simp]
theorem Fits.alloca_allocaPtr_add {s : GlobalState} :
    Fits (s.alloca n).mem (s.allocaPtr.add off) w ↔ off.toNat * 8 + w ≤ 8 * n := by
  simp [Fits, GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq, Pointer.add,
    Pointer.offsetInBits, MemoryBlock.lengthInBits]
  omega

@[simp]
theorem Fits.alloca_allocaPtr {s : GlobalState} :
    Fits (s.alloca n).mem s.allocaPtr w ↔ w ≤ 8 * n := by
  simp [Fits, GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq,
    Pointer.offsetInBits, MemoryBlock.lengthInBits]

end Theorems

end

end LeanMLIR.RIR
