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

/-- Add a block of `bytes` zero bytes under `b`, holding `x` from its start: an `alloca` stored
into at once. -/
def MemoryState.addBlock (m : MemoryState) (b : BlockId) (bytes : Nat) {w : Nat} (x : BitVec w) :
    MemoryState :=
  ⟨m.mem.insert b ⟨bytes, spliceBits 0 0 x⟩⟩

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

/-- A narrower read at a known read's start: its low bits. -/
theorem MemoryState.readAt_of_readAt_le {m : MemoryState} {p : Pointer} {x : BitVec v}
    (hw : w ≤ v) (h : m.readAt p v = x) : m.readAt p w = x.setWidth w := by
  subst h
  unfold MemoryState.readAt
  split
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi, show i < v by omega]
  · simp

/-- A read over a store inside it: the bits read before, with the stored ones spliced in. -/
@[mlir_read]
theorem MemoryState.readAt_add_storeAt {off : BitVec 64} (hfits : Fits m p v)
    (hov : ¬p.offset.uaddOverflow off) (_hw : off.toNat * 8 + w ≤ v) (x : BitVec w) :
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

/-- A store keeps the set of blocks. -/
theorem MemoryState.mem_storeAt {m : MemoryState} : k ∈ (m.storeAt p x).mem ↔ k ∈ m.mem := by
  unfold MemoryState.storeAt
  split
  · rename_i blk hblk
    rw [MemoryState.getElem?_eq] at hblk
    show k ∈ m.mem.insert _ _ ↔ _
    rw [Std.ExtHashMap.mem_insert]
    constructor
    · rintro (hk | hk)
      · have : p.id = k := by simpa using hk
        subst this
        exact
          Std.ExtHashMap.mem_iff_isSome_getElem?.2
            (by
              rw [hblk]; rfl)
      · exact hk
    · exact .inr
  · exact Iff.rfl

/-- A store keeps the set of blocks, so `WF` does not depend on it. -/
@[simp, mlir_mem]
theorem GlobalState.WF_storeAt {s : GlobalState} :
    ({ s with mem := m.storeAt p x } : GlobalState).WF ↔
      ({ s with mem := m } : GlobalState).WF := by
  constructor
  · rintro ⟨hb, hp, hn⟩
    exact
      ⟨fun k hk => hb k (MemoryState.mem_storeAt.2 hk), hp, fun h =>
        hn (MemoryState.mem_storeAt.2 h)⟩
  · rintro ⟨hb, hp, hn⟩
    exact
      ⟨fun k hk => hb k (MemoryState.mem_storeAt.1 hk), hp, fun h =>
        hn (MemoryState.mem_storeAt.1 h)⟩

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.storeAt {s : GlobalState} (h : s.WF) :
    { s with mem := s.mem.storeAt p x }.WF :=
  GlobalState.WF_storeAt.2 h

@[mlir_mem]
theorem GlobalState.eraseFrom_self {s : GlobalState} (hs : s.WF) :
    { s with mem := s.mem.eraseFrom s.alloc.nextFreeBlock } = s := by
  ext : 2 <;> dsimp
  rw [MemoryState.eraseFrom]
  dsimp
  rw [Std.ExtHashMap.filter_eq_self_iff]
  intro k hk
  simp
  exact hs.bound k hk

/-! ### `alloca` and frames -/

/-- A block in memory has an id below the counter. -/
theorem GlobalState.WF.lt {s : GlobalState} (h : s.WF) (hq : q ∈ s.mem.mem) :
    q.id < s.alloc.nextFreeBlock :=
  h.bound q hq

theorem Fits.mem (h : Fits m p w) : p.id ∈ m.mem := by
  obtain ⟨b, hb, _⟩ := h
  rw [MemoryState.getElem?_eq] at hb
  exact
    Std.ExtHashMap.mem_iff_isSome_getElem?.2
      (by
        rw [hb]; rfl)

/-- A pointer into memory of a `WF` state is not null. -/
theorem GlobalState.WF.ne_null_of_fits {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w) :
    q.id ≠ Pointer.null.id := by
  intro heq
  have := h.mem
  rw [heq] at this
  exact hwf.null this

/-- A pointer into memory is not the next `alloca`'s. -/
theorem GlobalState.ne_allocaPtr_of_fits {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w) :
    q.id ≠ s.allocaPtr.id := by
  intro heq
  have := hwf.lt h.mem
  simp [heq, GlobalState.allocaPtr] at this

/-- Advancing the block counter keeps a state well-formed: a callee's frames, freed again. -/
@[mlir_transport]
theorem GlobalState.WF.add_blocks {s : GlobalState} (h : s.WF) :
    (⟨⟨s.alloc.nextFreeBlock + k⟩, s.mem⟩ : GlobalState).WF
    where
  bound b hb := by
    have := h.bound b hb
    dsimp
    omega
  pos := by
    have := h.pos
    dsimp
    omega
  null := h.null

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.alloca {s : GlobalState} (h : s.WF) : (s.alloca n).WF where
  bound k hk := by
    simp only [GlobalState.alloca, Std.ExtHashMap.mem_insert] at hk ⊢
    rcases hk with hk | hk
    · have : (⟨s.alloc.nextFreeBlock⟩ : BlockId) = k := by simpa using hk
      subst this; simp
    · have := h.bound k hk; omega
  pos := by simp [GlobalState.alloca]
  null := by
    simp only [GlobalState.alloca, Std.ExtHashMap.mem_insert, not_or]
    have := h.pos
    exact
      ⟨by
        simp; omega, h.null⟩

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

/-- An `alloca`'s block holds its `8 * n` bits. -/
@[mlir_fresh]
theorem Fits.allocaPtr_self {n : Nat} {s : GlobalState} :
    Fits (s.alloca n).mem s.allocaPtr (8 * n) :=
  Fits.allocaPtr (Nat.le_refl _)

@[mlir_read]
theorem MemoryState.readAt_alloca {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w') :
    (s.alloca n).mem.readAt q w = s.mem.readAt q w := by
  simp only [MemoryState.readAt,
    GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_fits hwf h)]

/-- `readAt_alloca` with the read's own width fitting: found among `Fits` conjuncts and wider
facts, which `readAt_alloca`'s open width never matches. -/
@[mlir_read]
theorem MemoryState.readAt_alloca_of_fits {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w) :
    (s.alloca n).mem.readAt q w = s.mem.readAt q w :=
  MemoryState.readAt_alloca hwf h

/-- Erasing a frame commutes with a store: a store into the frame is lost either way. -/
@[mlir_frame, mlir_erase]
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

@[mlir_frame, mlir_erase]
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
@[mlir_frame, mlir_erase]
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
@[mlir_frame, mlir_erase]
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
    have := h.bound _ hm
    simp [hp, GlobalState.allocaPtr] at this
  simp [MemoryState.storeAt, this]

/-! ### `addBlock`: an `alloca` stored into at once, as `addressof` does -/

/-- An `alloca` stored into from its start: the block added with the bits. -/
theorem GlobalState.alloca_storeAt_allocaPtr {s : GlobalState} {x : BitVec w} :
    (s.alloca n).mem.storeAt s.allocaPtr x = s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x := by
  simp only [MemoryState.storeAt, GlobalState.alloca, GlobalState.allocaPtr,
    MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert_self, MemoryState.addBlock,
    Pointer.offsetInBits]
  congr 1
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_insert]
  split <;> simp

/-- A new block keeps what fits. -/
@[mlir_transport]
theorem Fits.addBlock {s : GlobalState} {x : BitVec v} (hwf : s.WF) (h : Fits s.mem q w) :
    Fits (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x) q w := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact (Fits.alloca hwf h).storeAt

/-- A new block keeps the state `WF`. -/
@[mlir_transport]
theorem GlobalState.WF.addBlock {s : GlobalState} {x : BitVec v} (h : s.WF) :
    ({ alloc := ⟨s.alloc.nextFreeBlock + 1⟩, mem := s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x } :
        GlobalState).WF := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact GlobalState.WF.storeAt (s := s.alloca n) h.alloca

/-- A new block holds its `8 * n` bits. -/
@[mlir_fresh]
theorem Fits.addBlock_allocaPtr {n : Nat} {s : GlobalState} {v : Nat} {x : BitVec v} :
    Fits (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x) s.allocaPtr (8 * n) := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact (Fits.allocaPtr (Nat.le_refl _)).storeAt

/-- A new block reads back its bits. -/
@[mlir_read]
theorem MemoryState.readAt_addBlock_allocaPtr {w n : Nat} {s : GlobalState} {x : BitVec w}
    (hw : w ≤ 8 * n) : (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x).readAt s.allocaPtr w = x := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact MemoryState.readAt_storeAt_self (Fits.allocaPtr hw) x

/-- A read of a block that fits before a new one: the read before it. -/
@[mlir_read]
theorem MemoryState.readAt_addBlock {s : GlobalState} {x : BitVec v} (hwf : s.WF)
    (h : Fits s.mem q w') :
    (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x).readAt q w = s.mem.readAt q w := by
  have hne := GlobalState.ne_allocaPtr_of_fits hwf h
  have hget : (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x)[q.id]? = s.mem[q.id]? := by
    simp only [MemoryState.addBlock, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert]
    split
    · rename_i heq
      exact absurd (by simpa [GlobalState.allocaPtr] using (beq_iff_eq.mp heq).symm) hne
    · rfl
  unfold MemoryState.readAt
  rw [hget]

/-- A read outside a new block: the read before it. For a block below others added since the
state (a second global's), where `readAt_addBlock` does not match. -/
@[mlir_read]
theorem MemoryState.readAt_addBlock_of_id_ne {m : MemoryState} {b : BlockId} {x : BitVec v}
    (h : q.id ≠ b) : (m.addBlock b n x).readAt q w = m.readAt q w := by
  have hget : (m.addBlock b n x)[q.id]? = m[q.id]? := by
    simp only [MemoryState.addBlock, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert]
    split
    · rename_i heq
      exact absurd (beq_iff_eq.mp heq).symm h
    · rfl
  unfold MemoryState.readAt
  rw [hget]

/-- A block at or above `n` is gone once the frame from `n` is erased. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.eraseFrom_addBlock_of_le {m : MemoryState} {b : BlockId} {x : BitVec v}
    (h : n ≤ b.id) : (m.addBlock b bytes x).eraseFrom n = m.eraseFrom n := by
  simp only [MemoryState.addBlock, MemoryState.eraseFrom, MemoryState.mk.injEq]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_insert]
  split
  · rename_i h'; simp at h'; subst h'; simp [show ¬b.id < n by omega]
  · rfl

/-- `s.allocaPtr` after `k` `alloca`s: the `k`-th block allocated after `s`, from its start. -/
def GlobalState.slot (s : GlobalState) (k : Nat) : Pointer :=
  ⟨⟨s.alloc.nextFreeBlock + k⟩, 0#64⟩

theorem GlobalState.allocaPtr_eq_slot {s : GlobalState} : s.allocaPtr = s.slot 0 :=
  rfl

theorem GlobalState.alloca_slot {s : GlobalState} : (s.alloca n).slot k = s.slot (1 + k) := by
  simp only [GlobalState.slot, GlobalState.alloca, Nat.add_assoc]

/-- The slots of a state literal whose counter is `s`'s after `j` blocks: `s`'s. -/
theorem GlobalState.mk_slot {s : GlobalState} {m : MemoryState} :
    ({ alloc := ⟨s.alloc.nextFreeBlock + j⟩, mem := m } : GlobalState).slot k = s.slot (j + k) := by
  simp only [GlobalState.slot, Nat.add_assoc]

@[simp]
theorem GlobalState.slot_id_id {s : GlobalState} : (s.slot k).id.id = s.alloc.nextFreeBlock + k :=
  rfl

@[simp]
theorem GlobalState.slot_offset {s : GlobalState} : (s.slot k).offset = 0 :=
  rfl

/-- One state's slots at distinct indices are distinct blocks. -/
theorem GlobalState.slot_id_ne {s : GlobalState} {i j : Nat} (h : i ≠ j) :
    (s.slot i).id ≠ (s.slot j).id := by simp [GlobalState.slot, h]

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
