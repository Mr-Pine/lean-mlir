module

public import MLIR.Semantics.Effectful.Memory
public import MLIR.Memory.Range
public import MLIR.Semantics.Effectful.Memory.Bits
public import MLIR.Semantics.Effectful.Memory.Fits
public import MLIR.SimpSets
import Std.Data.ExtHashMap.Lemmas

namespace MLIR

open Memory

@[expose] public section

/-- `m` with block `i` changed by `f`, if there is one. -/
def MemoryState.modifyBlock (m : MemoryState) (i : BlockId) (f : MemoryBlock → MemoryBlock) :
    MemoryState :=
  { m with mem := m.mem.modify i f }

/-- Store bits `b` at a pointer, defined where `d` is set. If the pointer does not reference a
block, this is a no-op. -/
def MemoryState.storeDef (m : MemoryState) (p : Pointer) {w : Nat} (b d : BitVec w) : MemoryState :=
  m.modifyBlock p.id fun blk =>
    { blk with
      bytes := spliceBits blk.bytes p.offsetInBits b
      defined := spliceBits blk.defined p.offsetInBits d }

/-- Store bits at a pointer, all defined. If the pointer does not reference a block, this is a
no-op. -/
def MemoryState.storeAt (m : MemoryState) (p : Pointer) {w : Nat} (b : BitVec w) : MemoryState :=
  m.storeDef p b (BitVec.allOnes w)

/-- Read bits at a pointer. Returns `0#w` if there is no block for the pointer. -/
def MemoryState.readAt (m : MemoryState) (p : Pointer) (w : Nat) : BitVec w :=
  match m[p.id]? with
  | some block => block.bytes.extractLsb' p.offsetInBits _
  | _ => 0

/-- Which bits at a pointer are defined. Returns `0#w` if there is no block for the pointer. -/
def MemoryState.definedAt (m : MemoryState) (p : Pointer) (w : Nat) : BitVec w :=
  match m[p.id]? with
  | some block => block.defined.extractLsb' p.offsetInBits _
  | _ => 0

/-- `p`'s object live (`live`) or dead, its bits undefined either way. -/
def MemoryState.setLifetime (m : MemoryState) (p : Pointer) (live : Bool) : MemoryState :=
  m.modifyBlock p.id fun blk =>
    { blk with
      defined := 0, live }

/-- `llvm.lifetime.start`: `p`'s object becomes live, its bits undefined. -/
def MemoryState.lifetimeStart (m : MemoryState) (p : Pointer) : MemoryState :=
  m.setLifetime p true

/-- `llvm.lifetime.end`: `p`'s object becomes dead. -/
def MemoryState.lifetimeEnd (m : MemoryState) (p : Pointer) : MemoryState :=
  m.setLifetime p false

/-- The pointer the next `alloca` returns: offset 0 in the next free block. -/
def GlobalState.allocaPtr (s : GlobalState) : Pointer :=
  ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩

/-- Allocate a block of `bytes` undefined bytes at `allocaPtr`, and bump the counter; `dead` until
a `lifetimeStart`. -/
def GlobalState.alloca (s : GlobalState) (bytes : Nat) (dead : Bool := false) : GlobalState :=
  { alloc := ⟨s.alloc.nextFreeBlock + 1⟩,
    mem := { s.mem with mem := s.mem.mem.insert ⟨s.alloc.nextFreeBlock⟩ ⟨bytes, 0, 0, !dead⟩ } }

/-- Add a live block of `bytes` bytes under `b`, holding `x` from its start, the rest undefined: an
`alloca` stored into at once. -/
def MemoryState.addBlock (m : MemoryState) (b : BlockId) (bytes : Nat) {w : Nat} (x : BitVec w) :
    MemoryState :=
  { m with
    mem := m.mem.insert b ⟨bytes, spliceBits 0 0 x, spliceBits 0 0 (BitVec.allOnes w), true⟩ }

/-- Remove every block with id `n` or above: a returning callee's frame. -/
def MemoryState.eraseFrom (m : MemoryState) (n : Nat) : MemoryState :=
  { m with mem := m.mem.filter fun id _ => id.id < n }

section Theorems

/-! ### The unspecified choices: kept by every write -/

@[simp, mlir_mem, mlir_state]
theorem MemoryState.unspec_storeDef {m : MemoryState} {b d : BitVec w} :
    (m.storeDef p b d).unspec = m.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.unspec_storeAt {m : MemoryState} {b : BitVec w} :
    (m.storeAt p b).unspec = m.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.unspec_lifetimeStart {m : MemoryState} :
    (m.lifetimeStart p).unspec = m.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.unspec_lifetimeEnd {m : MemoryState} : (m.lifetimeEnd p).unspec = m.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.unspec_addBlock {m : MemoryState} {x : BitVec w} :
    (m.addBlock b n x).unspec = m.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.unspec_eraseFrom {m : MemoryState} : (m.eraseFrom n).unspec = m.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem GlobalState.unspec_alloca {s : GlobalState} : (s.alloca n d).mem.unspec = s.mem.unspec :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.addr_storeDef {m : MemoryState} {b d : BitVec w} :
    (m.storeDef p b d).addr = m.addr :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.addr_storeAt {m : MemoryState} {b : BitVec w} : (m.storeAt p b).addr = m.addr :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.addr_lifetimeStart {m : MemoryState} : (m.lifetimeStart p).addr = m.addr :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.addr_lifetimeEnd {m : MemoryState} : (m.lifetimeEnd p).addr = m.addr :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.addr_addBlock {m : MemoryState} {x : BitVec w} :
    (m.addBlock b n x).addr = m.addr :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem MemoryState.addr_eraseFrom {m : MemoryState} : (m.eraseFrom n).addr = m.addr :=
  rfl

@[simp, mlir_mem, mlir_state]
theorem GlobalState.addr_alloca {s : GlobalState} : (s.alloca n d).mem.addr = s.mem.addr :=
  rfl

/-! ### Changing one block -/

theorem MemoryState.getElem?_modifyBlock {m : MemoryState} :
    (m.modifyBlock i f)[j]? = if i = j then m[i]?.map f else m[j]? := by
  simp only [modifyBlock, getElem?_eq, Std.ExtHashMap.getElem?_modify, beq_iff_eq]

theorem MemoryState.getElem?_modifyBlock_self {m : MemoryState} :
    (m.modifyBlock i f)[i]? = m[i]?.map f := by simp [getElem?_modifyBlock]

theorem MemoryState.getElem?_modifyBlock_ne {m : MemoryState} (h : j ≠ i) :
    (m.modifyBlock i f)[j]? = m[j]? := by simp [getElem?_modifyBlock, Ne.symm h]

theorem MemoryState.mem_modifyBlock {m : MemoryState} : k ∈ (m.modifyBlock i f).mem ↔ k ∈ m.mem :=
  Std.ExtHashMap.mem_modify

theorem GlobalState.WF_modifyBlock {s : GlobalState} :
    ({ s with mem := m.modifyBlock i f } : GlobalState).WF ↔
      ({ s with mem := m } : GlobalState).WF := by
  constructor
  · rintro ⟨hb, hp, hn⟩
    exact
      ⟨fun k hk => hb k (MemoryState.mem_modifyBlock.2 hk), hp, fun h =>
        hn (MemoryState.mem_modifyBlock.2 h)⟩
  · rintro ⟨hb, hp, hn⟩
    exact
      ⟨fun k hk => hb k (MemoryState.mem_modifyBlock.1 hk), hp, fun h =>
        hn (MemoryState.mem_modifyBlock.1 h)⟩

theorem MemoryState.eraseFrom_modifyBlock {m : MemoryState} :
    (m.modifyBlock i f).eraseFrom n = (m.eraseFrom n).modifyBlock i f := by
  simp only [eraseFrom, modifyBlock, MemoryState.mk.injEq, and_true]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_modify, beq_iff_eq]
  split
  · rename_i h; subst h
    cases m.mem[i]? with
    | none => rfl
    | some _ =>
      simp only [Option.map_some, Option.filter_some]; split <;> rfl
  · rfl

theorem MemoryState.modifyBlock_eraseFrom_of_le {m : MemoryState} (h : n ≤ i.id) :
    (m.eraseFrom n).modifyBlock i f = m.eraseFrom n := by
  simp only [eraseFrom, modifyBlock, MemoryState.mk.injEq, and_true]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_modify, beq_iff_eq]
  split
  · rename_i h'; subst h'
    cases m.mem[i]? with
    | none => rfl
    | some _ => simp [Option.filter_some, show ¬i.id < n by omega]
  · rfl

/-! ### `storeDef`, `storeAt` -/

theorem MemoryState.storeAt_eq_storeDef {m : MemoryState} {x : BitVec w} :
    m.storeAt p x = m.storeDef p x (BitVec.allOnes w) :=
  rfl

theorem MemoryState.getElem?_storeDef_self {m : MemoryState} (h : m[p.id]? = some blk) :
    (m.storeDef p x d)[p.id]? =
      some
        { blk with
          bytes := spliceBits blk.bytes p.offsetInBits x
          defined := spliceBits blk.defined p.offsetInBits d } := by
  simp [storeDef, getElem?_modifyBlock_self, h]

/-- The an existing block is overwritten with `storeAt` -/
@[mlir_mem]
theorem MemoryState.getElem?_storeAt_self {m : MemoryState} {x : BitVec w}
    (h : m[p.id]? = some blk) :
    (m.storeAt p x)[p.id]? =
      some
        { blk with
          bytes := spliceBits blk.bytes p.offsetInBits x
          defined := spliceBits blk.defined p.offsetInBits (BitVec.allOnes w) } :=
  getElem?_storeDef_self h

theorem MemoryState.getElem?_storeDef_ne {m : MemoryState} {p q : Pointer} (hptr : q.id ≠ p.id) :
    (m.storeDef p x d)[q.id]? = m[q.id]? :=
  getElem?_modifyBlock_ne hptr

/-- Other blocks are not modified by `storeAt` -/
@[mlir_mem]
theorem MemoryState.getElem?_storeAt_ne {m : MemoryState} {p q : Pointer} (hptr : q.id ≠ p.id) :
    (m.storeAt p x)[q.id]? = m[q.id]? :=
  getElem?_storeDef_ne hptr

theorem MemoryState.getElem?_storeDef_isSome {m : MemoryState} {i : BlockId} :
    ((m.storeDef p x d)[i]?).isSome = (m[i]?).isSome := by
  simp only [storeDef, getElem?_modifyBlock]
  split
  · rename_i h; subst h; simp
  · rfl

/-- `storeAt` does not change whether an id is allocated or not. -/
@[mlir_mem]
theorem MemoryState.getElem?_storeAt_isSome {m : MemoryState} {i : BlockId} :
    ((m.storeAt p x)[i]?).isSome = (m[i]?).isSome :=
  getElem?_storeDef_isSome

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_storeDef_self (hfits : InBounds m p w) (x d : BitVec w) :
    (m.storeDef p x d).readAt p w = x := by
  obtain ⟨blk, hblk, hsz⟩ := hfits
  unfold MemoryBlock.lengthInBits at hsz
  simp [readAt, getElem?_storeDef_self hblk, extractLsb'_spliceBits_self, hsz]

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_storeAt_self (hfits : InBounds m p w) (x : BitVec w) :
    (m.storeAt p x).readAt p w = x :=
  readAt_storeDef_self hfits x _

theorem MemoryState.definedAt_storeDef_self (hfits : InBounds m p w) (x d : BitVec w) :
    (m.storeDef p x d).definedAt p w = d := by
  obtain ⟨blk, hblk, hsz⟩ := hfits
  unfold MemoryBlock.lengthInBits at hsz
  simp [definedAt, getElem?_storeDef_self hblk, extractLsb'_spliceBits_self, hsz]

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_storeDef_disjoint {v w : Nat} {m : MemoryState}
    (h : (Range.of p v).Disjoint (Range.of q w)) (x d : BitVec v) :
    (m.storeDef p x d).readAt q w = m.readAt q w := by
  simp only [readAt]
  by_cases hid : q.id = p.id
  · simp [Range.Disjoint, hid, Range.of] at h
    rw [hid]
    cases h' : m[p.id]? with
    | none =>
      have := getElem?_storeDef_isSome (m := m) (p := p) (x := x) (d := d) (i := p.id)
      rw [h'] at this
      cases h'' : (m.storeDef p x d)[p.id]? <;> simp_all
    | some blk =>
      rw [getElem?_storeDef_self h']
      exact extractLsb'_spliceBits_of_disjoint _ _ _ _ (by omega)
  · rw [getElem?_storeDef_ne hid]

@[mlir_mem, mlir_read]
theorem MemoryState.readAt_storeAt_disjoint {v w : Nat} {m : MemoryState}
    (h : (Range.of p v).Disjoint (Range.of q w)) (x : BitVec v) :
    (m.storeAt p x).readAt q w = m.readAt q w :=
  readAt_storeDef_disjoint h x _

theorem MemoryState.definedAt_storeDef_disjoint {v w : Nat} {m : MemoryState}
    (h : (Range.of p v).Disjoint (Range.of q w)) (x d : BitVec v) :
    (m.storeDef p x d).definedAt q w = m.definedAt q w := by
  simp only [definedAt]
  by_cases hid : q.id = p.id
  · simp [Range.Disjoint, hid, Range.of] at h
    rw [hid]
    cases h' : m[p.id]? with
    | none =>
      have := getElem?_storeDef_isSome (m := m) (p := p) (x := x) (d := d) (i := p.id)
      rw [h'] at this
      cases h'' : (m.storeDef p x d)[p.id]? <;> simp_all
    | some blk =>
      rw [getElem?_storeDef_self h']
      exact extractLsb'_spliceBits_of_disjoint _ _ _ _ (by omega)
  · rw [getElem?_storeDef_ne hid]

@[mlir_mem]
theorem MemoryState.readAt_storeAt_subrange (hfits : InBounds m p v) (hid : q.id = p.id)
    (hle : p.offsetInBits ≤ q.offsetInBits) (hw : (q.offsetInBits - p.offsetInBits) + w' ≤ v)
    (x : BitVec v) :
    (m.storeAt p x).readAt q w' = x.extractLsb' (q.offsetInBits - p.offsetInBits) w' := by
  obtain ⟨blk, hblk, hsz⟩ := hfits
  simp only [readAt, hid, getElem?_storeAt_self hblk]
  exact extractLsb'_spliceBits_of_subrange _ _ _ _ (by omega) hw hsz

/-- `p.add off`'s offset in bits, without overflow. -/
theorem Pointer.offsetInBits_add {p : Pointer} {off : BitVec 64}
    (hov : ¬p.offset.uaddOverflow off) :
    (p.add off).offsetInBits = p.offsetInBits + off.toNat * 8 := by
  simp only [Pointer.offsetInBits, Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hov]
  omega

theorem InBounds.add_of_le {off : BitVec 64} (hov : ¬p.offset.uaddOverflow off)
    (hw : off.toNat * 8 + w ≤ v) (h : InBounds m p v) : InBounds m (p.add off) w := by
  obtain ⟨blk, hblk, hsz⟩ := h
  exact
    ⟨blk, hblk, by
      rw [Pointer.offsetInBits_add hov]; omega⟩

theorem Room.add_of_le {off : BitVec 64} (hov : ¬p.offset.uaddOverflow off)
    (hw : off.toNat * 8 + w ≤ v) (h : Room m p v) : Room m (p.add off) w := by
  obtain ⟨blk, hblk, hl, hsz⟩ := h
  exact
    ⟨blk, hblk, hl, by
      rw [Pointer.offsetInBits_add hov]; omega⟩

/-- A range inside `p`'s fits too. -/
theorem Fits.add_of_le {off : BitVec 64} (hov : ¬p.offset.uaddOverflow off)
    (hw : off.toNat * 8 + w ≤ v) (h : Fits m p v) : Fits m (p.add off) w := by
  obtain ⟨blk, hblk, hl, hsz, hd⟩ := h
  refine
    ⟨blk, hblk, hl, by
      rw [Pointer.offsetInBits_add hov]; omega, ?_⟩
  have := congrArg (·.extractLsb' (off.toNat * 8) w) hd
  simp only [BitVec.extractLsb'_extractLsb'_add hw, BitVec.extractLsb'_allOnes hw] at this
  rw [Pointer.offsetInBits_add hov]
  exact this

/-- Two adjacent ranges that fit: their union fits. -/
@[mlir_mem]
theorem Fits.append {off : BitVec 64} (hov : ¬p.offset.uaddOverflow off) (hv : off.toNat * 8 = v)
    (hu : v + w = u) (h₁ : Fits m p v) (h₂ : Fits m (p.add off) w) : Fits m p u := by
  subst hu
  obtain ⟨blk, hblk, hl, hsz, hd⟩ := h₁
  obtain ⟨blk', hblk', _, hsz', hd'⟩ := h₂
  have hb : blk' = blk := by
    have : m[p.id]? = some blk' := hblk'
    rw [hblk] at this
    exact (Option.some.inj this).symm
  subst hb
  rw [Pointer.offsetInBits_add hov] at hsz' hd'
  refine ⟨blk', hblk, hl, by omega, ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_allOnes]
  by_cases hiv : i < v
  · have := congrArg (·.getLsbD i) hd
    simp only [BitVec.getLsbD_extractLsb', hiv, decide_true, Bool.true_and,
      BitVec.getLsbD_allOnes] at this
    exact this
  · have := congrArg (·.getLsbD (i - v)) hd'
    simp only [BitVec.getLsbD_extractLsb', show i - v < w by omega, decide_true, Bool.true_and,
      BitVec.getLsbD_allOnes] at this
    rw [← this]
    congr 1
    omega

/-- A read inside a store: the stored value's bits. -/
@[mlir_read]
theorem MemoryState.readAt_storeAt_add {off : BitVec 64} (hfits : InBounds m p v)
    (hov : ¬p.offset.uaddOverflow off) (hw : off.toNat * 8 + w ≤ v) (x : BitVec v) :
    (m.storeAt p x).readAt (p.add off) w = x.extractLsb' (off.toNat * 8) w := by
  rw [readAt_storeAt_subrange (q := p.add off) hfits rfl
      (by
        rw [Pointer.offsetInBits_add hov]; omega)
      (by
        rw [Pointer.offsetInBits_add hov]; omega)]
  rw [Pointer.offsetInBits_add hov, Nat.add_sub_cancel_left]

/-- A read inside a known read: its bits. -/
theorem MemoryState.readAt_add_of_readAt {off : BitVec 64} (hfits : InBounds m p v)
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
theorem MemoryState.readAt_of_readAt_le {m : MemoryState} {p : Pointer} {x : BitVec v} (hw : w ≤ v)
    (h : m.readAt p v = x) : m.readAt p w = x.setWidth w := by
  subst h
  unfold MemoryState.readAt
  split
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi, show i < v by omega]
  · simp

/-- A read over a store inside it: the bits read before, with the stored ones spliced in. -/
@[mlir_read]
theorem MemoryState.readAt_add_storeAt {off : BitVec 64} (hfits : InBounds m p v)
    (hov : ¬p.offset.uaddOverflow off) (_hw : off.toNat * 8 + w ≤ v) (x : BitVec w) :
    (m.storeAt (p.add off) x).readAt p v = spliceBits (m.readAt p v) (off.toNat * 8) x := by
  obtain ⟨blk, hblk, hsz⟩ := hfits
  have hs :
    (m.storeAt (p.add off) x)[p.id]? =
      some
        { blk with
          bytes := spliceBits blk.bytes (p.add off).offsetInBits x
          defined := spliceBits blk.defined (p.add off).offsetInBits (BitVec.allOnes w) } :=
    getElem?_storeAt_self (p := p.add off) hblk
  simp only [readAt, hs, hblk]
  unfold MemoryBlock.lengthInBits at hsz
  rw [Pointer.offsetInBits_add hov]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', getLsbD_spliceBits]
  grind

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

/-- The defined bits of `Fits`, read. -/
theorem MemoryState.definedAt_of_fits (h : Fits m p w) : m.definedAt p w = BitVec.allOnes w := by
  obtain ⟨blk, hblk, _, _, hd⟩ := h
  simp [definedAt, hblk, hd]

/-! #### What fits after a store -/

theorem InBounds.storeDef_iff {m : MemoryState} {x d : BitVec v} :
    InBounds (m.storeDef q x d) p w ↔ InBounds m p w := by
  unfold InBounds
  by_cases h : q.id = p.id
  · rw [← h]
    cases hb : m[q.id]? with
    | none =>
      have := MemoryState.getElem?_storeDef_isSome (m := m) (p := q) (x := x) (d := d) (i := q.id)
      rw [hb] at this
      cases h' : (m.storeDef q x d)[q.id]? <;> simp_all
    | some blk => simp [MemoryState.getElem?_storeDef_self hb, MemoryBlock.lengthInBits]
  · rw [MemoryState.getElem?_storeDef_ne (Ne.symm h)]

theorem Room.storeDef_iff {m : MemoryState} {x d : BitVec v} :
    Room (m.storeDef q x d) p w ↔ Room m p w := by
  unfold Room
  by_cases h : q.id = p.id
  · rw [← h]
    cases hb : m[q.id]? with
    | none =>
      have := MemoryState.getElem?_storeDef_isSome (m := m) (p := q) (x := x) (d := d) (i := q.id)
      rw [hb] at this
      cases h' : (m.storeDef q x d)[q.id]? <;> simp_all
    | some blk => simp [MemoryState.getElem?_storeDef_self hb, MemoryBlock.lengthInBits]
  · rw [MemoryState.getElem?_storeDef_ne (Ne.symm h)]

/-- A store keeps every block and its length. -/
@[simp]
theorem InBounds.storeAt_iff {m : MemoryState} {x : BitVec v} :
    InBounds (m.storeAt q x) p w ↔ InBounds m p w :=
  InBounds.storeDef_iff

/-- A store keeps every block, its length and lifetime. -/
@[simp]
theorem Room.storeAt_iff {m : MemoryState} {x : BitVec v} : Room (m.storeAt q x) p w ↔ Room m p w :=
  Room.storeDef_iff

@[mlir_mem, mlir_transport]
theorem InBounds.storeAt (hq : InBounds m p w) : InBounds (m.storeAt q x) p w :=
  InBounds.storeAt_iff.2 hq

@[mlir_mem, mlir_transport]
theorem Room.storeAt (hq : Room m p w) : Room (m.storeAt q x) p w :=
  Room.storeAt_iff.2 hq

@[mlir_mem, mlir_transport]
theorem InBounds.storeDef (hq : InBounds m p w) : InBounds (m.storeDef q x d) p w :=
  InBounds.storeDef_iff.2 hq

@[mlir_mem, mlir_transport]
theorem Room.storeDef (hq : Room m p w) : Room (m.storeDef q x d) p w :=
  Room.storeDef_iff.2 hq

/-- A store keeps known bits known: it defines the bits it writes. -/
@[mlir_mem, mlir_transport]
theorem Fits.storeAt (hq : Fits m p w) : Fits (m.storeAt q x) p w := by
  obtain ⟨blk, hblk, hl, hsz, hd⟩ := hq
  by_cases h : q.id = p.id
  · rw [← h] at hblk
    refine
      ⟨{ blk with
          bytes := spliceBits blk.bytes q.offsetInBits x
          defined := spliceBits blk.defined q.offsetInBits (BitVec.allOnes _) },
        by
        rw [← h]; exact MemoryState.getElem?_storeAt_self hblk, hl, hsz, ?_⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (·.getLsbD i) hd
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
      BitVec.getLsbD_allOnes] at this ⊢
    rw [getLsbD_spliceBits]
    split
    · simp only [BitVec.getLsbD_allOnes, decide_eq_true_eq]; omega
    · exact this
  · exact
      ⟨blk, by
        rw [MemoryState.getElem?_storeAt_ne (Ne.symm h)]; exact hblk, hl, hsz, hd⟩

/-- A store into a live block's room: what it stored is known. -/
@[mlir_fresh, mlir_mem]
theorem Fits.storeAt_self {m : MemoryState} {x : BitVec w} (h : Room m p w) :
    Fits (m.storeAt p x) p w := by
  obtain ⟨blk, hblk, hl, hsz⟩ := h
  unfold MemoryBlock.lengthInBits at hsz
  exact ⟨_, MemoryState.getElem?_storeAt_self hblk, hl, hsz, extractLsb'_spliceBits_self _ _ _ hsz⟩

/-- A store elsewhere keeps known bits known. -/
@[mlir_transport]
theorem Fits.storeDef_of_disjoint (hq : Fits m p w) (hd : (Range.of q v).Disjoint (Range.of p w))
    {x d : BitVec v} : Fits (m.storeDef q x d) p w := by
  obtain ⟨blk, hblk, hl, hsz, hdef⟩ := hq
  by_cases h : q.id = p.id
  · rw [← h] at hblk
    refine
      ⟨{ blk with
          bytes := spliceBits blk.bytes q.offsetInBits x
          defined := spliceBits blk.defined q.offsetInBits d },
        by
        rw [← h]; exact MemoryState.getElem?_storeDef_self hblk, hl, hsz, ?_⟩
    simp only [Range.Disjoint, Range.of, h, ne_eq, not_true_eq_false, false_or] at hd
    rw [extractLsb'_spliceBits_of_disjoint _ _ _ _ (by omega)]
    exact hdef
  · exact
      ⟨blk, by
        rw [MemoryState.getElem?_storeDef_ne (Ne.symm h)]; exact hblk, hl, hsz, hdef⟩

/-- A store keeps the set of blocks. -/
theorem MemoryState.mem_storeDef {m : MemoryState} : k ∈ (m.storeDef p x d).mem ↔ k ∈ m.mem :=
  mem_modifyBlock

/-- A store keeps the set of blocks. -/
theorem MemoryState.mem_storeAt {m : MemoryState} : k ∈ (m.storeAt p x).mem ↔ k ∈ m.mem :=
  mem_modifyBlock

/-- A store keeps the set of blocks, so `WF` does not depend on it. -/
@[simp, mlir_mem]
theorem GlobalState.WF_storeDef {s : GlobalState} :
    ({ s with mem := m.storeDef p x d } : GlobalState).WF ↔
      ({ s with mem := m } : GlobalState).WF :=
  WF_modifyBlock

/-- A store keeps the set of blocks, so `WF` does not depend on it. -/
@[simp, mlir_mem]
theorem GlobalState.WF_storeAt {s : GlobalState} :
    ({ s with mem := m.storeAt p x } : GlobalState).WF ↔ ({ s with mem := m } : GlobalState).WF :=
  WF_modifyBlock

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.storeAt {s : GlobalState} (h : s.WF) :
    { s with mem := s.mem.storeAt p x }.WF :=
  GlobalState.WF_storeAt.2 h

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.storeDef {s : GlobalState} (h : s.WF) :
    { s with mem := s.mem.storeDef p x d }.WF :=
  GlobalState.WF_storeDef.2 h

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

/-! ### Lifetimes -/

theorem MemoryState.getElem?_setLifetime_ne {m : MemoryState} {p q : Pointer} (h : q.id ≠ p.id) :
    (m.setLifetime p l)[q.id]? = m[q.id]? :=
  getElem?_modifyBlock_ne h

theorem MemoryState.readAt_setLifetime {m : MemoryState} :
    (m.setLifetime q l).readAt p w = m.readAt p w := by
  unfold readAt
  by_cases h : q.id = p.id
  · rw [← h, setLifetime, getElem?_modifyBlock_self]
    cases m[q.id]? <;> rfl
  · rw [setLifetime, getElem?_modifyBlock_ne (Ne.symm h)]

/-- A lifetime marker keeps the bits. -/
@[mlir_mem, mlir_read]
theorem MemoryState.readAt_lifetimeStart {m : MemoryState} :
    (m.lifetimeStart q).readAt p w = m.readAt p w :=
  readAt_setLifetime

/-- A lifetime marker keeps the bits. -/
@[mlir_mem, mlir_read]
theorem MemoryState.readAt_lifetimeEnd {m : MemoryState} :
    (m.lifetimeEnd q).readAt p w = m.readAt p w :=
  readAt_setLifetime

theorem InBounds.setLifetime_iff {m : MemoryState} :
    InBounds (m.setLifetime q l) p w ↔ InBounds m p w := by
  unfold InBounds
  by_cases h : q.id = p.id
  · rw [← h, MemoryState.setLifetime, MemoryState.getElem?_modifyBlock_self]
    cases m[q.id]? <;> simp [MemoryBlock.lengthInBits]
  · rw [MemoryState.setLifetime, MemoryState.getElem?_modifyBlock_ne (Ne.symm h)]

@[simp]
theorem InBounds.lifetimeStart_iff {m : MemoryState} :
    InBounds (m.lifetimeStart q) p w ↔ InBounds m p w :=
  InBounds.setLifetime_iff

@[simp]
theorem InBounds.lifetimeEnd_iff {m : MemoryState} :
    InBounds (m.lifetimeEnd q) p w ↔ InBounds m p w :=
  InBounds.setLifetime_iff

@[mlir_mem, mlir_transport]
theorem InBounds.lifetimeStart (h : InBounds m p w) : InBounds (m.lifetimeStart q) p w :=
  InBounds.lifetimeStart_iff.2 h

@[mlir_mem, mlir_transport]
theorem InBounds.lifetimeEnd (h : InBounds m p w) : InBounds (m.lifetimeEnd q) p w :=
  InBounds.lifetimeEnd_iff.2 h

@[mlir_mem, mlir_transport]
theorem Room.lifetimeStart (h : Room m p w) (hne : p.id ≠ q.id) : Room (m.lifetimeStart q) p w := by
  obtain ⟨blk, hblk, hl, hsz⟩ := h
  exact
    ⟨blk, by
      rw [MemoryState.lifetimeStart, MemoryState.getElem?_setLifetime_ne hne]; exact hblk, hl, hsz⟩

@[mlir_mem, mlir_transport]
theorem Room.lifetimeEnd (h : Room m p w) (hne : p.id ≠ q.id) : Room (m.lifetimeEnd q) p w := by
  obtain ⟨blk, hblk, hl, hsz⟩ := h
  exact
    ⟨blk, by
      rw [MemoryState.lifetimeEnd, MemoryState.getElem?_setLifetime_ne hne]; exact hblk, hl, hsz⟩

@[mlir_mem, mlir_transport]
theorem Fits.lifetimeStart (h : Fits m p w) (hne : p.id ≠ q.id) : Fits (m.lifetimeStart q) p w := by
  obtain ⟨blk, hblk, hl, hsz, hd⟩ := h
  exact
    ⟨blk, by
      rw [MemoryState.lifetimeStart, MemoryState.getElem?_setLifetime_ne hne]; exact hblk, hl, hsz,
      hd⟩

@[mlir_mem, mlir_transport]
theorem Fits.lifetimeEnd (h : Fits m p w) (hne : p.id ≠ q.id) : Fits (m.lifetimeEnd q) p w := by
  obtain ⟨blk, hblk, hl, hsz, hd⟩ := h
  exact
    ⟨blk, by
      rw [MemoryState.lifetimeEnd, MemoryState.getElem?_setLifetime_ne hne]; exact hblk, hl, hsz,
      hd⟩

/-- After `lifetimeStart`, its object is live: room in its bounds. -/
@[mlir_fresh, mlir_mem]
theorem Room.lifetimeStart_self (h : InBounds m p w) : Room (m.lifetimeStart p) p w := by
  obtain ⟨blk, hblk, hsz⟩ := h
  refine
    ⟨{ blk with
        defined := 0, live := true },
      ?_, rfl, hsz⟩
  simp [MemoryState.lifetimeStart, MemoryState.setLifetime, MemoryState.getElem?_modifyBlock_self,
    hblk]

/-- A lifetime marker keeps the set of blocks, so `WF` does not depend on it. -/
@[simp, mlir_mem]
theorem GlobalState.WF_lifetimeStart {s : GlobalState} :
    ({ s with mem := m.lifetimeStart p } : GlobalState).WF ↔
      ({ s with mem := m } : GlobalState).WF :=
  WF_modifyBlock

/-- A lifetime marker keeps the set of blocks, so `WF` does not depend on it. -/
@[simp, mlir_mem]
theorem GlobalState.WF_lifetimeEnd {s : GlobalState} :
    ({ s with mem := m.lifetimeEnd p } : GlobalState).WF ↔ ({ s with mem := m } : GlobalState).WF :=
  WF_modifyBlock

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.lifetimeStart {s : GlobalState} (h : s.WF) :
    { s with mem := s.mem.lifetimeStart p }.WF :=
  GlobalState.WF_lifetimeStart.2 h

@[mlir_mem, mlir_transport]
theorem GlobalState.WF.lifetimeEnd {s : GlobalState} (h : s.WF) :
    { s with mem := s.mem.lifetimeEnd p }.WF :=
  GlobalState.WF_lifetimeEnd.2 h

/-- `WF.lifetimeStart` for a state written as a constructor, which unifies first-order. -/
@[mlir_transport]
theorem GlobalState.WF.lifetimeStart_mk {a : AllocState} {m : MemoryState}
    (h : (⟨a, m⟩ : GlobalState).WF) : (⟨a, m.lifetimeStart p⟩ : GlobalState).WF :=
  GlobalState.WF.lifetimeStart (s := ⟨a, m⟩) h

/-- `WF.lifetimeEnd` for a state written as a constructor, which unifies first-order. -/
@[mlir_transport]
theorem GlobalState.WF.lifetimeEnd_mk {a : AllocState} {m : MemoryState}
    (h : (⟨a, m⟩ : GlobalState).WF) : (⟨a, m.lifetimeEnd p⟩ : GlobalState).WF :=
  GlobalState.WF.lifetimeEnd (s := ⟨a, m⟩) h

/-- Erasing a frame commutes with a lifetime marker. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.eraseFrom_lifetimeStart {m : MemoryState} :
    (m.lifetimeStart p).eraseFrom n = (m.eraseFrom n).lifetimeStart p :=
  eraseFrom_modifyBlock

/-- Erasing a frame commutes with a lifetime marker. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.eraseFrom_lifetimeEnd {m : MemoryState} :
    (m.lifetimeEnd p).eraseFrom n = (m.eraseFrom n).lifetimeEnd p :=
  eraseFrom_modifyBlock

/-- A lifetime marker on an erased block does nothing. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.lifetimeStart_eraseFrom_of_le {m : MemoryState} (h : n ≤ p.id.id) :
    (m.eraseFrom n).lifetimeStart p = m.eraseFrom n :=
  modifyBlock_eraseFrom_of_le h

/-- A lifetime marker on an erased block does nothing. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.lifetimeEnd_eraseFrom_of_le {m : MemoryState} (h : n ≤ p.id.id) :
    (m.eraseFrom n).lifetimeEnd p = m.eraseFrom n :=
  modifyBlock_eraseFrom_of_le h

/-- A lifetime marker in the frame, dropped before the erase moves past it, as
`eraseFrom_storeAt_of_le`. -/
@[mlir_erase high]
theorem MemoryState.eraseFrom_lifetimeStart_of_le {m : MemoryState} (h : n ≤ p.id.id) :
    (m.lifetimeStart p).eraseFrom n = m.eraseFrom n := by
  rw [eraseFrom_lifetimeStart, lifetimeStart_eraseFrom_of_le h]

/-- A lifetime marker in the frame, dropped before the erase moves past it, as
`eraseFrom_storeAt_of_le`. -/
@[mlir_erase high]
theorem MemoryState.eraseFrom_lifetimeEnd_of_le {m : MemoryState} (h : n ≤ p.id.id) :
    (m.lifetimeEnd p).eraseFrom n = m.eraseFrom n := by
  rw [eraseFrom_lifetimeEnd, lifetimeEnd_eraseFrom_of_le h]

/-! ### `alloca` and frames -/

/-- A block in memory has an id below the counter. -/
theorem GlobalState.WF.lt {s : GlobalState} (h : s.WF) (hq : q ∈ s.mem.mem) :
    q.id < s.alloc.nextFreeBlock :=
  h.bound q hq

theorem InBounds.mem (h : InBounds m p w) : p.id ∈ m.mem := by
  obtain ⟨b, hb, _⟩ := h
  rw [MemoryState.getElem?_eq] at hb
  exact
    Std.ExtHashMap.mem_iff_isSome_getElem?.2
      (by
        rw [hb]; rfl)

theorem Room.mem (h : Room m p w) : p.id ∈ m.mem :=
  h.inBounds.mem

theorem Fits.mem (h : Fits m p w) : p.id ∈ m.mem :=
  h.inBounds.mem

/-- A pointer into memory of a `WF` state is not null. -/
theorem GlobalState.WF.ne_null_of_inBounds {s : GlobalState} (hwf : s.WF) (h : InBounds s.mem q w) :
    q.id ≠ Pointer.null.id := by
  intro heq
  have := h.mem
  rw [heq] at this
  exact hwf.null this

/-- A pointer into memory of a `WF` state is not null. -/
theorem GlobalState.WF.ne_null_of_fits {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w) :
    q.id ≠ Pointer.null.id :=
  hwf.ne_null_of_inBounds h.inBounds

/-- A pointer into memory is not the next `alloca`'s. -/
theorem GlobalState.ne_allocaPtr_of_inBounds {s : GlobalState} (hwf : s.WF)
    (h : InBounds s.mem q w) : q.id ≠ s.allocaPtr.id := by
  intro heq
  have := hwf.lt h.mem
  simp [heq, GlobalState.allocaPtr] at this

/-- A pointer into memory is not the next `alloca`'s. -/
theorem GlobalState.ne_allocaPtr_of_room {s : GlobalState} (hwf : s.WF) (h : Room s.mem q w) :
    q.id ≠ s.allocaPtr.id :=
  ne_allocaPtr_of_inBounds hwf h.inBounds

/-- A pointer into memory is not the next `alloca`'s. -/
theorem GlobalState.ne_allocaPtr_of_fits {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w) :
    q.id ≠ s.allocaPtr.id :=
  ne_allocaPtr_of_inBounds hwf h.inBounds

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
theorem GlobalState.WF.alloca {s : GlobalState} (h : s.WF) : (s.alloca n d).WF where
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
    (s.alloca n d).mem[q]? = s.mem[q]? := by
  simp only [GlobalState.alloca, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert]
  split
  · rename_i h
    exact absurd (show s.allocaPtr.id = q by simpa [GlobalState.allocaPtr] using h) (Ne.symm hq)
  · rfl

@[mlir_transport]
theorem InBounds.alloca {s : GlobalState} (hwf : s.WF) (h : InBounds s.mem q w) :
    InBounds (s.alloca n d).mem q w := by
  obtain ⟨b, hb, hs⟩ := h
  refine ⟨b, ?_, hs⟩
  rw [GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_inBounds hwf ⟨b, hb, hs⟩)]
  exact hb

@[mlir_transport]
theorem Room.alloca {s : GlobalState} (hwf : s.WF) (h : Room s.mem q w) :
    Room (s.alloca n d).mem q w := by
  obtain ⟨b, hb, hl, hs⟩ := h
  refine ⟨b, ?_, hl, hs⟩
  rw [GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_inBounds hwf ⟨b, hb, hs⟩)]
  exact hb

@[mlir_transport]
theorem Fits.alloca {s : GlobalState} (hwf : s.WF) (h : Fits s.mem q w) :
    Fits (s.alloca n d).mem q w := by
  obtain ⟨b, hb, hl, hs, hd⟩ := h
  refine ⟨b, ?_, hl, hs, hd⟩
  rw [GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_inBounds hwf ⟨b, hb, hs⟩)]
  exact hb

theorem InBounds.allocaPtr {s : GlobalState} (hw : w ≤ 8 * n) :
    InBounds (s.alloca n d).mem s.allocaPtr w := by
  refine ⟨⟨n, 0, 0, !d⟩, ?_, ?_⟩
  · simp [GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
  · simp [Pointer.offsetInBits, GlobalState.allocaPtr, MemoryBlock.lengthInBits]; omega

theorem Room.allocaPtr {s : GlobalState} (hw : w ≤ 8 * n) :
    Room (s.alloca n).mem s.allocaPtr w := by
  refine ⟨⟨n, 0, 0, true⟩, ?_, rfl, ?_⟩
  · simp [GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
  · simp [Pointer.offsetInBits, GlobalState.allocaPtr, MemoryBlock.lengthInBits]; omega

/-- A live `alloca`'s block has room for its `8 * n` bits. -/
@[mlir_fresh]
theorem Room.allocaPtr_self {n : Nat} {s : GlobalState} :
    Room (s.alloca n).mem s.allocaPtr (8 * n) :=
  Room.allocaPtr (Nat.le_refl _)

/-- A dead `alloca`'s block is `8 * n` bits long. -/
@[mlir_fresh]
theorem InBounds.allocaPtr_self {n : Nat} {s : GlobalState} :
    InBounds (s.alloca n true).mem s.allocaPtr (8 * n) :=
  InBounds.allocaPtr (Nat.le_refl _)

@[mlir_read]
theorem MemoryState.readAt_alloca {s : GlobalState} (hwf : s.WF) (h : InBounds s.mem q w') :
    (s.alloca n d).mem.readAt q w = s.mem.readAt q w := by
  simp only [MemoryState.readAt,
    GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_inBounds hwf h)]

/-- `readAt_alloca` with the read's own width in bounds: found among the facts' conjuncts and wider
facts, which `readAt_alloca`'s open width never matches. -/
@[mlir_read]
theorem MemoryState.readAt_alloca_of_fits {s : GlobalState} (hwf : s.WF) (h : InBounds s.mem q w) :
    (s.alloca n d).mem.readAt q w = s.mem.readAt q w :=
  MemoryState.readAt_alloca hwf h

/-- Erasing a frame commutes with a store: a store into the frame is lost either way. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.eraseFrom_storeDef {m : MemoryState} {p : Pointer} {x d : BitVec w} :
    (m.storeDef p x d).eraseFrom n = (m.eraseFrom n).storeDef p x d :=
  eraseFrom_modifyBlock

/-- Erasing a frame commutes with a store: a store into the frame is lost either way. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.eraseFrom_storeAt {m : MemoryState} {p : Pointer} {x : BitVec w} :
    (m.storeAt p x).eraseFrom n = (m.eraseFrom n).storeAt p x :=
  eraseFrom_modifyBlock

@[mlir_frame, mlir_erase]
theorem GlobalState.eraseFrom_alloca {s : GlobalState} :
    (s.alloca b d).mem.eraseFrom s.alloc.nextFreeBlock = s.mem.eraseFrom s.alloc.nextFreeBlock := by
  simp only [GlobalState.alloca, MemoryState.eraseFrom, MemoryState.mk.injEq, and_true]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_insert]
  split
  · rename_i h; simp at h; subst h; simp
  · rfl

/-- An `alloca` at or above `n` is gone once the frame from `n` is erased. -/
@[mlir_frame, mlir_erase]
theorem GlobalState.eraseFrom_alloca_of_le {s : GlobalState} (h : n ≤ s.alloc.nextFreeBlock) :
    (s.alloca b d).mem.eraseFrom n = s.mem.eraseFrom n := by
  simp only [GlobalState.alloca, MemoryState.eraseFrom, MemoryState.mk.injEq, and_true]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_insert]
  split
  · rename_i h'; simp at h'; subst h'; simp [show ¬s.alloc.nextFreeBlock < n by omega]
  · rfl

/-- A store into an erased block does nothing. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.storeDef_eraseFrom_of_le {m : MemoryState} {p : Pointer} {x d : BitVec w}
    (h : n ≤ p.id.id) : (m.eraseFrom n).storeDef p x d = m.eraseFrom n :=
  modifyBlock_eraseFrom_of_le h

/-- A store into an erased block does nothing. -/
@[mlir_frame, mlir_erase]
theorem MemoryState.storeAt_eraseFrom_of_le {m : MemoryState} {p : Pointer} {x : BitVec w}
    (h : n ≤ p.id.id) : (m.eraseFrom n).storeAt p x = m.eraseFrom n :=
  modifyBlock_eraseFrom_of_le h

/-- A store into the frame, dropped before the erase moves past it: moved first, it stays above a
store outside the frame, where `storeAt_eraseFrom_of_le` cannot reach it. -/
@[mlir_erase high]
theorem MemoryState.eraseFrom_storeAt_of_le {m : MemoryState} {p : Pointer} {x : BitVec w}
    (h : n ≤ p.id.id) : (m.storeAt p x).eraseFrom n = m.eraseFrom n := by
  rw [eraseFrom_storeAt, storeAt_eraseFrom_of_le h]

/-- `eraseFrom_storeAt_of_le` for `storeDef`. -/
@[mlir_erase high]
theorem MemoryState.eraseFrom_storeDef_of_le {m : MemoryState} {p : Pointer} {x d : BitVec w}
    (h : n ≤ p.id.id) : (m.storeDef p x d).eraseFrom n = m.eraseFrom n := by
  rw [eraseFrom_storeDef, storeDef_eraseFrom_of_le h]

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

/-- `WF.storeDef` for a state written as a constructor, which unifies first-order. -/
@[mlir_transport]
theorem GlobalState.WF.storeDef_mk {a : AllocState} {m : MemoryState}
    (h : (⟨a, m⟩ : GlobalState).WF) : (⟨a, m.storeDef p x d⟩ : GlobalState).WF :=
  GlobalState.WF.storeDef (s := ⟨a, m⟩) h

/-- In a `WF` state there is no block at `allocaPtr` yet: a store there does nothing. -/
@[mlir_frame]
theorem GlobalState.WF.storeAt_allocaPtr {s : GlobalState} (h : s.WF) (hp : p.id = s.allocaPtr.id) :
    s.mem.storeAt p x = s.mem := by
  have : s.mem.mem[p.id]? = none := by
    apply Std.ExtHashMap.getElem?_eq_none
    intro hm
    have := h.bound _ hm
    simp [hp, GlobalState.allocaPtr] at this
  simp only [MemoryState.storeAt, MemoryState.storeDef, MemoryState.modifyBlock]
  congr 1
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_modify, beq_iff_eq]
  split
  · rename_i h'; subst h'; rw [this]; rfl
  · rfl

/-! ### `addBlock`: an `alloca` stored into at once, as `addressof` does -/

/-- An `alloca` stored into from its start: the block added with the bits. -/
theorem GlobalState.alloca_storeAt_allocaPtr {s : GlobalState} {x : BitVec w} :
    (s.alloca n).mem.storeAt s.allocaPtr x = s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x := by
  simp only [MemoryState.storeAt, MemoryState.storeDef, MemoryState.modifyBlock, GlobalState.alloca,
    GlobalState.allocaPtr, MemoryState.addBlock, Pointer.offsetInBits]
  congr 1
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_modify, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  split
  · rename_i h; subst h; simp
  · rfl

/-- A new block keeps what fits. -/
@[mlir_transport]
theorem Fits.addBlock {s : GlobalState} {x : BitVec v} (hwf : s.WF) (h : Fits s.mem q w) :
    Fits (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x) q w := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact (Fits.alloca hwf h).storeAt

/-- A new block keeps what has room. -/
@[mlir_transport]
theorem Room.addBlock {s : GlobalState} {x : BitVec v} (hwf : s.WF) (h : Room s.mem q w) :
    Room (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x) q w := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact (Room.alloca hwf h).storeAt

/-- A new block keeps what is in bounds. -/
@[mlir_transport]
theorem InBounds.addBlock {s : GlobalState} {x : BitVec v} (hwf : s.WF) (h : InBounds s.mem q w) :
    InBounds (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x) q w := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact (InBounds.alloca hwf h).storeAt

/-- A new block keeps the state `WF`. -/
@[mlir_transport]
theorem GlobalState.WF.addBlock {s : GlobalState} {x : BitVec v} (h : s.WF) :
    ({ alloc := ⟨s.alloc.nextFreeBlock + 1⟩, mem := s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x } :
        GlobalState).WF := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact GlobalState.WF.storeAt (s := s.alloca n) h.alloca

/-- A new block has room for its `8 * n` bits. -/
@[mlir_fresh]
theorem Room.addBlock_allocaPtr {n : Nat} {s : GlobalState} {v : Nat} {x : BitVec v} :
    Room (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x) s.allocaPtr (8 * n) := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact (Room.allocaPtr (Nat.le_refl _)).storeAt

/-- A new block holds its bits. -/
@[mlir_fresh]
theorem Fits.addBlock_allocaPtr {n : Nat} {s : GlobalState} {v : Nat} {x : BitVec v}
    (hw : v ≤ 8 * n) : Fits (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x) s.allocaPtr v := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact Fits.storeAt_self (Room.allocaPtr hw)

/-- A new block reads back its bits. -/
@[mlir_read]
theorem MemoryState.readAt_addBlock_allocaPtr {w n : Nat} {s : GlobalState} {x : BitVec w}
    (hw : w ≤ 8 * n) : (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x).readAt s.allocaPtr w = x := by
  rw [← GlobalState.alloca_storeAt_allocaPtr]
  exact MemoryState.readAt_storeAt_self (InBounds.allocaPtr hw) x

/-- A read of a block in bounds before a new one: the read before it. -/
@[mlir_read]
theorem MemoryState.readAt_addBlock {s : GlobalState} {x : BitVec v} (hwf : s.WF)
    (h : InBounds s.mem q w') :
    (s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n x).readAt q w = s.mem.readAt q w := by
  have hne := GlobalState.ne_allocaPtr_of_inBounds hwf h
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
  simp only [MemoryState.addBlock, MemoryState.eraseFrom, MemoryState.mk.injEq, and_true]
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

theorem GlobalState.alloca_slot {s : GlobalState} : (s.alloca n d).slot k = s.slot (1 + k) := by
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
    (s.alloca n d).alloc = ⟨s.alloc.nextFreeBlock + 1⟩ :=
  rfl

@[simp]
theorem GlobalState.allocaPtr_id_id {s : GlobalState} : s.allocaPtr.id.id = s.alloc.nextFreeBlock :=
  rfl

@[simp]
theorem GlobalState.allocaPtr_offset {s : GlobalState} : s.allocaPtr.offset = 0 :=
  rfl

/-- The new block is `8 * n` bits long from its start. -/
@[simp]
theorem InBounds.alloca_allocaPtr_add {s : GlobalState} :
    InBounds (s.alloca n d).mem (s.allocaPtr.add off) w ↔ off.toNat * 8 + w ≤ 8 * n := by
  simp [InBounds, GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq, Pointer.add,
    Pointer.offsetInBits, MemoryBlock.lengthInBits]
  omega

/-- The new live block has room for `8 * n` bits from its start. -/
@[simp]
theorem Room.alloca_allocaPtr_add {s : GlobalState} :
    Room (s.alloca n).mem (s.allocaPtr.add off) w ↔ off.toNat * 8 + w ≤ 8 * n := by
  simp [Room, GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq, Pointer.add,
    Pointer.offsetInBits, MemoryBlock.lengthInBits]
  omega

@[simp]
theorem InBounds.alloca_allocaPtr {s : GlobalState} :
    InBounds (s.alloca n d).mem s.allocaPtr w ↔ w ≤ 8 * n := by
  simp [InBounds, GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq,
    Pointer.offsetInBits, MemoryBlock.lengthInBits]

@[simp]
theorem Room.alloca_allocaPtr {s : GlobalState} :
    Room (s.alloca n).mem s.allocaPtr w ↔ w ≤ 8 * n := by
  simp [Room, GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq,
    Pointer.offsetInBits, MemoryBlock.lengthInBits]

end Theorems

end

end MLIR
