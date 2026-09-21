module

public import SSA.Projects.RIR.Semantics.Effectful.Memory
public import SSA.Projects.RIR.Memory.Range
public import SSA.Projects.RIR.Semantics.Effectful.Memory.Bits
public import SSA.Projects.RIR.Semantics.Effectful.Memory.Fits
import Std.Data.HashMap.Lemmas

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

section Theorems

/-- The an existing block is overwritten with `storeAt` -/
theorem MemoryState.getElem?_storeAt_self {m : MemoryState} (h : m[p.id]? = some blk) :
    (m.storeAt p x)[p.id]? = some { blk with bytes := spliceBits blk.bytes p.offsetInBits x } := by
  simp [storeAt, h, MemoryState.getElem?_eq]

/-- Other blocks are not modified by `storeAt` -/
theorem MemoryState.getElem?_storeAt_ne {m : MemoryState} {p q : Pointer} (hptr : q.id ≠ p.id) :
    (m.storeAt p x)[q.id]? = m[q.id]? := by
  simp [storeAt]
  cases m[p.id]? with
  | none => simp
  | some _ =>
    simp [MemoryState.getElem?_eq] at ⊢
    simp [Std.HashMap.getElem?_insert, hptr.symm]

/-- `storeAt` does not change whether an id is allocated or not. -/
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

theorem MemoryState.readAt_storeAt_self (hfits : Fits m p w) (x : BitVec w) :
    (m.storeAt p x).readAt p w = x := by
  obtain ⟨blk, hblk, hsz⟩ := hfits
  unfold MemoryBlock.lengthInBits at hsz
  simp [readAt, getElem?_storeAt_self hblk, extractLsb'_spliceBits_self, hsz]

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

theorem MemoryState.readAt_storeAt_subrange (hfits : Fits m p v) (hid : q.id = p.id)
    (hle : p.offsetInBits ≤ q.offsetInBits) (hw : (q.offsetInBits - p.offsetInBits) + w' ≤ v)
    (x : BitVec v) :
    (m.storeAt p x).readAt q w' = x.extractLsb' (q.offsetInBits - p.offsetInBits) w' := by
  obtain ⟨blk, hblk, hsz⟩ := hfits
  simp [readAt, hid, getElem?_storeAt_self hblk]
  exact extractLsb'_spliceBits_of_subrange _ _ _ _ (by omega) hw hsz

theorem Fits.storeAt (hq : Fits m p w) : Fits (m.storeAt q x) p w := by
  unfold Fits
  obtain ⟨blk, hblk, hsz⟩ := hq
  grind [MemoryState.getElem?_storeAt_self, MemoryState.getElem?_storeAt_ne,
    MemoryBlock.lengthInBits]

end Theorems

end

end LeanMLIR.RIR
