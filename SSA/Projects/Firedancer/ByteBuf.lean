/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# 32-byte buffers

A 32-byte little-endian buffer read as one 256-bit word: field-element and point encodings,
and scalars.
-/

namespace Firedancer
open LeanMLIR SLLVM

/-- A 32-byte buffer at `p`: the block holds 256 bits from `p`'s offset, and byte offsets into
it do not wrap. -/
abbrev IsByteBufPtr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (32 * 8) ∧ p.offset.toNat + 32 ≤ 2 ^ 64

/-- The 32-byte little-endian buffer at `p`, read as one 256-bit word. -/
def readBuf? (p : Pointer) (m : MemoryState) : Option (BitVec 256) := do
  let liveBlock ← m.live? p.id
  return liveBlock.bytes.extractLsb' p.offsetInBits 256

theorem readBuf?_isSome {m : MemoryState} {p : Pointer} (h : IsByteBufPtr m p) :
    (readBuf? p m).isSome := by
  obtain ⟨⟨block, hblk, -⟩, -⟩ := h
  have hlive : m.live? p.id = some block := by
    simp only [MemoryState.live?, hblk]
  simp [readBuf?, hlive]

def readBuf {p : Pointer} {m : MemoryState} (h : IsByteBufPtr m p) : BitVec 256 :=
  (readBuf? p m).get (readBuf?_isSome h)

/-- A store leaves live blocks and their sizes alone, so a buffer that fitted at `q` still fits
after a splice anywhere. -/
theorem isByteBufPtr_splice {m : MemoryState} {p q : Pointer} {w : Nat} {x : BitVec w}
    (h : IsByteBufPtr m q) : IsByteBufPtr (m.splice p x) q :=
  ⟨fits_splice h.left, h.right⟩

/-- A buffer read looks only at the block the pointer addresses, so it survives any step that
left that block alone. -/
theorem readBuf_of_live?_eq {m m' : MemoryState} {p : Pointer}
    (h : m'.live? p.id = m.live? p.id) {hp : IsByteBufPtr m p} {hp' : IsByteBufPtr m' p} :
    readBuf hp' = readBuf hp := by
  simp only [readBuf, readBuf?, h]

end Firedancer
