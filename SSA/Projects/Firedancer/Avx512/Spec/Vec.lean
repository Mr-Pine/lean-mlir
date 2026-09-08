/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Quad

/-!
# A single `fd_r43x6_t` in memory

`Spec/Quad.lean` addresses the three vectors of a QUAD together, because the
point operations take them that way. The `fd_r43x6.c` entry points --
`fd_r43x6_repsqr_mul2`, `fd_r43x6_pow22523_2`, `fd_r43x6_ge_decode2` -- return
through *separate* `wwl_t *` out-parameters, one vector each, which is what
`IsVecPtr`/`readVec` are for. `vecBV` (in `Spec/Quad.lean`) is the bit pattern
a whole-vector store writes.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `p` addresses one `fd_r43x6_t`: eight 64-bit lanes, 64 bytes. -/
abbrev IsVecPtr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (8 * 64) ∧ p.offset.toNat + 64 ≤ 2 ^ 64

def readVec? (p : Pointer) (m : MemoryState) : Option (Vector (BitVec 64) 8) := do
  let block ← m.live? p.id
  return Vector.ofFn fun j => block.bytes.extractLsb' (p.offsetInBits + 64 * j.val) 64

theorem readVec?_isSome {m : MemoryState} {p : Pointer} (h : IsVecPtr m p) :
    (readVec? p m).isSome := by
  obtain ⟨⟨block, hblk, -⟩, -⟩ := h
  have hlive : m.live? p.id = some block := by simp only [MemoryState.live?, hblk]
  simp [readVec?, hlive]

def readVec {p : Pointer} {m : MemoryState} (h : IsVecPtr m p) : Vector (BitVec 64) 8 :=
  (readVec? p m).get (readVec?_isSome h)

/-- The field element eight lanes stand for, as `decodeVec` reads it. -/
abbrev vecValue (v : Vector (BitVec 64) 8) : ZMod p := decodeVec (by omega) v

end Firedancer.Avx512
