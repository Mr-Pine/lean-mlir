/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Spec.Quad

/-!
# A single `fd_r43x6_t` in memory

`Spec/Quad.lean` addresses the three vectors of a QUAD together, because the
point operations take them that way. The `fd_r43x6.c` entry points --
`fd_r43x6_repsqr_mul2`, `fd_r43x6_pow22523_2`, `fd_r43x6_ge_decode2` -- return
through *separate* `wwl_t *` out-parameters, one vector each, which is what
`IsVecPtr`/`readVec` are for. `vecBV` (in `Spec/Quad.lean`) is the bit pattern
a whole-vector store writes.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `p` addresses one `fd_r43x6_t`: eight 64-bit lanes, 64 bytes. -/
abbrev IsVecPtr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (8 * 64) ∧ p.offset.toNat + 64 ≤ 2 ^ 64

def readVec? (p : Pointer) (m : MemoryState) : Option (Vector (BitVec 64) 8) := do
  let block ← m.live? p.id
  return Vector.ofFn fun j => block.bytes.extractLsb' (p.offsetInBits + 64 * j.val) 64

/-- A store leaves live blocks and their sizes alone, so a vector that fitted
at `p` before still fits after a splice anywhere -- the `fd_r43x6_t`
counterpart of `Ref.isFieldElemPtr_splice`. -/
theorem isVecPtr_splice {m : MemoryState} {p q : Pointer} {wd : Nat} {x : BitVec wd}
    (h : IsVecPtr m p) : IsVecPtr (m.splice q x) p :=
  ⟨fits_splice h.1, h.2⟩

/-- `IsVecPtr` speaks only of a live block and its size, and `≈` equates
those, so it transports along an equivalence -- the form in which a spec's
`s' ≈ ...` hands the readback its proof. -/
theorem isVecPtr_of_equiv {s s' : GlobalState} {p : Pointer}
    (h : s ≈ s') (hp : IsVecPtr s.mem p) : IsVecPtr s'.mem p := by
  obtain ⟨⟨block, hblk, hlen⟩, hoff⟩ := hp
  have hlive := h.live p.id
  simp only [MemoryState.live?, hblk] at hlive
  -- `live?` is a `match`, so `hlive` is one too; splitting names the branch
  -- and hands over the scrutinee's equation, which is the lookup wanted.
  replace hlive : s'.mem[p.id]? = some (Block.live block) := by
    split at hlive <;> simp_all
  exact ⟨⟨block, hlive, hlen⟩, hoff⟩

theorem readVec?_isSome {m : MemoryState} {p : Pointer} (h : IsVecPtr m p) :
    (readVec? p m).isSome := by
  obtain ⟨⟨block, hblk, -⟩, -⟩ := h
  have hlive : m.live? p.id = some block := by simp only [MemoryState.live?, hblk]
  simp [readVec?, hlive]

def readVec {p : Pointer} {m : MemoryState} (h : IsVecPtr m p) : Vector (BitVec 64) 8 :=
  (readVec? p m).get (readVec?_isSome h)

/-- The field element eight lanes stand for, as `decodeVec` reads it. -/
abbrev vecValue (v : Vector (BitVec 64) 8) : ZMod p := decodeVec (by omega) v

/-- `fd_r43x6_zero()`: the all-zero pattern, and the vector both of
`fd_r43x6_ge_decode2`'s failure paths store. -/
def zeroVec : Vector (BitVec 64) 8 := Vector.replicate 8 0#64

/-- `fd_r43x6_p()`: `p`'s limbs in lanes 0-5, lanes 6 and 7 clear -- the second
representation of zero, and the region's own `dense<[8796093022189, …]>`
constant. The lanes are `2^43-19, 2^43-1, 2^43-1, 2^43-1, 2^43-1, 2^40-1`,
written as the literals the artifact carries so `denote_dense` matches. -/
def pVec : Vector (BitVec 64) 8 :=
  #v[8796093022189, 8796093022207, 8796093022207, 8796093022207, 8796093022207,
     1099511627775, 0, 0]

end Firedancer.Avx512
