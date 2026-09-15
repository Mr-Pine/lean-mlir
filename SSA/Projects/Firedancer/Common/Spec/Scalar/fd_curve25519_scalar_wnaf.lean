/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_wnaf
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_validate

/-!
# `fd_curve25519_scalar_wnaf` (common)

The region returns, its only effect on memory is on the 256 `short`s at `slides`, and those
`short`s are the scalar's digits: each zero or odd and within `±2 ^ bits`, and for
`bits ≤ 13` summing, weighted by `2 ^ k`, to the scalar's low 255 bits.

One splice of the whole buffer is exact rather than an over-approximation of the loops'
scattered stores: `^bb2` and `^bb1` write all 256 entries before any other store, so whatever
the absorb loop does afterwards the buffer ends as some 4096 bits. That nothing *past* the
buffer is written rests on the C's argument that the carry never propagates beyond
`slides[255]` (the comment above the subtract case in `fd_curve25519_scalar.c`), which the proof
carries as an invariant.

The sum needs `bits ≤ 13`: at 14, `delta = 2 ^ min(j - i, 14)` passes the `delta > 2 * max`
check while `j - i > 14`, and the digit absorbs a bit at the wrong weight. The C documents
`bits` in `[1, 12]`.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- 256 `short`s at `p`, the output's shape. -/
abbrev IsSlidesPtr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (256 * 16) ∧ p.offset.toNat + 512 ≤ 2 ^ 64

/-- The 32-byte little-endian scalar at `p`. -/
def readScalar? (p : Pointer) (m : MemoryState) : Option (BitVec 256) := do
  let blk ← m.live? p.id
  return blk.bytes.extractLsb' p.offsetInBits 256

theorem readScalar?_isSome {m : MemoryState} {p : Pointer} (h : IsScalarPtr m p) :
    (readScalar? p m).isSome := by
  obtain ⟨⟨blk, hblk, -⟩, -⟩ := h
  simp [readScalar?, MemoryState.live?, hblk]

def readScalar {m : MemoryState} {p : Pointer} (h : IsScalarPtr m p) : BitVec 256 :=
  (readScalar? p m).get (readScalar?_isSome h)

/-- `∑ k < K, slides[k] * 2 ^ k`, with `slides[k]` signed. -/
def digitSum (w : BitVec 4096) : Nat → Int
  | 0 => 0
  | k + 1 => digitSum w k + (w.extractLsb' (16 * k) 16).toInt * 2 ^ k

/-- **The region returns, writes nowhere but `slides`, and writes the scalar's digits there.**

The state it leaves is the entry state with the 256 entries at `slides` replaced by some `w`;
the allocation counter, the symbol table and every other block -- the scalar `n`'s included --
are untouched. Each entry of `w`, as a signed `short`, is zero or odd and at most `2 ^ bits` in
absolute value. For `bits ≤ 13` and `slides`, `n` in different blocks, the entries weighted by
`2 ^ k` sum to `n`'s low 255 bits. -/
abbrev fd_curve25519_scalar_wnaf_spec (slides n : Pointer) (bits : BitVec 32)
    (s : GlobalState) (hn : IsScalarPtr s.mem n) : Prop :=
  let invocation := runFunction (fd_curve25519_scalar_wnaf.denote
    (Ctxt.Valuation.ofHVector [.value bits, .value n, .value slides]ₕ))

  ∃ s' : GlobalState, StateT.run invocation s = .value ([]ₕ, s')
    ∧ ∃ w : BitVec (256 * 16), s' ≈ ({ s with mem := s.mem.splice slides w } : GlobalState)
      ∧ (∀ k < 256, (w.extractLsb' (16 * k) 16 = 0 ∨ (w.extractLsb' (16 * k) 16).toInt % 2 = 1)
        ∧ (w.extractLsb' (16 * k) 16).toInt.natAbs ≤ 2 ^ bits.toNat)
      ∧ (bits.toNat ≤ 13 → slides.id ≠ n.id →
        digitSum w 256 = ((readScalar hn).toNat % 2 ^ 255 : Nat))

end Firedancer.Common
