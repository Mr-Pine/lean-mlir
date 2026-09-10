/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.fd_curve25519_scalar_reduce
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_curve25519_scalar_reduce` (common)

`out = in mod l`, where `in` is a 512-bit little-endian scalar, `out` a 256-bit
one, and `l` the order of the ed25519 prime-order subgroup. The region returns
`out`.

The statement is arithmetic on the two buffers' values, not on limbs: the
twenty-four 21-bit digits the region unpacks into are an implementation detail
of the Barrett-style reduction and appear nowhere here.

`in` and `out` may alias -- `fd_curve25519_scalar.h` documents in-place
operation as fine -- so the spec is deliberately *not* framed as "`out` changes
and nothing else does". It says where the four stores land and what value they
leave, and a caller that wants the rest of memory back proves the two buffers
disjoint itself. The eight loads all run before the first store, which is why
in-place operation is sound and why the specified output is a function of the
*entry* state's `in`.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The order of the ed25519 prime-order subgroup,
`l = 2^252 + 27742317777372353535851937790883648493`. The `fd_curve25519_scalar`
tables encode it; `fd_curve25519_scalar.h` prints it in this form. -/
def scalarOrder : ℕ := 2 ^ 252 + 27742317777372353535851937790883648493

/-- A 64-byte little-endian scalar at `p`, the input's shape. -/
abbrev IsScalar512Ptr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (64 * 8) ∧ p.offset.toNat + 64 ≤ 2 ^ 64

/-- A 32-byte little-endian scalar at `p`, the output's shape. Shares
`IsScalarPtr`'s meaning with `fd_curve25519_scalar_validate`'s argument. -/
abbrev IsScalar256Ptr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (32 * 8) ∧ p.offset.toNat + 32 ≤ 2 ^ 64

/-- The four `i64` stores the region ends with, at `out + 0, 8, 16, 24`.

A `def`, not an `abbrev`, for the reason `pointOutMem` is one: reducible, every
unifier that meets it walks four splices. -/
def scalarOutMem (m : MemoryState) (r : Pointer) (w : Fin 4 → BitVec 64) : MemoryState :=
  (((m.splice r (w 0)).splice (r.withOffset 8) (w 1)).splice
    (r.withOffset 16) (w 2)).splice (r.withOffset 24) (w 3)

/-- The four words as one 256-bit little-endian value: `w 3` is the most
significant. -/
def packWords (w : Fin 4 → BitVec 64) : BitVec 256 := w 3 ++ w 2 ++ w 1 ++ w 0

/-- **`out = in mod l`.**

The region succeeds, returns `out`, and leaves memory as the four stores at
`out` leave it. The words it stores are pinned by their packed value: the
512-bit scalar `in` held on entry, reduced modulo `scalarOrder`.

The result is stated on `BitVec.toNat` rather than in `ZMod scalarOrder` so that
it fixes the 32 bytes exactly -- `in mod l` is below `l < 2^255`, so the
representative is canonical and the buffer's contents are determined, which a
caller re-encoding them needs.

The `∃ w` sits *inside* the state existential, as `fd_ed25519_point_frombytes`'s
four coordinate vectors do: the words are not determined until the stores run,
so a derivation has to name the state first and the words at the end. -/
abbrev fd_curve25519_scalar_reduce_spec (out inp : Pointer) (s : GlobalState)
    (hin : Fits s.mem inp (64 * 8)) : Prop :=
  let invocation := runFunction (fd_curve25519_scalar_reduce.denote
    (Ctxt.Valuation.ofHVector [.value inp, .value out]ₕ))
  let result := StateT.run invocation s

  ∃ s' : GlobalState,
    result = .value ([.value out]ₕ, s')
      ∧ ∃ w : Fin 4 → BitVec 64,
          s' ≈ ({ s with mem := scalarOutMem s.mem out w } : GlobalState)
            ∧ (packWords w).toNat = (readWord hin).toNat % scalarOrder

end Firedancer.Common
