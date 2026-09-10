/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_r43x6_ge_decode2

/-!
# What `fd_ed25519_point_frombytes_2x` is specified to compute

`fd_r43x6_ge_decode2`, with the six `wwl_t` out-parameters gathered back into
the two callers' `FD_R43X6_QUAD`s. Everything the decoded points satisfy is
`Decodes`, from the callee's spec; what this layer adds is *where* the six
vectors land -- `r₁`'s three fields, then `r₂`'s, at 0, 64 and 128 bytes.

The two QUADs are written in that order and nothing separates them, so if
`r₁` and `r₂` are the same object `r₂`'s three stores win. `writeQuad`
nesting says exactly that, which is why no disjointness hypothesis appears.

Both encodings are read at the entry state: the callee copies them into its
own staging buffers before anything is written, so a `buf` overlapping an `r`
is still read unwritten.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- The memory a whole-QUAD store leaves: the three whole-vector stores the
region makes, at the struct's field offsets of 0, 64 and 128 bytes. -/
def _root_.LeanMLIR.MemoryState.writeQuad (m : MemoryState) (p : Pointer) (q : Quad) :
    MemoryState :=
  ((m.splice p (vecBV q.v03)).splice (p.withOffset 64) (vecBV q.v14)).splice
    (p.withOffset 128) (vecBV q.v25)

/-- The QUAD both failure paths store: `fd_r43x6_ge_decode2` zeroes all six
out-vectors, the other point's included. -/
abbrev zeroQuad : Quad := ⟨zeroVec, zeroVec, zeroVec⟩

abbrev fd_ed25519_point_frombytes_2x_spec (r₁ buf₁ r₂ buf₂ : Pointer) (s : GlobalState)
    (hr₁ : IsQuadPtr s.mem r₁) (hbuf₁ : IsWvPtr s.mem buf₁)
    (hr₂ : IsQuadPtr s.mem r₂) (hbuf₂ : IsWvPtr s.mem buf₂) : Prop :=
  let invocation := runFunction (fd_ed25519_point_frombytes_2x.denote
    (Ctxt.Valuation.ofHVector [.value buf₂, .value r₂, .value buf₁, .value r₁]ₕ))
  let result := StateT.run invocation s
  let u₁ := readWv hbuf₁
  let u₂ := readWv hbuf₂

  ∃ (s' : GlobalState) (ret : LLVM.IntW 32) (q₁ q₂ : Quad),
    result = .value ([ret]ₕ, s')
    ∧ s' ≈ ({ s with mem := (s.mem.writeQuad r₁ q₁).writeQuad r₂ q₂ } : GlobalState)
    ∧ (Decodable u₁ → Decodable u₂ →
        ret = .value 0#32 ∧ Decodes u₁ q₁ ∧ Decodes u₂ q₂)
    ∧ (¬ Decodable u₁ →
        ret = .value (-1#32) ∧ q₁ = zeroQuad ∧ q₂ = zeroQuad)
    ∧ (Decodable u₁ → ¬ Decodable u₂ →
        ret = .value (-2#32) ∧ q₁ = zeroQuad ∧ q₂ = zeroQuad)

end Firedancer.Avx512
