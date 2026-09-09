/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_r43x6_ge_decode2
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Avx512.Spec.Util.wv_ld
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_unpack
import SSA.Projects.Firedancer.Curve

/-!
# What `fd_r43x6_ge_decode2` is specified to compute

Two point decompressions, RFC 8032 §5.1.3, short-circuiting: `0` if both
encodings name a point, `-1` if the first does not, `-2` if the second does
not. On either failure *all six* out-vectors are zeroed -- the HPC path
matches the reference implementation, which clears the other point too.

Each point comes back QUAD-packed across three `wwl_t` out-parameters, so the
six pointers are six separate writes; `Quad.toPoint` is what reads a point off
them.

The sign clause is guarded by `X ≠ 0`, as in the `ref` layer: `fd_r43x6_diagnose`
returns `-1` at zero, so `x_0 != x_mod_2` accepts either sign bit there. The C
says so in as many words, citing Dalek.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- The `y` an encoding names: the low 255 bits of the `uint256`, reduced. -/
abbrev wvY (u : Vector (BitVec 64) 4) : ZMod p := ((wvNat u % 2 ^ 255 : ℕ) : ZMod p)

/-- ... and the sign bit of `x` it carries, the top bit of the last lane. -/
abbrev wvSign (u : Vector (BitVec 64) 4) : Bool := u[3].getLsbD 63

abbrev Decodable (u : Vector (BitVec 64) 4) : Prop :=
  IsSquare ((wvY u ^ 2 - 1) / (d * wvY u ^ 2 + 1))

/-- ... and what the QUAD then holds. -/
abbrev Decodes (u : Vector (BitVec 64) 4) (q : Quad) : Prop :=
  let point := q.toPoint
  OnCurve point.x point.y
    ∧ point.Z = 1
    ∧ point.Y = wvY u
    ∧ point.T / point.Z = point.x * point.y
    ∧ (point.X ≠ 0 → (point.X.val % 2 = 0 ↔ wvSign u = false))

/-- The zero vector both failure paths store. -/
abbrev zeroVec : Vector (BitVec 64) 8 := Vector.replicate 8 0#64

abbrev fd_r43x6_ge_decode2_spec (a03 a14 a25 sa b03 b14 b25 sb : Pointer) (s : GlobalState)
    (ha03 : IsVecPtr s.mem a03) (ha14 : IsVecPtr s.mem a14) (ha25 : IsVecPtr s.mem a25)
    (hb03 : IsVecPtr s.mem b03) (hb14 : IsVecPtr s.mem b14) (hb25 : IsVecPtr s.mem b25)
    (hsa : IsWvPtr s.mem sa) (hsb : IsWvPtr s.mem sb) : Prop :=
  let invocation := runFunction (fd_r43x6_ge_decode2.denote (Ctxt.Valuation.ofHVector
    [.value sb, .value b25, .value b14, .value b03,
      .value sa, .value a25, .value a14, .value a03]ₕ))
  let result := StateT.run invocation s
  let ua := readWv hsa
  let ub := readWv hsb

  ∃ (s' : GlobalState) (ret : LLVM.IntW 32),
    result = .value ([ret]ₕ, s') ∧
    ∃ va03 va14 va25 vb03 vb14 vb25 : Vector (BitVec 64) 8,
    let outMem :=
      ((((((s.mem.splice a03 (vecBV va03)).splice a14 (vecBV va14)).splice
        a25 (vecBV va25)).splice b03 (vecBV vb03)).splice b14 (vecBV vb14)).splice
        b25 (vecBV vb25))
    s' ≈ ({ s with mem := outMem } : GlobalState)
    ∧ (Decodable ua → Decodable ub →
        ret = .value 0#32
        ∧ Decodes ua ⟨va03, va14, va25⟩ ∧ Decodes ub ⟨vb03, vb14, vb25⟩)
    ∧ (¬ Decodable ua →
        ret = .value (-1#32)
        ∧ va03 = zeroVec ∧ va14 = zeroVec ∧ va25 = zeroVec
        ∧ vb03 = zeroVec ∧ vb14 = zeroVec ∧ vb25 = zeroVec)
    ∧ (Decodable ua → ¬ Decodable ub →
        ret = .value (-2#32)
        ∧ va03 = zeroVec ∧ va14 = zeroVec ∧ va25 = zeroVec
        ∧ vb03 = zeroVec ∧ vb14 = zeroVec ∧ vb25 = zeroVec)

end Firedancer.Avx512
