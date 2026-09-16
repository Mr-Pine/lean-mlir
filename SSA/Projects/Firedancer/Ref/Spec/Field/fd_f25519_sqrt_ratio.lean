/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqrt_ratio
import SSA.Projects.Firedancer.Ref.Spec.Bias

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `√(u/v)`, with the flag saying whether `u/v` is a square -- the contract
RFC 9496 calls `SQRT_RATIO_M1`, stated over the field rather than over the
region's operations.

The flag is `∃ x, x² · v = u`, which is the right statement at `v = 0` too:
there it says `u = 0`, and the region does return `1` exactly then. The root:

* square case -- `o² · v = u`;
* non-square case with `v ≠ 0` -- `o² · v = sqrtm1 · u`, the standard "off by
  `√-1`" answer;
* `v = 0` -- `o = 0`, the exceptional case the ratio does not cover.

`o` is always the *non-negative* representative (`o.val % 2 = 0`); the region's
last operation is `fd_f25519_abs`, whose result also fixes the limb bounds --
per-limb, plus the sum bound `fd_f25519_sgn` needs downstream.

`sqrtm1` is a constant of the field, not a parameter: the region reaches
`@fd_f25519_sqrtm1` through `llvm.mlir.addressof`, so its address never enters
the statement. A conformance proof is what connects the two, with
`HoldsGlobal "fd_f25519_sqrtm1" fd_f25519_sqrtm1_init s g`, and it also needs
`g.id ≠ o.id` -- the region writes through `o` at `%18`/`%19` before reading
the global at `%23`/`%27`, and nothing else says those writes miss it.

NOTE this is a real proof obligation, not a restatement of the code: getting
from what the region computes -- `c = (u v⁷)^((p-5)/8) · u v³` and three
comparisons of `c² · v` against `u`, `-u`, `-u · i` -- to the claims above
needs the `p ≡ 5 mod 8` square-root theory, namely that `c² · v` lands in
`{u, -u, i·u, -i·u}` and that which of the four it is decides squareness. -/
abbrev fd_f25519_sqrt_ratio_spec (o u v : Pointer) (s : GlobalState)
    (ho : IsFieldElemPtr s.mem o)
    (hu : IsFieldElemPtr s.mem u)
    (hv : IsFieldElemPtr s.mem v) : Prop :=
  let invocation := runFunction (fd_f25519_sqrt_ratio.denote
    (Ctxt.Valuation.ofHVector [.value v, .value u, .value o]ₕ))
  let result := StateT.run invocation s
  let uIn := readFieldElem hu
  let vIn := readFieldElem hv
  let isSquare := ∃ x : ZMod p, x ^ 2 * vIn = uIn

  ∃ out : Fin 5 → BitVec 64,
    let output_state : GlobalState := { s with mem := s.mem.splice o (packLimbs out) }
    let root := readFieldElem (m := output_state.mem) (isFieldElemPtr_splice ho)

    -- `fd_f25519_abs` leaves the non-negative representative
    root.val % 2 = 0
    ∧ (isSquare → root ^ 2 * vIn = uIn)
    -- ∧ (¬ isSquare → vIn ≠ 0 → root ^ 2 * vIn = sqrtm1 * uIn) -- I don't think this is a relevant part of the spec
    ∧ (vIn = 0 → root = 0)
    ∧ BiasBounds (m := output_state.mem) (isFieldElemPtr_splice ho)
    ∧ limbSum (m := output_state.mem) (isFieldElemPtr_splice ho) < 2 ^ 256 - 38
    ∧ (∃ s' : GlobalState,
        result = .value
          ([(.value (if isSquare then 1#32 else 0#32) : LLVM.IntW 32)]ₕ, s')
        ∧ output_state ≈ s')
    -- all-zero limbs come only from an all-zero input
    ∧ (ZeroLimbs o output_state.mem → ZeroLimbs u s.mem ∨ ZeroLimbs v s.mem)

end Firedancer.Ref
