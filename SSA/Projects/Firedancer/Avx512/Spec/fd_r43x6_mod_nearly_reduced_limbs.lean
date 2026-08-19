/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.R43x6

/-!
# What `fd_r43x6_mod_nearly_reduced_limbs` computes

The second of the two serial carry macros: nearly reduced in, reduced out.
`fd_r43x6_mod*`, `fd_r43x6_diagnose` and `fd_r43x6_is_nonzero` all expand it,
always immediately after `fd_r43x6_biased_carry_propagate_limbs`, which is
what supplies its nearly reduced input.

## Theory, from the header

A nearly reduced `x` is in `[0,2p)`, so `x = q·p + r` with `q ∈ [0,1]` and
`r ∈ [0,p)`. Since `p = 2^255 - 19`, `x < p` is `x + 19 < 2^255`, so the carry
out of bit 255 of `x + 19` *is* `q`:

    y  = x + 19
    q  = y >> 255
    y -= q << 255
    r  = y - if(!q, 19, 0)

The `if` is the `fd_long_if` cmov, branchless for deterministic timing; it is
what `Mlir/fd_long_if.lean` lifts and `Proof/fd_long_if.lean` proves.

The two halves are the two carry propagates below: `mnrA` adds the 19 and
propagates, and `mnrE` takes the 19 back off (or not) and propagates the
borrow. Limb 5 is masked to 40 bits between them, which is the `y -= q<<255`.
-/

namespace Firedancer.Avx512

/-- The first half, `_y0 += 19` propagated: `mnrA x i` is the macro's `_y i`
after the carry into limb `i` and before masking. -/
def mnrA (x : Fin R43x6.limbCount → ℤ) : Fin R43x6.limbCount → ℤ :=
  let y0 := x 0 + 19
  let c0 := y0 >>> 43
  let y1 := x 1 + c0
  let c1 := y1 >>> 43
  let y2 := x 2 + c1
  let c2 := y2 >>> 43
  let y3 := x 3 + c2
  let c3 := y3 >>> 43
  let y4 := x 4 + c3
  let c4 := y4 >>> 43
  let y5 := x 5 + c4
  R43x6.limbs6 y0 y1 y2 y3 y4 y5

/-- `q = y >> 255`, the carry out of bit 255 of `x + 19`: `0` when `x < p` and
`1` when `p ≤ x < 2p`. Limb 5 holds bits 215 and up, so bit 255 is its bit
40. -/
def mnrQ (x : Fin R43x6.limbCount → ℤ) : ℤ := mnrA x 5 >>> 40

/-- The second half, `_y0 -= fd_long_if( !_c, 19L, 0L )` propagated. `mnrE x i`
is the macro's `_y i` on its second pass, after the borrow into limb `i` and
before masking; limb 5 takes no borrow of its own, so only limbs 0-4 are formed
here. Primed, since these are the macro's `_y i` a second time. -/
def mnrE (x : Fin R43x6.limbCount → ℤ) : Fin R43x6.limbCount → ℤ :=
  let y0' := mnrA x 0 % 2^43 - (if mnrQ x = 0 then 19 else 0)
  let c0' := y0' >>> 43
  let y1' := mnrA x 1 % 2^43 + c0'
  let c1' := y1' >>> 43
  let y2' := mnrA x 2 % 2^43 + c1'
  let c2' := y2' >>> 43
  let y3' := mnrA x 3 % 2^43 + c2'
  let c3' := y3' >>> 43
  let y4' := mnrA x 4 % 2^43 + c3'
  R43x6.limbs6 y0' y1' y2' y3' y4' 0

/-- **`fd_r43x6_mod_nearly_reduced_limbs`**: the reduced limbs. Limb 5 is the
40-bit remainder of the first half plus the last borrow of the second. -/
def mnr (x : Fin R43x6.limbCount → ℤ) : Fin R43x6.limbCount → ℤ :=
  let c4' := mnrE x 4 >>> 43
  R43x6.limbs6 (mnrE x 0 % 2^43) (mnrE x 1 % 2^43) (mnrE x 2 % 2^43)
    (mnrE x 3 % 2^43) (mnrE x 4 % 2^43)
    (mnrA x 5 % 2^40 + c4')

/-- The values the two chains form, in program order. All of these are
non-negative as well as in range -- the emitted code marks them `nuw` on top
of `nsw` -- with the single exception of `mnrE y 0`, the one subtraction,
which is exactly where a borrow is intended. -/
def mnrChain (x : Fin R43x6.limbCount → ℤ) : List ℤ :=
  [mnrA x 0, mnrA x 1, mnrA x 2, mnrA x 3, mnrA x 4, mnrA x 5,
   mnrE x 0, mnrE x 1, mnrE x 2, mnrE x 3, mnrE x 4,
   mnrA x 5 % 2^40 + (mnrE x 4 >>> 43)]

end Firedancer.Avx512
