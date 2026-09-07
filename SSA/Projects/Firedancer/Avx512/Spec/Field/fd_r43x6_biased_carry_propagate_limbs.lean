/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.R43x6

/-!
# What `fd_r43x6_biased_carry_propagate_limbs` computes

The first of the two serial carry macros of `fd_r43x6.h`. Nine operations
expand it -- `fd_r43x6_fold_signed`, the four `fd_r43x6_approx_mod*`, the four
`fd_r43x6_mod*`, `fd_r43x6_diagnose`, `fd_r43x6_is_nonzero` -- at `b = 0`,
`b = 1` and `b = 2^20`, so the bias `b` is a parameter throughout.

The macro is scalar `long` code over limbs `fd_r43x6_extract_limbs` has
already pulled out of the vector, so the model is over limb functions
`Fin limbCount → ℤ`. `x >>> n` below is `ashr` and `x % 2^n` is `and` with the
`n`-bit mask (`R43x6.shiftRight_eq`); the shifts are arithmetic, which is what
makes a negative limb borrow correctly and why this model is over `ℤ` where
`fd_r43x6_mul_fast`'s is over `ℕ`.

## Theory, from the header

Break limb 5 into its low 40 bits and the rest. Since `2^255 ≡ 19 (mod p)`,

    <x0,x1,x2,x3,x4,x5> = <x0 + 19·x5h, x1, x2, x3, x4, x5l>

and limb 5's overflow reappears in limb 0 scaled by 19. Serially propagating
limb 0's carry into limb 1, 1 into 2, and so on to 5 then leaves limbs 0-4
fully carried. `decodeLimbs_bcp` of the proof file is that paragraph as one
exact identity: the value changes by exactly `x5h · p`.

The bias `b` is subtracted from limb 5 before the chain and added back after.
It changes neither the element nor limbs 0-4; what it buys is limb 5's range,
since the last carry into limb 5 is as low as `-2^20` and `b` absorbs it.
-/

namespace Firedancer.Avx512

/-- The chain of unmasked sums: `bcpA b x i` is the macro's `_y i` at the
point it has taken its carry in, before `_y i &= _m`. `_c` is the carry out of
the limb below. Limb 5 is the biased `_y5 -= _b`, where the chain starts. -/
def bcpA (b : ℤ) (x : Fin R43x6.limbCount → ℤ) : Fin R43x6.limbCount → ℤ :=
  let y5 := x 5 - b
  let c5 := y5 >>> 40
  let y0 := x 0 + (19 : ℤ) * c5
  let c0 := y0 >>> 43
  let y1 := x 1 + c0
  let c1 := y1 >>> 43
  let y2 := x 2 + c1
  let c2 := y2 >>> 43
  let y3 := x 3 + c2
  let c3 := y3 >>> 43
  let y4 := x 4 + c3
  R43x6.limbs6 y0 y1 y2 y3 y4 y5

/-- **`fd_r43x6_biased_carry_propagate_limbs`**: `_y i &= _m` for each limb,
with limb 5 taking the last carry and `_y5 += _b` back. -/
def bcp (b : ℤ) (x : Fin R43x6.limbCount → ℤ) : Fin R43x6.limbCount → ℤ :=
  let c4 := bcpA b x 4 >>> 43
  R43x6.limbs6 (bcpA b x 0 % 2^43) (bcpA b x 1 % 2^43) (bcpA b x 2 % 2^43)
    (bcpA b x 3 % 2^43) (bcpA b x 4 % 2^43)
    (bcpA b x 5 % 2^40 + c4 + b)

/-- The **exact** domain of the macro at bias `b`, transcribed from the header
comment:

    x0    in [-2^63+19*2^23, 2^63-19*(2^23-1))
    x1-x4 in [-2^63+   2^20, 2^63-   (2^20-1))
    x5    in [-2^63+b,       2^63            )

Limb 0's is narrower by the `19` that limb 5's overflow is scaled by, and limb
5's is the only one that moves with the bias. It is far wider than `s62`: it
rules out at most `19 · 2^24 < 2^29` of the `2^64` values a limb can take, and
it is exactly the condition under which no add in the chain overflows a
`long`. -/
def BcpPre (b : ℤ) (x : Fin R43x6.limbCount → ℤ) : Prop :=
    (-2 ^ 63 + 19 * 2 ^ 23 ≤ x 0 ∧ x 0 < 2 ^ 63 - 19 * (2 ^ 23 - 1))
  ∧ (∀ i : Fin R43x6.limbCount, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 4 →
        -2 ^ 63 + 2 ^ 20 ≤ x i ∧ x i < 2 ^ 63 - (2 ^ 20 - 1))
  ∧ (-2 ^ 63 + b ≤ x 5 ∧ x 5 < 2 ^ 63)

/-- The values the chain forms, in program order. Each is the operand of an
`nsw` add, subtract or multiply in the emitted code, so each has to be shown
to fit in a `long` before the region denotes to anything but poison. -/
def bcpChain (b : ℤ) (x : Fin R43x6.limbCount → ℤ) : List ℤ :=
  [bcpA b x 5, (19 : ℤ) * (bcpA b x 5 >>> 40), bcpA b x 0, bcpA b x 1, bcpA b x 2,
   bcpA b x 3, bcpA b x 4, bcpA b x 5 % 2^40 + b,
   bcpA b x 5 % 2^40 + b + (bcpA b x 4 >>> 43)]

end Firedancer.Avx512
