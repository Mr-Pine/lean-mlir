import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Arithmetic

/-!
The natural-number five-round Montgomery schedule shared by the scalar
implementations. `telescope` follows the carry equations of the exact imported
32-byte reducer. The pending word refinement must connect each machine value
and flag to these natural-number equations.
-/
namespace Agave.Ed25519.ScalarReduce32.Arithmetic
open Agave.Ed25519.UpstreamMath.Canonicality
set_option exponentiation.threshold 512

/-- Unnormalized nine-limb multiplication result. -/
def wideLimbs (z0 z1 z2 z3 z4 z5 z6 z7 z8 : Nat) : Nat :=
  z0 + radix*z1 + radix^2*z2 + radix^3*z3 + radix^4*z4 +
    radix^5*z5 + radix^6*z6 + radix^7*z7 + radix^8*z8

/-- Upper half after the five adjustment steps, before its carries are repacked
into 52-bit limbs. The missing L[3] terms really are zero in the source. -/
def upperHalf (z5 z6 z7 z8 n1 n2 n3 n4 carry : Nat) : Nat :=
  carry + z5 + n1*17592186044416 + n3*1367801 + n4*3916664325105025 +
    radix*(z6 + n2*17592186044416 + n4*1367801) +
    radix^2*(z7 + n3*17592186044416) +
    radix^3*(z8 + n4*17592186044416)

/-- The five low-limb cancellation equations telescope to the full-width
Montgomery identity, with no assumption about unproved machine execution. -/
theorem telescope (z0 z1 z2 z3 z4 z5 z6 z7 z8 : Nat)
    (n0 n1 n2 n3 n4 c0 c1 c2 c3 c4 : Nat)
    (h0 : z0 + n0*671914833335277 = radix*c0)
    (h1 : c0 + z1 + n0*3916664325105025 + n1*671914833335277 = radix*c1)
    (h2 : c1 + z2 + n0*1367801 + n1*3916664325105025 + n2*671914833335277 = radix*c2)
    (h3 : c2 + z3 + n1*1367801 + n2*3916664325105025 + n3*671914833335277 = radix*c3)
    (h4 : c3 + z4 + n0*17592186044416 + n2*1367801 + n3*3916664325105025 +
      n4*671914833335277 = radix*c4) :
    upperHalf z5 z6 z7 z8 n1 n2 n3 n4 c4 * montgomeryModulus =
      wideLimbs z0 z1 z2 z3 z4 z5 z6 z7 z8 + limbs n0 n1 n2 n3 n4 * ell := by
  norm_num [upperHalf, wideLimbs, limbs, radix, montgomeryModulus, ell] at *
  omega

/-- Five bounded adjustment digits form a number strictly below 2^260. -/
theorem adjustment_bound (n0 n1 n2 n3 n4 : Nat)
    (h0 : n0 < radix) (h1 : n1 < radix) (h2 : n2 < radix)
    (h3 : n3 < radix) (h4 : n4 < radix) :
    limbs n0 n1 n2 n3 n4 < montgomeryModulus := by
  norm_num [limbs, radix, montgomeryModulus] at *
  omega

/-- The five `part1` rounds, in the order of the pinned source. The first result
is the Montgomery adjustment integer, the second is the unreduced quotient. -/
def reduceSchedule (z0 z1 z2 z3 z4 z5 z6 z7 z8 : Nat) : Nat × Nat :=
  let t0 := z0
  let n0 := adjustmentDigit t0
  let c0 := adjustmentCarry t0
  let t1 := c0 + z1 + n0*3916664325105025
  let n1 := adjustmentDigit t1
  let c1 := adjustmentCarry t1
  let t2 := c1 + z2 + n0*1367801 + n1*3916664325105025
  let n2 := adjustmentDigit t2
  let c2 := adjustmentCarry t2
  let t3 := c2 + z3 + n1*1367801 + n2*3916664325105025
  let n3 := adjustmentDigit t3
  let c3 := adjustmentCarry t3
  let t4 := c3 + z4 + n0*17592186044416 + n2*1367801 + n3*3916664325105025
  let n4 := adjustmentDigit t4
  let c4 := adjustmentCarry t4
  (limbs n0 n1 n2 n3 n4, upperHalf z5 z6 z7 z8 n1 n2 n3 n4 c4)

/-- Exact arithmetic certificate for the unbounded natural-number schedule.
No input bound is needed to establish the cancellation identity. -/
theorem reduceSchedule_certificate (z0 z1 z2 z3 z4 z5 z6 z7 z8 : Nat) :
    let pair := reduceSchedule z0 z1 z2 z3 z4 z5 z6 z7 z8
    pair.1 < montgomeryModulus ∧
      pair.2 * montgomeryModulus =
        wideLimbs z0 z1 z2 z3 z4 z5 z6 z7 z8 + pair.1 * ell := by
  dsimp only [reduceSchedule]
  constructor
  · apply adjustment_bound <;> apply adjustmentDigit_bound
  · apply telescope <;> apply adjustment_identity

/-- Canonical output of the source arithmetic schedule when its multiplication
columns denote x times the literal source R constant. Connecting the flagged
128/64-bit operations to those columns remains a separate proof. -/
theorem reduceSchedule_correct (x z0 z1 z2 z3 z4 z5 z6 z7 z8 : Nat)
    (hx : x < 2^256)
    (hz : wideLimbs z0 z1 z2 z3 z4 z5 z6 z7 z8 = x * sourceR) :
    finish (reduceSchedule z0 z1 z2 z3 z4 z5 z6 z7 z8).2 = x % ell ∧
      finish (reduceSchedule z0 z1 z2 z3 z4 z5 z6 z7 z8).2 < ell := by
  have hc := reduceSchedule_certificate z0 z1 z2 z3 z4 z5 z6 z7 z8
  dsimp only at hc
  rw [hz] at hc
  exact finish_correct x _ _ hx hc.1 hc.2

end Agave.Ed25519.ScalarReduce32.Arithmetic
