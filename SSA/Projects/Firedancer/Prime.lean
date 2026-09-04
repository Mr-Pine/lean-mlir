/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ed25519
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# `2^255 - 19` is prime

A Pratt certificate for the ed25519 field characteristic, checked by the kernel.

`Nat.lucas_primality` needs, for a witness `a`, that `a ^ (n-1) = 1` and
`a ^ ((n-1)/q) ≠ 1` for every prime `q ∣ n - 1`.  Two things make that machine
checkable:

* `powModAux`, a fuelled square-and-multiply.  The fuel makes the recursion
  structural, so the kernel reduces it in `fuel` steps of GMP-backed `*`/`%`
  instead of unfolding `npowRec` `2^255` times.
* the factor lists, peeled one prime at a time with `dvdStep` down to leaves
  that `norm_num` can factor directly.  Each list is written right-nested with a
  trailing `* 1`, so that peeling terminates on `q ∣ 1` and every prime factor
  is handled by the same step.

The certificate is a chain of seven Lucas nodes: `p`, `l`, `n`, `m`, `k`, `q`
and `r`.  It is from https://math.stackexchange.com/a/4999951 ; every node's
factorisation and both Lucas conditions were re-verified numerically before use.
-/

namespace Pratt

/-- Square-and-multiply for `a ^ k % n`, with `fuel` bounding `log₂ k`.
Fuelled so the recursion is structural and hence kernel-reducible. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, n => 1 % n
  | fuel + 1, a, k, n =>
      let h := powModAux fuel (a * a % n) (k / 2) n
      if k % 2 = 1 then h * a % n else h

/-- `powModAux` computes `a ^ k % n` once the fuel covers the bit width of `k`. -/
private theorem powModAux_eq {n : ℕ} :
    ∀ (fuel a k : ℕ), k < 2 ^ fuel → powModAux fuel a k n = a ^ k % n
  | 0, a, k, hk => by
      have : k = 0 := by simpa using hk
      subst this; simp [powModAux]
  | fuel + 1, a, k, hk => by
      have hk2 : k / 2 < 2 ^ fuel := by rw [pow_succ] at hk; omega
      have ih := powModAux_eq (n := n) fuel (a * a % n) (k / 2) hk2
      have hsq : (a * a % n) ^ (k / 2) % n = a ^ (2 * (k / 2)) % n := by
        rw [← Nat.pow_mod, ← pow_two, ← pow_mul]
      simp only [powModAux, ih, hsq]
      rcases Nat.even_or_odd k with h | h
      · have h2 : k % 2 = 0 := Nat.even_iff.mp h
        rw [if_neg (by omega), show 2 * (k / 2) = k from by omega]
      · have h2 : k % 2 = 1 := Nat.odd_iff.mp h
        rw [if_pos h2, Nat.mod_mul_mod, ← pow_succ, show 2 * (k / 2) + 1 = k from by omega]

/-- `powModAux` lands in `[0, n)`. -/
private theorem powModAux_lt {n : ℕ} (hn : 0 < n) :
    ∀ (fuel a k : ℕ), powModAux fuel a k n < n
  | 0, _, _ => Nat.mod_lt _ hn
  | fuel + 1, a, k => by
      simp only [powModAux]
      split
      · exact Nat.mod_lt _ hn
      · exact powModAux_lt hn fuel _ _

/-- Transfer a `powModAux` computation into `ZMod n`.  Fuel is fixed at `256`,
which covers every exponent in the certificate. -/
private theorem cast_pow_eq {n a k m : ℕ} (hk : k < 2 ^ 256)
    (h : powModAux 256 a k n = m) : ((a : ℕ) : ZMod n) ^ k = ((m : ℕ) : ZMod n) := by
  rw [← h, powModAux_eq 256 a k hk, ZMod.natCast_mod, Nat.cast_pow]

/-- Transfer of the `= 1` Lucas condition from the kernel computation. -/
private theorem pow_eq_one {n a k : ℕ} (hk : k < 2 ^ 256)
    (h : powModAux 256 a k n = 1) : ((a : ℕ) : ZMod n) ^ k = 1 := by
  rw [cast_pow_eq hk h, Nat.cast_one]

/-- Transfer of the `≠ 1` Lucas condition.  The residue is automatically `< n`,
so no separate bound on it is needed. -/
private theorem pow_ne_one {n a k : ℕ} (hn : 1 < n) (hk : k < 2 ^ 256)
    (h : powModAux 256 a k n ≠ 1) : ((a : ℕ) : ZMod n) ^ k ≠ 1 := by
  rw [cast_pow_eq hk rfl]
  intro hc
  rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by simp, ZMod.natCast_eq_natCast_iff'] at hc
  rw [Nat.mod_eq_of_lt (powModAux_lt (by omega) 256 a k), Nat.mod_eq_of_lt hn] at hc
  exact h hc

/-- One Pratt node: a witness `a` of order `n - 1`, with both Lucas conditions
discharged by kernel evaluation of `powModAux`. -/
theorem lucas_of_powMod {n a : ℕ} (hn : 1 < n) (hk : n - 1 < 2 ^ 256)
    (ha : powModAux 256 a (n - 1) n = 1)
    (hd : ∀ q : ℕ, q.Prime → q ∣ n - 1 → powModAux 256 a ((n - 1) / q) n ≠ 1) :
    n.Prime :=
  lucas_primality n ((a : ℕ) : ZMod n) (pow_eq_one hk ha) fun q hq hqd =>
    pow_ne_one hn (lt_of_le_of_lt (Nat.div_le_self _ _) hk) (hd q hq hqd)

/-- Peel the leading prime off a right-nested product of primes. -/
theorem dvdStep {q r s : ℕ} (hq : q.Prime) (hr : r.Prime) (h : q ∣ r * s) :
    q = r ∨ q ∣ s :=
  (hq.dvd_mul.mp h).imp (fun h => (Nat.prime_dvd_prime_iff_eq hq hr).mp h) id

end Pratt

/-- `2773320623`, a prime factor of `72106336199 - 1`. -/
private theorem prime_r : Nat.Prime 2773320623 := by
  refine Pratt.lucas_of_powMod (a := 5) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_
  intro q hq hqd
  rw [show 2773320623 - 1 =
    2 * (2437 * (569003 * 1))
    from by decide +kernel] at hqd
  repeat' rcases Pratt.dvdStep hq (by first | assumption | norm_num) hqd with rfl | hqd
  all_goals first
    | exact absurd (Nat.dvd_one.mp hqd) hq.ne_one
    | decide +kernel

/-- `72106336199`, a prime factor of `75445702479781427272750846543864801 - 1`. -/
private theorem prime_q : Nat.Prime 72106336199 := by
  refine Pratt.lucas_of_powMod (a := 7) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_
  intro q hq hqd
  have := prime_r
  rw [show 72106336199 - 1 =
    2 * (13 * (2773320623 * 1))
    from by decide +kernel] at hqd
  repeat' rcases Pratt.dvdStep hq (by first | assumption | norm_num) hqd with rfl | hqd
  all_goals first
    | exact absurd (Nat.dvd_one.mp hqd) hq.ne_one
    | decide +kernel

/-- `1919519569386763`, a prime factor of `75445702479781427272750846543864801 - 1`. -/
private theorem prime_k : Nat.Prime 1919519569386763 := by
  refine Pratt.lucas_of_powMod (a := 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_
  intro q hq hqd
  rw [show 1919519569386763 - 1 =
    2 * (3 * (7 * (19 * (47 * (47 * (127 * (8574133 * 1)))))))
    from by decide +kernel] at hqd
  repeat' rcases Pratt.dvdStep hq (by first | assumption | norm_num) hqd with rfl | hqd
  all_goals first
    | exact absurd (Nat.dvd_one.mp hqd) hq.ne_one
    | decide +kernel

/-- `31757755568855353`, a prime factor of
`74058212732561358302231226437062788676166966415465897661863160754340907 - 1`. -/
private theorem prime_m : Nat.Prime 31757755568855353 := by
  refine Pratt.lucas_of_powMod (a := 10) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_
  intro q hq hqd
  rw [show 31757755568855353 - 1 =
    2 * (2 * (2 * (3 * (31 * (107 * (223 * (4153 * (430751 * 1))))))))
    from by decide +kernel] at hqd
  repeat' rcases Pratt.dvdStep hq (by first | assumption | norm_num) hqd with rfl | hqd
  all_goals first
    | exact absurd (Nat.dvd_one.mp hqd) hq.ne_one
    | decide +kernel

/-- `75445702479781427272750846543864801`, a prime factor of
`74058212732561358302231226437062788676166966415465897661863160754340907 - 1`. -/
private theorem prime_n : Nat.Prime 75445702479781427272750846543864801 := by
  refine Pratt.lucas_of_powMod (a := 7) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_
  intro q hq hqd
  have := prime_q
  have := prime_k
  rw [show 75445702479781427272750846543864801 - 1 =
    2 * (2 * (2 * (2 * (2 * (3 * (3 * (5 * (5 * (75707 * (72106336199 * (1919519569386763 *
      (1))))))))))))
    from by decide +kernel] at hqd
  repeat' rcases Pratt.dvdStep hq (by first | assumption | norm_num) hqd with rfl | hqd
  all_goals first
    | exact absurd (Nat.dvd_one.mp hqd) hq.ne_one
    | decide +kernel

/-- `74058212732561358302231226437062788676166966415465897661863160754340907`, the large prime
factor of `p - 1`. -/
private theorem prime_l :
    Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 := by
  refine Pratt.lucas_of_powMod (a := 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_
  intro q hq hqd
  have := prime_m
  have := prime_n
  rw [show 74058212732561358302231226437062788676166966415465897661863160754340907 - 1 =
    2 * (3 * (353 * (57467 * (132049 * (1923133 * (31757755568855353 *
      (75445702479781427272750846543864801 * 1)))))))
    from by decide +kernel] at hqd
  repeat' rcases Pratt.dvdStep hq (by first | assumption | norm_num) hqd with rfl | hqd
  all_goals first
    | exact absurd (Nat.dvd_one.mp hqd) hq.ne_one
    | decide +kernel

/-- `2 ^ 255 - 19` is prime, by the Lucas test with witness `2`. -/
private theorem prime_p_aux : Nat.Prime (2 ^ 255 - 19) := by
  refine Pratt.lucas_of_powMod (a := 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_
  intro q hq hqd
  have := prime_l
  rw [show (2 ^ 255 - 19) - 1 =
    2 * (2 * (3 * (65147 *
      (74058212732561358302231226437062788676166966415465897661863160754340907 * 1))))
    from by decide +kernel] at hqd
  repeat' rcases Pratt.dvdStep hq (by first | assumption | norm_num) hqd with rfl | hqd
  all_goals first
    | exact absurd (Nat.dvd_one.mp hqd) hq.ne_one
    | decide +kernel

/-- The ed25519 field characteristic `p = 2 ^ 255 - 19` is prime.  This is the
theorem the `pPrime` axiom of `SSA.Projects.Firedancer.Ed25519` stands in for. -/
theorem prime_p : Nat.Prime p := prime_p_aux

instance : Fact (Nat.Prime p) := ⟨prime_p⟩
