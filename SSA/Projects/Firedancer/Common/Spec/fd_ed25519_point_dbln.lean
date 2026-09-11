/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Curve

/-!
# The doubling `fd_ed25519_point_dbln` repeats

Both backends double with the dedicated formulas of `dbl-2008-hwcd`
(Hisil–Wong–Carter–Dawson, §3.3), in the letters of the `FD_R43X6_GE_DBL`
comment. Neither reads `T`. That `dbl P` represents `2·P` is not proved: the
group law is not formalised (`Curve.lean`).
-/

namespace Ed25519

/-- One doubling. `T` is not read. -/
def Point.dbl (P : Point) : Point :=
  let A := P.X ^ 2
  let B := P.Y ^ 2
  let C := 2 * P.Z ^ 2
  let H := A + B
  let E := H - (P.X + P.Y) ^ 2
  let G := A - B
  let F := C + G
  ⟨E * F, G * H, F * G, E * H⟩

/-- How many doublings `fd_ed25519_point_dbln(r, a, n)` performs: the first is
unconditional, and the loop adds `n - 1` more when `n > 1` (signed). -/
def dblnCount (n : BitVec 32) : ℕ := if n.toInt ≤ 1 then 1 else n.toNat

/-- `2^n · P` as `fd_ed25519_point_dbln` computes it. -/
def Point.dbln (n : BitVec 32) (P : Point) : Point := Point.dbl^[dblnCount n] P

/-- `dbl` depends on `X`, `Y`, `Z` only. -/
theorem Point.dbl_congr {P Q : Point} (hX : P.X = Q.X) (hY : P.Y = Q.Y) (hZ : P.Z = Q.Z) :
    P.dbl = Q.dbl := by
  simp only [Point.dbl, hX, hY, hZ]

/-- ... so `dbln` does too. -/
theorem Point.dbln_congr {P Q : Point} (n : BitVec 32)
    (hX : P.X = Q.X) (hY : P.Y = Q.Y) (hZ : P.Z = Q.Z) : P.dbln n = Q.dbln n := by
  obtain ⟨k, hk⟩ : ∃ k, dblnCount n = k + 1 := by
    refine ⟨dblnCount n - 1, ?_⟩
    have := BitVec.toInt_eq_toNat_cond n
    simp only [dblnCount]; split <;> [rfl; (split at this <;> omega)]
  rw [Point.dbln, Point.dbln, hk, Function.iterate_succ_apply, Function.iterate_succ_apply,
    Point.dbl_congr hX hY hZ]

end Ed25519
