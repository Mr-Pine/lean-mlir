/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-! Shared lane packing for the RIR and LLVM memory encodings.
Keep these root `BitVec` declarations in one module so both dialects can be imported together. -/

@[expose] public section

/-- Pack `n` lanes of width `we` into one bitvector, lane `0` in the low bits.

There is no `BitVec.cast` here: `width` multiplies as `width e * l` precisely so
that `we * (n+1)` reduces to `we * n + we`, which is the width `append` gives. -/
def _root_.BitVec.packLanes {we : Nat} : {n : Nat} → Vector (BitVec we) n → BitVec (we * n)
  | 0, _ => 0#(we * 0)
  | _ + 1, v => BitVec.packLanes v.tail ++ v[0]

/-- Lane `i` of a packed bitvector is the `i`-th input lane. -/
theorem _root_.BitVec.extractLsb'_packLanes {we : Nat} :
    ∀ {n : Nat} (v : Vector (BitVec we) n) (i : Nat) (h : i < n),
      (BitVec.packLanes v).extractLsb' (i * we) we = v[i]
  | 0, _, _, h => absurd h (by omega)
  | _ + 1, v, 0, _ => by
    simpa [BitVec.packLanes] using
      (BitVec.extractLsb'_append_eq_right (a := BitVec.packLanes v.tail) (b := v[0]))
  | n + 1, v, i + 1, h => by
    have hi : i < n := by omega
    have key :
      (BitVec.packLanes v).extractLsb' ((i + 1) * we) we =
        (BitVec.packLanes v.tail).extractLsb' (i * we) we := by
      have hunfold :
        (BitVec.packLanes v).extractLsb' ((i + 1) * we) we =
          (BitVec.packLanes v.tail ++ v[0]).extractLsb' ((i + 1) * we) we :=
        rfl
      rw [hunfold, show (i + 1) * we = i * we + we from Nat.succ_mul i we,
        BitVec.extractLsb'_append_eq_of_le (Nat.le_add_left we (i * we))]
      congr 1
      omega
    rw [key, BitVec.extractLsb'_packLanes v.tail i hi]
    simp [Nat.add_comm]

