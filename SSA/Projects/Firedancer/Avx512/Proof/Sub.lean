/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Fold
import SSA.Projects.Firedancer.Proof.Overflow

/-!
# The constant-operand macros a caller's block expands inline

Three of them, and two share a fold:

* `fd_r43x6_sub( x, one )` -- nine instructions: an `add` of the constant
  `p - 1`, then `fd_r43x6_fold_signed`. The subtraction rides in the constant
  -- there is no `sub` -- and so does the fold's bias, which is why the fold's
  own `add` at the end puts the bias back rather than the macro.
* `fd_r43x6_neg( x )` -- ten: a `sub` from `p`, the same constant one higher in
  lane 0, and then the same fold.
* `fd_r43x6_add_fast( x, one )` -- one instruction, no fold: `add_fast` is
  exact, its result carrying one more bit than its operands.

The two folded ones differ only in the vector they hand the fold, so
everything downstream of it is shared: `decode'_acpBiasVec`,
`extractLimbs_acpBiasVec` and `extractLimbs_acpBiasVec_bounds`, over the limbs
the fold sees. What is *not* shared is the denotation, because the two are
emitted differently -- `neg` puts the bias on first and flags its `add`
`nsw nuw` -- so `Fold.lean` carries the fold in both shapes and each macro
gets its own `denote_*Vec`.

Each macro's caller wants the same three things of the vector it leaves: the
denotation, the element, and the `u44` bound the next kernel takes as its
input contract.
-/

namespace Firedancer.Avx512
open InstCombine (LLVM)

theorem decode'_limbVecInt (l : Fin 6 → ℤ) (hb : ∀ k, R43x6.FitsLong (l k)) :
    R43x6.decode' (limbVecInt l) = decodeNat l := by
  rw [limbVecInt, decode'_lit, toInt_ofInt (hb 0), toInt_ofInt (hb 1), toInt_ofInt (hb 2),
    toInt_ofInt (hb 3), toInt_ofInt (hb 4), toInt_ofInt (hb 5)]
  simp only [decodeNat_eq]

theorem ofNat_eq_ofInt (n : ℕ) : (BitVec.ofNat 64 n) = BitVec.ofInt 64 (n : ℤ) := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- `BitVec.ofInt_add`'s counterpart; the core has the `add` and the `mul` but
not the `sub`. -/
theorem ofInt_sub64 (a b : ℤ) :
    BitVec.ofInt 64 a - BitVec.ofInt 64 b = BitVec.ofInt 64 (a - b) := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_sub, BitVec.toInt_ofInt, Int.sub_emod, Int.bmod]
  omega

/-- `p - 1`, in limbs, with the signed fold's bias already taken out: the
constant `fd_r43x6_sub( x, one )` adds before folding. -/
def subOneConst : Vector Nat 8 :=
  #v[8795933638636, 8796091973631, 8796091973631, 8796091973631, 8796091973631,
     1099510579199, 0, 0]

/-- The same, as limbs. -/
def subOneLimb : Fin R43x6.limbCount → ℤ :=
  R43x6.limbs6 8795933638636 8796091973631 8796091973631 8796091973631 8796091973631
    1099510579199

/-- What the constant is: `p - 1` once the bias is added back. -/
theorem decodeNat_subOneLimb :
    decodeNat (fun k => subOneLimb k + biasLimb k) = (p : ℤ) - 1 := by
  simp only [decodeNat_eq, subOneLimb, biasLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, p]
  norm_num

theorem extractLimbs_addSubOne (x : Vector (BitVec 64) 8)
    (hb : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k + subOneLimb k))
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 subOneConst[i.val]) k
      = R43x6.extractLimbs x k + subOneLimb k := by
  have h := hb k
  simp only [R43x6.extractLimbs, LimbRepresentations.toInts] at h ⊢
  fin_cases k <;>
    simp only [Vector.getElem_ofFn, subOneConst, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_castLE] <;>
    (conv_lhs => rw [← ofInt_toInt x[_], ofNat_eq_ofInt, ← BitVec.ofInt_add]) <;>
    rw [toInt_ofInt (by simpa [subOneLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five] using h)] <;>
    simp [subOneLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five]

theorem extractLimbs_limbVecInt (l : Fin R43x6.limbCount → ℤ)
    (hb : ∀ k, R43x6.FitsLong (l k)) (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (limbVecInt l) k = l k := by
  fin_cases k <;>
    simp only [R43x6.extractLimbs, LimbRepresentations.toInts, limbVecInt, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_castLE] <;>
    exact toInt_ofInt (hb _)

/-! ## What the signed fold leaves

`fd_r43x6_sub( x, one )` and `fd_r43x6_neg( x )` differ only in the vector
they hand `fd_r43x6_fold_signed`: an `add` of `p - 1` in one, a `sub` from `p`
in the other, both with the bias already taken out of the constant. Everything
downstream of the fold is these three lemmas, over the limbs `l` the fold sees.

`2 ^ 45` is the slack both need: `sub` arrives with limbs in `[0, 2 ^ 44)` plus
a constant below `2 ^ 43`, `neg` with a difference in `(-2 ^ 44, 2 ^ 44)`. -/

/-- The carry propagate's output fits a `long`, which is what reading it back
out of `limbVecInt` needs. -/
theorem acpBias_fitsLong {l : Fin R43x6.limbCount → ℤ}
    (hl : ∀ k, -(2 ^ 45) < l k ∧ l k < 2 ^ 45) (k : Fin R43x6.limbCount) :
    R43x6.FitsLong (acpLimb l k + biasLimb k) := by
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2
  have h3 := hl 3; have h4 := hl 4; have h5 := hl 5
  fin_cases k <;> simp only [Fin.zero_eta, acpLimb, biasLimb, R43x6.FitsLong] <;> omega

/-- **What the fold leaves, limb by limb.** -/
theorem extractLimbs_acpBiasVec {z : Vector (BitVec 64) 8}
    (hz : ∀ k, -(2 ^ 45) < R43x6.extractLimbs z k ∧ R43x6.extractLimbs z k < 2 ^ 45)
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (acpBiasVec z) k
      = acpLimb (R43x6.extractLimbs z) k + biasLimb k :=
  extractLimbs_limbVecInt _ (acpBias_fitsLong hz) k

/-- **... and it lands in `u44`**, the next kernel's input contract. The bias
is what makes the lower bound hold: a carry off a negative limb is negative,
and `2 ^ 20` swallows it. -/
theorem extractLimbs_acpBiasVec_bounds {z : Vector (BitVec 64) 8}
    (hz : ∀ k, -(2 ^ 45) < R43x6.extractLimbs z k ∧ R43x6.extractLimbs z k < 2 ^ 45)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs (acpBiasVec z) k
      ∧ R43x6.extractLimbs (acpBiasVec z) k < 2 ^ 44 := by
  have hw := extractLimbs_acpBiasVec hz k
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2
  have h3 := hz 3; have h4 := hz 4; have h5 := hz 5
  rw [hw]
  fin_cases k <;> simp only [Fin.zero_eta, acpLimb, biasLimb] <;> omega

/-- **... and the element it holds**: the fold moves a multiple of `p`, so the
value is the limbs it saw plus the bias. -/
theorem decode'_acpBiasVec {z : Vector (BitVec 64) 8}
    (hz : ∀ k, -(2 ^ 45) < R43x6.extractLimbs z k ∧ R43x6.extractLimbs z k < 2 ^ 45) :
    ((R43x6.decode' (acpBiasVec z) : ℤ) : ZMod p)
      = ((decodeNat (fun k => R43x6.extractLimbs z k + biasLimb k) : ℤ) : ZMod p) := by
  rw [acpBiasVec, decode'_limbVecInt _ (acpBias_fitsLong hz)]
  have hfold : (fun k => acpLimb (R43x6.extractLimbs z) k + biasLimb k)
      = foldSignedLimb (fun k => R43x6.extractLimbs z k + biasLimb k) := by
    funext k
    simp only [foldSignedLimb]
    congr 2
    funext j
    ring
  rw [hfold, decodeNat_foldSignedLimb_zmod]

/-- The vector `fd_r43x6_sub( x, one )` returns: the constant added, then the
signed fold's carry propagate with the bias put back. -/
def subOneVec (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  acpBiasVec (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 subOneConst[i.val])

/-- The limbs the fold sees, and their range: `x`'s plus the constant's, so
inside the `2 ^ 45` `decode'_acpBiasVec` asks for. -/
private theorem subOneAdd_limbs {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44) :
    (∀ k, R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 subOneConst[i.val]) k
      = R43x6.extractLimbs x k + subOneLimb k)
    ∧ (∀ k, -(2 ^ 45) < R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 subOneConst[i.val]) k
      ∧ R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 subOneConst[i.val]) k
        < 2 ^ 45) := by
  have hcb : ∀ k : Fin R43x6.limbCount, 0 ≤ subOneLimb k ∧ subOneLimb k < 2 ^ 43 := by
    intro k; fin_cases k <;> simp [subOneLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five] <;> norm_num
  have hfit : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k + subOneLimb k) := by
    intro k
    have h1 := hx k
    have h2 := hcb k
    simp only [R43x6.FitsLong]
    omega
  have hw := extractLimbs_addSubOne x hfit
  refine ⟨hw, fun k => ?_⟩
  have := hx k; have := hcb k; have := hw k
  omega

/-- **`fd_r43x6_sub( x, one )` subtracts one.** -/
theorem decode'_subOneVec {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44) :
    ((R43x6.decode' (subOneVec x) : ℤ) : ZMod p)
      = ((R43x6.decode' x : ℤ) : ZMod p) - 1 := by
  obtain ⟨hw, hz⟩ := subOneAdd_limbs hx
  rw [subOneVec, decode'_acpBiasVec hz]
  have hsplit : (fun k => R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 subOneConst[i.val]) k
        + biasLimb k)
      = fun k => R43x6.extractLimbs x k + (subOneLimb k + biasLimb k) := by
    funext k; rw [hw k]; ring
  rw [hsplit, decodeNat_add, decodeNat_subOneLimb,
    show decodeNat (R43x6.extractLimbs x) = R43x6.decode' x from by
      simpa [decodeNat] using R43x6.decodeLimbs_extractLimbs x]
  push_cast
  simp [ZMod.natCast_self]
  ring

/-- **`fd_r43x6_sub( x, one )` returns `u44` limbs** -- the input contract of
the next kernel, out of a `u44` input. -/
theorem extractLimbs_subOneVec {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs (subOneVec x) k
      ∧ R43x6.extractLimbs (subOneVec x) k < 2 ^ 44 :=
  extractLimbs_acpBiasVec_bounds (subOneAdd_limbs hx).2 k

/-- Lanes 6 and 7 of the result are zero: `limbVecInt`'s. -/
theorem subOneVec_six (x : Vector (BitVec 64) 8) : (subOneVec x)[6] = 0 := rfl
theorem subOneVec_seven (x : Vector (BitVec 64) 8) : (subOneVec x)[7] = 0 := rfl

/-- **The nine instructions of `fd_r43x6_sub( x, one )`**, in the shape
`denote_eval` leaves them: the constant add, then `fd_r43x6_fold_signed`. -/
theorem denote_subOneVec {x : Vector (BitVec 64) 8}
    {a77 a78 a79 a80 a81 a82 a83 a84 a85 : Vector (LLVM.IntW 64) 8}
    (h77 : a77 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add
      (x.map PoisonOr.value)[i.val] (toBitVecValue 64 subOneConst)[i.val])
    (h78 : a78 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a77[i.val]
      (toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
        8796093022207, 1099511627775, 0, 0])[i.val])
    (h79 : a79 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .ashr
      a77[i.val] (toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0])[i.val])
    (h80 : a80 = LLVM.Ty.vpermi2var a79 (toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8])
      (toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0]))
    (h81 : a81 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .mul
      a80[i.val] (toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18])[i.val])
    (h82 : a82 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a81[i.val] (toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0])[i.val])
    (h83 : a83 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a80[i.val] a78[i.val])
    (h84 : a84 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a83[i.val] a82[i.val])
    (h85 : a85 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a84[i.val]
      (toBitVecValue 64 #v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0])[i.val]) :
    a85 = (subOneVec x).map PoisonOr.value := by
  rw [denote_vec_add_const] at h77
  rw [h77] at h78 h79
  exact denote_acpBiasVec h78 h79 h80 h81 h82 h83 h84 h85

private theorem toInt_eq_toNat_of_bounds {a : BitVec 64} (h0 : 0 ≤ a.toInt)
    (h1 : a.toInt < 2 ^ 44) : a.toInt = (a.toNat : ℤ) := by
  have hlt : (2:ℕ) ^ 44 ≤ 2 ^ 62 := Nat.pow_le_pow_right (by omega) (by omega)
  have := toNat_lt_of_bounds hlt (by omega) h0
  exact BitVec.toInt_eq_toNat_of_lt (by omega)

/-- `decode'` and `vecValue` agree on a vector whose limbs read back as
naturals: the `ℤ` model of the signed macros and the `ℕ` model of the kernels,
on the overlap where both apply. -/
theorem decode'_cast_eq_vecValue (v : Vector (BitVec 64) 8)
    (h : ∀ k : Fin R43x6.limbCount,
      0 ≤ R43x6.extractLimbs v k ∧ R43x6.extractLimbs v k < 2 ^ 44) :
    ((R43x6.decode' v : ℤ) : ZMod p) = vecValue v := by
  have hnat : ∀ k : Fin R43x6.limbCount, R43x6.extractLimbs v k = (limbNat v k : ℤ) := by
    intro k
    have hb := h k
    fin_cases k <;>
      · simp only [R43x6.extractLimbs, LimbRepresentations.toInts, limbNat, Fin.val_castLE] at hb ⊢
        exact toInt_eq_toNat_of_bounds (by omega) (by omega)
  have hd : R43x6.decode' v = decodeNat (fun k => (limbNat v k : ℤ)) := by
    rw [← R43x6.decodeLimbs_extractLimbs v]
    simp only [decodeNat]
    congr 1
    funext k
    exact hnat k
  rw [hd, vecValue_eq_decodeNat]
  simp only [decodeNat_eq]
  push_cast
  ring

/-! ## `fd_r43x6_add_fast( x, one )`

One instruction, and the only constant macro left in the `u`/`v` chain: the
`+ 1` of `v = d·y² + 1`. No fold follows it -- `add_fast` is exact, its result
carrying one more bit than its operands. -/

/-- The constant `fd_r43x6_add_fast( x, one )` adds. -/
def addOneConst : Vector Nat 8 := #v[1, 0, 0, 0, 0, 0, 0, 0]

/-- The same, as limbs. -/
def addOneLimb : Fin R43x6.limbCount → ℤ := R43x6.limbs6 1 0 0 0 0 0

/-- The vector it returns. -/
def addOneVec (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 addOneConst[i.val]

theorem denote_addOneVec {x : Vector (BitVec 64) 8} {a : Vector (LLVM.IntW 64) 8}
    (h : a = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add
      (x.map PoisonOr.value)[i.val] (toBitVecValue 64 addOneConst)[i.val]) :
    a = (addOneVec x).map PoisonOr.value := by
  rw [h, denote_vec_add_const]
  rfl

theorem extractLimbs_addOneVec (x : Vector (BitVec 64) 8)
    (hb : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k + addOneLimb k))
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (addOneVec x) k = R43x6.extractLimbs x k + addOneLimb k := by
  have h := hb k
  simp only [R43x6.extractLimbs, LimbRepresentations.toInts] at h ⊢
  fin_cases k <;>
    simp only [addOneVec, Vector.getElem_ofFn, addOneConst, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_castLE] <;>
    (conv_lhs => rw [← ofInt_toInt x[_], ofNat_eq_ofInt, ← BitVec.ofInt_add]) <;>
    rw [toInt_ofInt (by simpa [addOneLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five] using h)] <;>
    simp [addOneLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five]

/-- **`fd_r43x6_add_fast( x, one )` adds one.** -/
theorem decode'_addOneVec {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44) :
    R43x6.decode' (addOneVec x) = R43x6.decode' x + 1 := by
  have hcb : ∀ j : Fin R43x6.limbCount, 0 ≤ addOneLimb j ∧ addOneLimb j ≤ 1 := by
    intro j; fin_cases j <;> simp [addOneLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five]
  have hb : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k + addOneLimb k) := by
    intro k
    have h1 := hx k
    have h2 := hcb k
    simp only [R43x6.FitsLong]
    omega
  have hl := extractLimbs_addOneVec x hb
  rw [← R43x6.decodeLimbs_extractLimbs, ← R43x6.decodeLimbs_extractLimbs,
    show R43x6.decodeLimbs (R43x6.extractLimbs (addOneVec x))
        = R43x6.decodeLimbs (fun k => R43x6.extractLimbs x k + addOneLimb k) from by
      congr 1; funext k; exact hl k]
  simp only [R43x6.decodeLimbs_eq, addOneLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five]
  ring

/-- ... and its limbs stay inside the next kernel's reach. -/
theorem extractLimbs_addOneVec_bounds {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs (addOneVec x) k
      ∧ R43x6.extractLimbs (addOneVec x) k < 2 ^ 45 := by
  have hcb : ∀ j : Fin R43x6.limbCount, 0 ≤ addOneLimb j ∧ addOneLimb j ≤ 1 := by
    intro j; fin_cases j <;> simp [addOneLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five]
  have hb : ∀ j, R43x6.FitsLong (R43x6.extractLimbs x j + addOneLimb j) := by
    intro j
    have h1 := hx j
    have h2 := hcb j
    simp only [R43x6.FitsLong]
    omega
  have := extractLimbs_addOneVec x hb k
  have h1 := hx k
  have h2 := hcb k
  omega

/-! ## `fd_r43x6_neg( x )`

Ten instructions: `p - x` -- the constant with the bias already taken out, as
in `fd_r43x6_sub` -- and then `fd_r43x6_fold_signed`.

The fold is the same eight instructions, but the *emission* differs from
`fd_r43x6_sub`'s in two ways, so it needs its own denotation lemma: the bias
goes on first rather than last, and its `add` carries `nsw nuw`. Everything
downstream -- the value, the `u44` bound, the zero lanes -- is
`decode'_acpBiasVec` and friends, shared with `sub`.

The flags are what makes this more than a reassociation. `%222` is a masked
lane, so below `2 ^ 43`, and the bias is below `2 ^ 28`: the sum is below
`2 ^ 44` and neither wrap can fire. `masked_add_no_wrap` is that argument. -/

/-- `p`, in limbs, with the signed fold's bias already taken out: the constant
`fd_r43x6_neg( x )` subtracts from. One more than `subOneConst` in lane 0,
which is exactly the `- 1`. -/
def negConst : Vector Nat 8 :=
  #v[8795933638637, 8796091973631, 8796091973631, 8796091973631, 8796091973631,
     1099510579199, 0, 0]

/-- The same, as limbs. -/
def negLimb : Fin R43x6.limbCount → ℤ :=
  R43x6.limbs6 8795933638637 8796091973631 8796091973631 8796091973631 8796091973631
    1099510579199

/-- What the constant is: `p` once the bias is added back. -/
theorem decodeNat_negLimb : decodeNat (fun k => negLimb k + biasLimb k) = (p : ℤ) := by
  simp only [decodeNat_eq, negLimb, biasLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, p]
  norm_num

/-- The vector `fd_r43x6_neg( x )` returns. -/
def negVec (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  acpBiasVec (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 negConst[i.val] - x[i.val])

theorem extractLimbs_subNegConst (x : Vector (BitVec 64) 8)
    (hb : ∀ k, R43x6.FitsLong (negLimb k - R43x6.extractLimbs x k))
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 negConst[i.val] - x[i.val]) k
      = negLimb k - R43x6.extractLimbs x k := by
  have h := hb k
  simp only [R43x6.extractLimbs, LimbRepresentations.toInts] at h ⊢
  fin_cases k <;>
    simp only [Vector.getElem_ofFn, negConst, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_castLE] <;>
    (conv_lhs => rw [← ofInt_toInt x[_], ofNat_eq_ofInt, ofInt_sub64]) <;>
    rw [toInt_ofInt (by simpa [negLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five] using h)] <;>
    simp [negLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five]

/-- The limbs the fold sees, and their range. Unlike `sub`'s these can be
*negative* -- the constant's lanes are around `2 ^ 43` and `x`'s reach
`2 ^ 44` -- which is the whole reason the fold is the signed one. -/
private theorem negSub_limbs {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44) :
    (∀ k, R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 negConst[i.val] - x[i.val]) k
      = negLimb k - R43x6.extractLimbs x k)
    ∧ (∀ k, -(2 ^ 45) < R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 negConst[i.val] - x[i.val]) k
      ∧ R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 negConst[i.val] - x[i.val]) k
        < 2 ^ 45) := by
  have hcb : ∀ k : Fin R43x6.limbCount, 0 ≤ negLimb k ∧ negLimb k < 2 ^ 44 := by
    intro k; fin_cases k <;> simp [negLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five] <;> norm_num
  have hfit : ∀ k, R43x6.FitsLong (negLimb k - R43x6.extractLimbs x k) := by
    intro k
    have h1 := hx k
    have h2 := hcb k
    simp only [R43x6.FitsLong]
    omega
  have hw := extractLimbs_subNegConst x hfit
  refine ⟨hw, fun k => ?_⟩
  have := hx k; have := hcb k; have := hw k
  omega

/-- **The ten instructions of `fd_r43x6_neg( x )`**, in the shape `denote_eval`
leaves them: the subtract, then the fold. `denote_subOneVec`'s twin. -/
theorem denote_negVec {x : Vector (BitVec 64) 8}
    {a225 a226 a227 a228 a229 a230 a231 a232 a233 : Vector (LLVM.IntW 64) 8}
    (h225 : a225 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .sub
      (toBitVecValue 64 negConst)[i.val] (x.map PoisonOr.value)[i.val])
    (h226 : a226 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a225[i.val]
      (toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
        8796093022207, 1099511627775, 0, 0])[i.val])
    (h227 : a227 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .ashr
      a225[i.val] (toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0])[i.val])
    (h228 : a228 = LLVM.Ty.vpermi2var a227 (toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8])
      (toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0]))
    (h229 : a229 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .mul
      a228[i.val] (toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18])[i.val])
    (h230 : a230 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a229[i.val] (toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0])[i.val])
    (h231 : a231 = Vector.ofFn fun i : Fin 8 =>
      InstCombine.binaryDenote (.add { nsw := true, nuw := true }) a226[i.val]
      (toBitVecValue 64
        #v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0])[i.val])
    (h232 : a232 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add
      a231[i.val] a228[i.val])
    (h233 : a233 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add
      a232[i.val] a230[i.val]) :
    a233 = (negVec x).map PoisonOr.value := by
  rw [denote_vec_sub_const] at h225
  rw [h225] at h226 h227
  exact denote_acpBiasVec_biasFirst h226 h227 h228 h229 h230 h231 h232 h233

/-- **`fd_r43x6_neg( x )` negates.** -/
theorem decode'_negVec {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44) :
    ((R43x6.decode' (negVec x) : ℤ) : ZMod p) = -((R43x6.decode' x : ℤ) : ZMod p) := by
  obtain ⟨hw, hz⟩ := negSub_limbs hx
  rw [negVec, decode'_acpBiasVec hz]
  have hsplit : (fun k => R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 negConst[i.val] - x[i.val]) k
        + biasLimb k)
      = fun k => (negLimb k + biasLimb k) - R43x6.extractLimbs x k := by
    funext k; rw [hw k]; ring
  rw [hsplit, decodeNat_sub, decodeNat_negLimb,
    show decodeNat (R43x6.extractLimbs x) = R43x6.decode' x from by
      simpa [decodeNat] using R43x6.decodeLimbs_extractLimbs x]
  push_cast
  simp [ZMod.natCast_self]

/-- **... and returns `u44` limbs**, the next kernel's input contract. -/
theorem extractLimbs_negVec {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs (negVec x) k ∧ R43x6.extractLimbs (negVec x) k < 2 ^ 44 :=
  extractLimbs_acpBiasVec_bounds (negSub_limbs hx).2 k

/-- Lanes 6 and 7 of the result are zero: `limbVecInt`'s. -/
theorem negVec_six (x : Vector (BitVec 64) 8) : (negVec x)[6] = 0 := rfl
theorem negVec_seven (x : Vector (BitVec 64) 8) : (negVec x)[7] = 0 := rfl

/-- The `add_fast` leaves the two ignored lanes as it found them. -/
theorem addOneVec_six {x : Vector (BitVec 64) 8} (h : x[6] = 0) : (addOneVec x)[6] = 0 := by
  simp [addOneVec, addOneConst, h]

theorem addOneVec_seven {x : Vector (BitVec 64) 8} (h : x[7] = 0) : (addOneVec x)[7] = 0 := by
  simp [addOneVec, addOneConst, h]

/-! ## The pre-bias vector

`fd_r43x6_sub_fast( vx2, u )` does not read `u`: the compiler folds `u`'s
bias-add into the subtraction's constant and subtracts the carry propagate's
output instead. These say what that vector holds. -/

/-- `decode'` of the carry propagate before the bias goes back on. -/
theorem decode'_acpVec {z : Vector (BitVec 64) 8}
    (hb : ∀ k, R43x6.FitsLong (acpLimb (R43x6.extractLimbs z) k)) :
    R43x6.decode' (acpVec z) = decodeNat (acpLimb (R43x6.extractLimbs z)) := by
  rw [acpVec, decode'_limbVecInt _ hb]

/-- ... and that the bias is all that separates it from the fold's output. -/
theorem decode'_acpBiasVec_eq {z : Vector (BitVec 64) 8}
    (hb : ∀ k, R43x6.FitsLong (acpLimb (R43x6.extractLimbs z) k))
    (hbb : ∀ k, R43x6.FitsLong (acpLimb (R43x6.extractLimbs z) k + biasLimb k)) :
    R43x6.decode' (acpBiasVec z) = R43x6.decode' (acpVec z) + decodeNat biasLimb := by
  rw [acpBiasVec, decode'_limbVecInt _ hbb, decode'_acpVec hb]
  simp only [decodeNat_eq, biasLimb]
  ring

/-! ## `fd_r43x6_sub_fast( x, y )` and `fd_r43x6_add_fast( x, y )`

Two lane-wise instructions each -- a `sub` and the constant `add` that puts the
element back above zero, or a bare `add` -- so they are peeled inline. What is
not inline is the constant: it is `p` with the signed fold's bias taken out,
because the vector the `sub` reads is the fold's pre-bias output. -/

/-- `%18` -- `p`, in limbs, with the fold's bias taken out. -/
def subFastConst : Vector Nat 8 :=
  #v[8795933638637, 8796091973631, 8796091973631, 8796091973631, 8796091973631,
     1099510579199, 0, 0]

/-- The same, as limbs. -/
def subFastLimb : Fin R43x6.limbCount → ℤ :=
  R43x6.limbs6 8795933638637 8796091973631 8796091973631 8796091973631 8796091973631
    1099510579199

/-- What the constant is: `p`, once the bias is added back. -/
theorem decodeNat_subFastLimb :
    decodeNat (fun k => subFastLimb k + biasLimb k) = (p : ℤ) := by
  simp only [decodeNat_eq, subFastLimb, biasLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, p]
  norm_num

/-- Subtracting lane-wise, on limbs. -/
theorem extractLimbs_sub (x y : Vector (BitVec 64) 8)
    (hb : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k - R43x6.extractLimbs y k))
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (Vector.ofFn fun i : Fin 8 => x[i.val] - y[i.val]) k
      = R43x6.extractLimbs x k - R43x6.extractLimbs y k := by
  have h := hb k
  simp only [R43x6.extractLimbs, LimbRepresentations.toInts] at h ⊢
  fin_cases k <;>
    simp only [Vector.getElem_ofFn, Fin.val_castLE] <;>
    (conv_lhs => rw [← ofInt_toInt x[_], ← ofInt_toInt y[_], ofInt_sub64]) <;>
    rw [toInt_ofInt (by simpa using h)] <;>
    simp

/-- ... and adding. -/
theorem extractLimbs_add (x y : Vector (BitVec 64) 8)
    (hb : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k + R43x6.extractLimbs y k))
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (Vector.ofFn fun i : Fin 8 => x[i.val] + y[i.val]) k
      = R43x6.extractLimbs x k + R43x6.extractLimbs y k := by
  have h := hb k
  simp only [R43x6.extractLimbs, LimbRepresentations.toInts] at h ⊢
  fin_cases k <;>
    simp only [Vector.getElem_ofFn, Fin.val_castLE] <;>
    (conv_lhs => rw [← ofInt_toInt x[_], ← ofInt_toInt y[_], ← BitVec.ofInt_add]) <;>
    rw [toInt_ofInt (by simpa using h)] <;>
    simp

/-- The constant add, on limbs: `extractLimbs_addOneVec` for any constant. -/
theorem extractLimbs_add_const (x : Vector (BitVec 64) 8) (c : Vector Nat 8)
    (cl : Fin R43x6.limbCount → ℤ)
    (hcl : ∀ k : Fin R43x6.limbCount,
      ((c[(k : ℕ)]'(Nat.lt_of_lt_of_le k.isLt (by decide)) : ℕ) : ℤ) = cl k)
    (hb : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k + cl k))
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 c[i.val]) k
      = R43x6.extractLimbs x k + cl k := by
  have h := hb k
  have hc := hcl k
  simp only [R43x6.extractLimbs, LimbRepresentations.toInts] at h hc ⊢
  fin_cases k <;>
    simp only [Vector.getElem_ofFn, Fin.val_castLE] at hc ⊢ <;>
    (conv_lhs => rw [← ofInt_toInt x[_], ofNat_eq_ofInt, ← BitVec.ofInt_add]) <;>
    rw [← hc] at h ⊢ <;>
    rw [toInt_ofInt (by simpa using h)] <;>
    simp

/-- The pre-bias vector of a `fd_r43x6_sub( x, one )`, named: the `sub_fast`
that reads it back writes it often enough to be worth a name. -/
def subOneAcp (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  acpVec (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 subOneConst[i.val])

/-- The `%80` of a `fd_r43x6_sub( x, one )`: the same eight instructions
stopped before the bias goes back on, which is the vector a later
`fd_r43x6_sub_fast` against the result actually reads. -/
theorem denote_subOneVec' {x : Vector (BitVec 64) 8}
    {a77 a78 a79 a80 a81 a82 a83 a84 : Vector (LLVM.IntW 64) 8}
    (h77 : a77 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add
      (x.map PoisonOr.value)[i.val] (toBitVecValue 64 subOneConst)[i.val])
    (h78 : a78 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a77[i.val]
      (toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
        8796093022207, 1099511627775, 0, 0])[i.val])
    (h79 : a79 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .ashr
      a77[i.val] (toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0])[i.val])
    (h80 : a80 = LLVM.Ty.vpermi2var a79 (toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8])
      (toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0]))
    (h81 : a81 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .mul
      a80[i.val] (toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18])[i.val])
    (h82 : a82 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      a81[i.val] (toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0])[i.val])
    (h83 : a83 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a80[i.val] a78[i.val])
    (h84 : a84 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .add a83[i.val] a82[i.val]) :
    a84 = (subOneAcp x).map PoisonOr.value := by
  rw [subOneAcp]
  rw [denote_vec_add_const] at h77
  rw [h77] at h78 h79
  exact denote_acpVec h78 h79 h80 h81 h82 h83 h84

/-! ### The two `fast` vectors -/

/-- `fd_r43x6_sub_fast( x, y )`, as the two instructions leave it. -/
def subFastVec (x y : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  Vector.ofFn fun i : Fin 8 => x[i.val] - y[i.val] + BitVec.ofNat 64 subFastConst[i.val]

/-- ... in the shape the `sub` and the `add` denote to. -/
theorem subFastVec_eq (x y : Vector (BitVec 64) 8) :
    (Vector.ofFn fun i : Fin 8 =>
      (Vector.ofFn fun j : Fin 8 => x[j.val] - y[j.val])[i.val]
        + BitVec.ofNat 64 subFastConst[i.val]) = subFastVec x y := by
  apply Vector.ext
  intro i hi
  simp [subFastVec]

/-- The carry propagate's limbs read back. -/
theorem extractLimbs_acpVec {z : Vector (BitVec 64) 8}
    (hb : ∀ k, R43x6.FitsLong (acpLimb (R43x6.extractLimbs z) k))
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (acpVec z) k = acpLimb (R43x6.extractLimbs z) k :=
  extractLimbs_limbVecInt _ hb k

/-- `sub_fast`'s limbs. -/
theorem extractLimbs_subFastVec {x y : Vector (BitVec 64) 8}
    (h1 : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k - R43x6.extractLimbs y k))
    (h2 : ∀ k, R43x6.FitsLong
      (R43x6.extractLimbs x k - R43x6.extractLimbs y k + subFastLimb k))
    (k : Fin R43x6.limbCount) :
    R43x6.extractLimbs (subFastVec x y) k
      = R43x6.extractLimbs x k - R43x6.extractLimbs y k + subFastLimb k := by
  have hsub := extractLimbs_sub x y h1
  have := extractLimbs_add_const (Vector.ofFn fun i : Fin 8 => x[i.val] - y[i.val])
    subFastConst subFastLimb (by intro j; fin_cases j <;> rfl)
    (by intro j; rw [hsub j]; exact h2 j) k
  rw [hsub k] at this
  rw [subFastVec, show (Vector.ofFn fun i : Fin 8 =>
      x[i.val] - y[i.val] + BitVec.ofNat 64 subFastConst[i.val])
    = Vector.ofFn fun i : Fin 8 =>
      (Vector.ofFn fun j : Fin 8 => x[j.val] - y[j.val])[i.val]
        + BitVec.ofNat 64 subFastConst[i.val] from by
    apply Vector.ext; intro i hi; simp]
  exact this

/-- **`fd_r43x6_sub_fast( x, y ) = x - y + p`**, with the bias the fold left in
`y` still to be accounted for by the caller. -/
theorem decode'_subFastVec {x y : Vector (BitVec 64) 8}
    (h1 : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k - R43x6.extractLimbs y k))
    (h2 : ∀ k, R43x6.FitsLong
      (R43x6.extractLimbs x k - R43x6.extractLimbs y k + subFastLimb k)) :
    R43x6.decode' (subFastVec x y)
      = R43x6.decode' x - R43x6.decode' y + decodeNat subFastLimb := by
  have hl := extractLimbs_subFastVec h1 h2
  rw [← R43x6.decodeLimbs_extractLimbs, ← R43x6.decodeLimbs_extractLimbs,
    ← R43x6.decodeLimbs_extractLimbs,
    show R43x6.decodeLimbs (R43x6.extractLimbs (subFastVec x y))
        = R43x6.decodeLimbs (fun k => R43x6.extractLimbs x k - R43x6.extractLimbs y k
          + subFastLimb k) from by congr 1; funext k; exact hl k]
  simp only [R43x6.decodeLimbs_eq, decodeNat, subFastLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five]
  ring

/-- **`fd_r43x6_add_fast( x, y ) = x + y`**. -/
theorem decode'_addVec {x y : Vector (BitVec 64) 8}
    (hb : ∀ k, R43x6.FitsLong (R43x6.extractLimbs x k + R43x6.extractLimbs y k)) :
    R43x6.decode' (Vector.ofFn fun i : Fin 8 => x[i.val] + y[i.val])
      = R43x6.decode' x + R43x6.decode' y := by
  have hl := extractLimbs_add x y hb
  rw [← R43x6.decodeLimbs_extractLimbs, ← R43x6.decodeLimbs_extractLimbs,
    ← R43x6.decodeLimbs_extractLimbs,
    show R43x6.decodeLimbs (R43x6.extractLimbs (Vector.ofFn fun i : Fin 8 => x[i.val] + y[i.val]))
        = R43x6.decodeLimbs (fun k => R43x6.extractLimbs x k + R43x6.extractLimbs y k) from by
      congr 1; funext k; exact hl k]
  simp only [R43x6.decodeLimbs_eq]
  ring

/-- The vector the `sub`'s constant add produces, bounded: the input of the
carry propagate. -/
theorem extractLimbs_addSubOne_bounds {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 subOneConst[i.val]) k
      ∧ R43x6.extractLimbs
        (Vector.ofFn fun i : Fin 8 => x[i.val] + BitVec.ofNat 64 subOneConst[i.val]) k
        < 2 ^ 45 := by
  have hcb : ∀ j : Fin R43x6.limbCount, 0 ≤ subOneLimb j ∧ subOneLimb j < 2 ^ 43 := by
    intro j; fin_cases j <;> simp [subOneLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five] <;> norm_num
  have hfit : ∀ j, R43x6.FitsLong (R43x6.extractLimbs x j + subOneLimb j) := by
    intro j
    have h1 := hx j
    have h2 := hcb j
    simp only [R43x6.FitsLong]
    omega
  have := extractLimbs_addSubOne x hfit k
  have h1 := hx k
  have h2 := hcb k
  omega

/-- ... and the carry propagate's own output. -/
theorem acpVec_bounds {z : Vector (BitVec 64) 8}
    (hz : ∀ k, 0 ≤ R43x6.extractLimbs z k ∧ R43x6.extractLimbs z k < 2 ^ 45)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs (acpVec z) k
      ∧ R43x6.extractLimbs (acpVec z) k < 2 ^ 44 := by
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2
  have h3 := hz 3; have h4 := hz 4; have h5 := hz 5
  have hfit : ∀ j, R43x6.FitsLong (acpLimb (R43x6.extractLimbs z) j) := by
    intro j
    fin_cases j <;> simp only [acpLimb, R43x6.FitsLong] <;> omega
  rw [extractLimbs_acpVec hfit]
  fin_cases k <;> simp only [acpLimb] <;> omega

/-- The `sub_fast` constant's limbs, for the caller's `omega`. -/
theorem subFastLimb_bounds (k : Fin R43x6.limbCount) :
    0 ≤ subFastLimb k ∧ subFastLimb k < 2 ^ 43 := by
  fin_cases k <;> simp [subFastLimb, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five] <;> norm_num

theorem subOneAcp_bounds {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs (subOneAcp x) k
      ∧ R43x6.extractLimbs (subOneAcp x) k < 2 ^ 44 :=
  acpVec_bounds (extractLimbs_addSubOne_bounds hx) k

/-! ### What the `sub_fast`/`add_fast` pair holds, in the field

`^bb0` of `fd_r43x6_ge_decode2` tests `v·x² ∓ u` against zero, and the two
vectors it tests are these. -/

private theorem toInt_eq_toNat62 {a : BitVec 64} (h0 : 0 ≤ a.toInt) (h1 : a.toInt < 2 ^ 62) :
    a.toInt = (a.toNat : ℤ) :=
  BitVec.toInt_eq_toNat_of_lt (by
    have := toNat_lt_of_bounds (le_refl (2 ^ 62)) (by omega) h0
    omega)

/-- `decode'_cast_eq_vecValue` at the widest bound the two readings share: a
limb below `2 ^ 62` reads the same as an `Int` and as a `Nat`. -/
theorem decode'_cast_eq_vecValue62 (v : Vector (BitVec 64) 8)
    (h : ∀ k : Fin R43x6.limbCount,
      0 ≤ R43x6.extractLimbs v k ∧ R43x6.extractLimbs v k < 2 ^ 62) :
    ((R43x6.decode' v : ℤ) : ZMod p) = vecValue v := by
  have hnat : ∀ k : Fin R43x6.limbCount, R43x6.extractLimbs v k = (limbNat v k : ℤ) := by
    intro k
    have hb := h k
    fin_cases k <;>
      · simp only [R43x6.extractLimbs, LimbRepresentations.toInts, limbNat, Fin.val_castLE] at hb ⊢
        exact toInt_eq_toNat62 (by omega) (by omega)
  have hd : R43x6.decode' v = decodeNat (fun k => (limbNat v k : ℤ)) := by
    rw [← R43x6.decodeLimbs_extractLimbs v]
    simp only [decodeNat]
    congr 1
    funext k
    exact hnat k
  rw [hd, vecValue_eq_decodeNat]
  simp only [decodeNat_eq]
  push_cast
  ring

/-- **`fd_r43x6_sub_fast( x, y )` where `y` is a `fd_r43x6_sub( ·, one )`'s
pre-bias vector**: the constant carries `p` less the bias, so the two cancel
and the difference of the two elements is what is left. -/
theorem decode'_subFast_subOneAcp {x y : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44)
    (hy : ∀ k, 0 ≤ R43x6.extractLimbs y k ∧ R43x6.extractLimbs y k < 2 ^ 44) :
    ((R43x6.decode' (subFastVec x (subOneAcp y)) : ℤ) : ZMod p)
      = ((R43x6.decode' x : ℤ) : ZMod p) - ((R43x6.decode' (subOneVec y) : ℤ) : ZMod p) := by
  have hacp := subOneAcp_bounds hy
  have h1 : ∀ k, R43x6.FitsLong
      (R43x6.extractLimbs x k - R43x6.extractLimbs (subOneAcp y) k) := by
    intro k; have := hx k; have := hacp k; simp only [R43x6.FitsLong]; omega
  have h2 : ∀ k, R43x6.FitsLong
      (R43x6.extractLimbs x k - R43x6.extractLimbs (subOneAcp y) k + subFastLimb k) := by
    intro k
    have := hx k; have := hacp k; have := subFastLimb_bounds k
    simp only [R43x6.FitsLong]; omega
  have hz := (subOneAdd_limbs hy).2
  have hb : ∀ j, R43x6.FitsLong (acpLimb (R43x6.extractLimbs
      (Vector.ofFn fun i : Fin 8 => y[i.val] + BitVec.ofNat 64 subOneConst[i.val])) j) := by
    have h0 := hz 0; have h1 := hz 1; have h2 := hz 2
    have h3 := hz 3; have h4 := hz 4; have h5 := hz 5
    intro j; fin_cases j <;> simp only [acpLimb, R43x6.FitsLong] <;> omega
  have hsplit : R43x6.decode' (subOneVec y)
      = R43x6.decode' (subOneAcp y) + decodeNat biasLimb := by
    rw [subOneVec, subOneAcp]; exact decode'_acpBiasVec_eq hb (acpBias_fitsLong hz)
  have hp : ((decodeNat subFastLimb + decodeNat biasLimb : ℤ) : ZMod p) = 0 := by
    rw [← decodeNat_add, decodeNat_subFastLimb]
    simp
  rw [decode'_subFastVec h1 h2, hsplit]
  push_cast at hp ⊢
  linear_combination hp

/-- **`fd_r43x6_add_fast( x, y )`**, in the field. -/
theorem decode'_addVec_cast {x y : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44)
    (hy : ∀ k, 0 ≤ R43x6.extractLimbs y k ∧ R43x6.extractLimbs y k < 2 ^ 44) :
    ((R43x6.decode' (Vector.ofFn fun i : Fin 8 => x[i.val] + y[i.val]) : ℤ) : ZMod p)
      = ((R43x6.decode' x : ℤ) : ZMod p) + ((R43x6.decode' y : ℤ) : ZMod p) := by
  rw [decode'_addVec (fun k => by
    have := hx k; have := hy k; simp only [R43x6.FitsLong]; omega)]
  push_cast
  ring

end Firedancer.Avx512
