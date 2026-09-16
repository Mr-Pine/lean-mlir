/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_curve25519_scalar_wnaf
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel

/-!
# `fd_ed25519_double_scalar_mul_base`, both backends

What the two regions share: the ladder's closed form (`ladder_digitSum`), a digit's signed table
add (`addSigned_value`), the digits `wnaf` leaves (`wnaf_run`) and how they load, and the
loop-index arithmetic.
-/

namespace Firedancer.Common.DoubleScalarMulBase
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Finset Ed25519

/-! ## Values -/

/-- `E k` is the precomputed form of `(2k+1)·P`, for `k < K`. -/
def OddMultiples (E : ℕ → PrecomputedPoint) (P : Edwards.Point curve) (K : ℕ) : Prop :=
  ∀ k < K, ∃ (Q : Point) (hQ : Q.WellFormed), E k = Q.toPrecomputed ∧ Q.toAffine hQ = (2 * k + 1) • P

theorem BaseVals.oddMultiples {B : ℕ → PrecomputedPoint} {G : Point} {hG : G.WellFormed}
    (h : BaseVals B G hG) : OddMultiples B (G.toAffine hG) 128 := fun k hk =>
  (h k hk).elim fun Q h => h.elim fun hQ h => ⟨Q, hQ, h.2⟩

/-- `ai[k] = (2k+1)·A`, for `ai[0] = A` and `ai[k+1] = 2A + ai[k]`. -/
theorem oddMultiples_of_succ {A : Point} (hA : A.WellFormed) {E : ℕ → PrecomputedPoint}
    (h0 : E 0 = A.toPrecomputed)
    (hs : ∀ k, E (k + 1) = ((A.dbln 1#32).addPrecomputed (E k)).toPrecomputed) (K : ℕ) :
    OddMultiples E (A.toAffine hA) K := fun i _ => by
  induction i with
  | zero => exact ⟨A, hA, h0, by simp⟩
  | succ k ih =>
    obtain ⟨R, hR, hQ, hval⟩ := ih (by omega)
    have h2 := Point.wellFormed_dbln 1#32 hA
    refine ⟨(A.dbln 1#32).addPrecomputed R.toPrecomputed,
      Point.wellFormed_addPrecomputed h2 hR, by rw [hs, hQ], ?_⟩
    rw [Point.toAffine_addPrecomputed h2 hR, hval, Point.toAffine_dbln hA]
    simp only [show dblnCount 1#32 = 1 by decide, pow_one, ← add_nsmul]
    congr 1
    ring

/-- A digit's table index, `d >> 1` at 64 bits, as a natural. -/
theorem shift_toNat (d : BitVec 16) : (BitVec.setWidth 64 d >>> 1).toNat = d.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by have := d.isLt; omega)]

/-- `T` plus entry `|d| >> 1` of `E`, negated for `d < 0`; `T` itself at `d = 0`. -/
def addSigned (T : Point) (E : ℕ → PrecomputedPoint) (d : BitVec 16) : Point :=
  if 0#16 <ₛ d then T.addPrecomputed (E (BitVec.setWidth 64 d >>> 1).toNat)
  else if d <ₛ 0#16 then T.addPrecomputed (E (BitVec.setWidth 64 (-d) >>> 1).toNat).neg
  else T

/-- **A digit's add**: `T + d·P`, for `d` zero or odd below `2K` and `E` the odd multiples of `P`. -/
theorem addSigned_value {T : Point} (hT : T.WellFormed) {E : ℕ → PrecomputedPoint}
    {P : Edwards.Point curve} {K : ℕ} (hE : OddMultiples E P K) {d : BitVec 16}
    (hd : d = 0 ∨ d.toInt % 2 = 1) (hb : |d.toInt| < 2 * K) :
    ∃ h : (addSigned T E d).WellFormed, (addSigned T E d).toAffine h = T.toAffine hT + d.toInt • P := by
  rcases hd with h | h
  · subst h
    exact ⟨hT, by simp [addSigned]⟩
  have hc := BitVec.toInt_eq_toNat_cond d
  have := d.isLt
  rw [abs_lt] at hb
  by_cases hp : (0#16 <ₛ d) = true
  · have hgt : 0 < d.toInt := by simpa [BitVec.slt] using hp
    obtain ⟨Q, hQ, hEQ, hval⟩ := hE (d.toNat / 2) (by split_ifs at hc <;> omega)
    rw [addSigned, if_pos hp, shift_toNat, hEQ]
    refine ⟨Point.wellFormed_addPrecomputed hT hQ, ?_⟩
    rw [Point.toAffine_addPrecomputed hT hQ, hval, ← natCast_zsmul]
    congr 2
    split_ifs at hc <;> omega
  by_cases hn : (d <ₛ 0#16) = true
  · have hlt : d.toInt < 0 := by simpa [BitVec.slt] using hn
    have hneg : (-d).toNat = 65536 - d.toNat := by
      rw [BitVec.toNat_neg]; split_ifs at hc <;> omega
    obtain ⟨Q, hQ, hEQ, hval⟩ := hE ((-d).toNat / 2) (by rw [hneg]; split_ifs at hc <;> omega)
    rw [addSigned, if_neg hp, if_pos hn, shift_toNat, hEQ]
    refine ⟨Point.wellFormed_addPrecomputed_neg hT hQ, ?_⟩
    rw [Point.toAffine_addPrecomputed_neg hT hQ, hval, ← natCast_zsmul, sub_eq_add_neg,
      ← neg_zsmul]
    congr 2
    rw [hneg]
    split_ifs at hc <;> omega
  · have h0 : d = 0 := by simp only [Bool.not_eq_true] at hp hn; bv_decide
    simp [h0] at h

theorem toAffine_zero : Point.zero.toAffine Point.wellFormed_zero = 0 :=
  Edwards.Point.ext (by simp [Point.toAffine, Point.x, Point.zero])
    (by simp [Point.toAffine, Point.y, Point.zero])

/-! ## The ladder -/

/-- One ladder iteration at position `j`: double `X`, add `d₁ⱼ·A` and `d₂ⱼ·G`. -/
def ladderStep (A G X : Edwards.Point curve) (w₁ w₂ : BitVec 4096) (j : ℕ) : Edwards.Point curve :=
  2 • X + (Wnaf.slot w₁ j).toInt • A + (Wnaf.slot w₂ j).toInt • G

/-- The ladder from `X` over positions `j` down to `0`:
`2^(j+1)·X + ∑ i ≤ j, 2^i·(d₁ᵢ·A + d₂ᵢ·G)`. -/
def ladder (A G X : Edwards.Point curve) (w₁ w₂ : BitVec 4096) (j : ℕ) : Edwards.Point curve :=
  2 ^ (j + 1) • X + ∑ i ∈ range (j + 1),
    (((Wnaf.slot w₁ i).toInt * 2 ^ i) • A + ((Wnaf.slot w₂ i).toInt * 2 ^ i) • G)

section Ladder
variable {A G X : Edwards.Point curve} {w₁ w₂ : BitVec 4096}

theorem ladder_zero : ladder A G X w₁ w₂ 0 = ladderStep A G X w₁ w₂ 0 := by
  simp [ladder, ladderStep, add_assoc]

theorem ladder_succ (j : ℕ) :
    ladder A G X w₁ w₂ (j + 1) = ladder A G (ladderStep A G X w₁ w₂ (j + 1)) w₁ w₂ j := by
  simp only [ladder, ladderStep]
  rw [Finset.sum_range_succ _ (j + 1)]
  generalize (∑ x ∈ range (j + 1), (((Wnaf.slot w₁ x).toInt * 2 ^ x) • A
    + ((Wnaf.slot w₂ x).toInt * 2 ^ x) • G) : Edwards.Point curve) = S
  rw [smul_add, smul_add, smul_smul, ← pow_succ, mul_smul, mul_smul,
    smul_comm (2 ^ (j + 1)) (Wnaf.slot w₁ (j + 1)).toInt A,
    smul_comm (2 ^ (j + 1)) (Wnaf.slot w₂ (j + 1)).toInt G]
  simp only [← natCast_zsmul, Nat.cast_pow, Nat.cast_ofNat]
  abel

/-- Zero digits above `i` add nothing. -/
theorem ladder_skip {i : ℕ} (hi : i < 256)
    (hz : ∀ k, i < k → k ≤ 255 → Wnaf.slot w₁ k = 0 ∧ Wnaf.slot w₂ k = 0) :
    ladder A G 0 w₁ w₂ i = ladder A G 0 w₁ w₂ 255 := by
  obtain ⟨j, hj⟩ : ∃ j, 256 = (i + 1) + j := ⟨256 - i - 1, by omega⟩
  simp only [ladder, smul_zero, zero_add, show 255 + 1 = 256 from rfl, hj,
    Finset.sum_range_add _ _ j, left_eq_add]
  refine Finset.sum_eq_zero fun x hx => ?_
  have := hz (i + 1 + x) (by omega) (by simp at hx; omega)
  simp [this.1, this.2]

theorem ladder_all_zero (hz : ∀ k ≤ 255, Wnaf.slot w₁ k = 0 ∧ Wnaf.slot w₂ k = 0) :
    ladder A G 0 w₁ w₂ 255 = 0 := by
  simp only [ladder, smul_zero, zero_add]
  refine Finset.sum_eq_zero fun x hx => ?_
  have := hz x (by simp at hx; omega)
  simp [this.1, this.2]

/-- `∑ i < K, dᵢ·2^i` over `w`'s digits is wnaf's `digitSum`. -/
theorem sum_slot_eq_digitSum (w : BitVec 4096) (K : ℕ) :
    ∑ i ∈ range K, (Wnaf.slot w i).toInt * 2 ^ i = digitSum w K := by
  induction K with
  | zero => rfl
  | succ K ih => rw [Finset.sum_range_succ, ih]; rfl

/-- The ladder's value from `0`: the digit sums' multiples of `A` and `G`. -/
theorem ladder_digitSum :
    ladder A G 0 w₁ w₂ 255 = digitSum w₁ 256 • A + digitSum w₂ 256 • G := by
  simp only [ladder, smul_zero, zero_add, Finset.sum_add_distrib, ← Finset.sum_smul,
    sum_slot_eq_digitSum]

end Ladder

/-! ## Digits -/

/-- Every entry of `w` in `[-B, B]`. -/
def Digits (w : BitVec 4096) (B : BitVec 16) : Prop :=
  ∀ j < 256, (-B).sle (Wnaf.slot w j) ∧ (Wnaf.slot w j).sle B

/-- `w`'s digits as the ladder's value needs them: zero or odd, of absolute value at most `B`. -/
def DigitVals (w : BitVec 4096) (B : ℤ) : Prop :=
  ∀ j < 256, (Wnaf.slot w j = 0 ∨ (Wnaf.slot w j).toInt % 2 = 1) ∧ |(Wnaf.slot w j).toInt| ≤ B

theorem DigitVals.digits15 {w : BitVec 4096} (h : DigitVals w 15) : Digits w 15#16 := fun j hj => by
  have hb := abs_le.mp (h j hj).2
  simp only [BitVec.sle, decide_eq_true_eq]
  exact ⟨by rw [show (-15#16).toInt = -15 by decide]; omega,
    by rw [show (15#16).toInt = 15 by decide]; omega⟩

theorem DigitVals.digits255 {w : BitVec 4096} (h : DigitVals w 255) : Digits w 255#16 :=
  fun j hj => by
  have hb := abs_le.mp (h j hj).2
  simp only [BitVec.sle, decide_eq_true_eq]
  exact ⟨by rw [show (-255#16).toInt = -255 by decide]; omega,
    by rw [show (255#16).toInt = 255 by decide]; omega⟩

/-- A positive digit in `[-15, 15]` halves into the table. -/
theorem idx_pos {d : BitVec 16} (hlo : (-15#16).sle d) (hhi : d.sle 15#16)
    (h : (0#16 <ₛ d) = true) : (BitVec.setWidth 64 d >>> 1).toNat < 8 := by
  have : BitVec.setWidth 64 d >>> 1 < 8#64 := by bv_decide
  exact this

/-- A nonpositive digit in `[-15, 15]`, negated, halves into the table. -/
theorem idx_neg {d : BitVec 16} (hlo : (-15#16).sle d) (hhi : d.sle 15#16)
    (h : ¬(0#16 <ₛ d) = true) : (BitVec.setWidth 64 (-d) >>> 1).toNat < 8 := by
  have : BitVec.setWidth 64 (-d) >>> 1 < 8#64 := by bv_decide
  exact this

/-- A positive digit in `[-255, 255]` halves into the base-point table. -/
theorem idx_pos_tbl {d : BitVec 16} (hlo : (-255#16).sle d) (hhi : d.sle 255#16)
    (h : (0#16 <ₛ d) = true) : (BitVec.setWidth 64 d >>> 1).toNat < 128 := by
  have : BitVec.setWidth 64 d >>> 1 < 128#64 := by bv_decide
  exact this

/-- A negative digit in `[-255, 255]`, negated, halves into the base-point table. -/
theorem idx_neg_tbl {d : BitVec 16} (hlo : (-255#16).sle d) (hhi : d.sle 255#16)
    (h : (d <ₛ 0#16) = true) : (BitVec.setWidth 64 (-d) >>> 1).toNat < 128 := by
  have : BitVec.setWidth 64 (-d) >>> 1 < 128#64 := by bv_decide
  exact this

/-- The sign test's branch bit. -/
theorem ofBool_sgt_zero {d : BitVec 16} :
    BitVec.ofBool (LLVM.icmp' LLVM.IntPred.sgt d 0#16) = 1 ↔ (0#16 <ₛ d) = true := by
  cases h : 0#16 <ₛ d <;> simp [LLVM.icmp', h]

theorem ofBool_slt_zero {d : BitVec 16} :
    BitVec.ofBool (LLVM.icmp' LLVM.IntPred.slt d 0#16) = 1 ↔ (d <ₛ 0#16) = true := by
  cases h : d <ₛ 0#16 <;> simp [LLVM.icmp', h]

/-! ## Loop indices -/

/-- `j + -1` under `nsw`, for `1 ≤ j`. -/
theorem add_neg_one64 {j : Nat} (h1 : 1 ≤ j) (h : j < 2 ^ 63) :
    LLVM.add (PoisonOr.value (BitVec.ofNat 64 j)) (PoisonOr.value (BitVec.ofInt 64 (-1)))
      { nsw := true } = PoisonOr.value (BitVec.ofNat 64 (j - 1)) := by
  simp only [LLVM.add, LLVM.add?, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  rw [if_neg (by simp [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond]; omega)]
  exact congrArg PoisonOr.value (BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, show BitVec.ofInt 64 (-1) = BitVec.ofNat 64 18446744073709551615 from rfl,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega))

/-- `j >s 0` for `1 ≤ j < 2^63`. -/
theorem icmp_sgt_zero64 {j : Nat} (h1 : 1 ≤ j) (h : j < 2 ^ 63) :
    LLVM.icmp .sgt (PoisonOr.value (BitVec.ofNat 64 j)) (PoisonOr.value 0#64)
      = PoisonOr.value 1#1 := by
  simp only [LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind]
  congr 2
  have : (0#64 <ₛ BitVec.ofNat 64 j) = true := by
    simp only [BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega
  simp [this]

/-- `k + 1` under `nsw nuw`, for `k < 2^63`. -/
theorem add_one64 {k : Nat} (h : k + 1 < 2 ^ 63) :
    LLVM.add (PoisonOr.value (BitVec.ofNat 64 k)) (PoisonOr.value 1#64) { nsw := true, nuw := true }
      = PoisonOr.value (BitVec.ofNat 64 (k + 1)) := by
  simp only [LLVM.add, LLVM.add?, PoisonOr.value_bind]
  rw [if_neg (by simp [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond]; omega),
    if_neg (by simp [BitVec.uaddOverflow]; omega)]
  exact congrArg PoisonOr.value (BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- `zext` of a 32-bit natural to 64 bits. -/
theorem setWidth_ofNat {i : Nat} (h : i < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 i) = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `i + -1` under `nsw`, for `1 ≤ i`. -/
theorem add_neg_one32 {i : Nat} (h1 : 1 ≤ i) (h : i < 2 ^ 31) :
    LLVM.add (PoisonOr.value (BitVec.ofNat 32 i)) (PoisonOr.value (BitVec.ofInt 32 (-1)))
      { nsw := true } = PoisonOr.value (BitVec.ofNat 32 (i - 1)) := by
  simp only [LLVM.add, LLVM.add?, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  rw [if_neg (by simp [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond]; omega)]
  -- `congr`/`simp` on `ofInt (-1)` hit the kernel's recursion limit
  exact congrArg PoisonOr.value (BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, show BitVec.ofInt 32 (-1) = BitVec.ofNat 32 4294967295 from rfl,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega))

/-- `i >s -1` for `i ≤ 255`. -/
theorem slt_neg_one32 {i : Nat} (hi : i ≤ 255) : (4294967295#32 <ₛ BitVec.ofNat 32 i) = true := by
  have h1 : (4294967295#32).toInt = -1 := by decide
  have h2 : (BitVec.ofNat 32 i).toInt = i := by
    rw [BitVec.toInt_eq_toNat_cond]; simp; split_ifs <;> omega
  simp only [BitVec.slt, decide_eq_true_eq, h1, h2]
  omega

/-! ## Tables and slides -/

/-- `p + n·k`, entry `k` of a table of `n`-byte entries. -/
def entryPtr (n : ℕ) (p : Pointer) (k : ℕ) : Pointer :=
  { p with offset := p.offset + BitVec.ofNat 64 (n * k) }

@[simp] theorem entryPtr_id (n : ℕ) (p : Pointer) (k : ℕ) : (entryPtr n p k).id = p.id := rfl

@[simp] theorem entryPtr_zero (n : ℕ) (p : Pointer) : entryPtr n p 0 = p := by
  simp [entryPtr]

/-- `getelementptr` into a table of `n`-byte entries: entry `x`. -/
theorem gep_entryPtr (n : ℕ) (p : Pointer) (x : BitVec 64) :
    gep (PoisonOr.value p) n 0 (PoisonOr.value x) = PoisonOr.value (entryPtr n p x.toNat) := by
  simp only [gep, ptradd, LLVM.mul, LLVM.add, LLVM.const?, LLVM.mul?, LLVM.add?, entryPtr,
    PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  rw [show (BitVec.ofInt 64 ((0 : Nat) : Int)) = 0#64 from rfl, BitVec.ofInt_natCast]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
    Nat.mod_mod]
  rw [Nat.mul_comm, Nat.mod_mul_mod]

/-- Entry `k < K`'s byte offset in a table that does not wrap. -/
theorem entryPtr_offset_toNat {n K : ℕ} {p : Pointer} (hoff : p.offset.toNat + K * n ≤ 2 ^ 64)
    {k : ℕ} (hk : k < K) : (entryPtr n p k).offset.toNat = p.offset.toNat + n * k := by
  simp only [entryPtr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using p.offset.isLt
  have : n * k + n ≤ K * n := by
    have := Nat.mul_le_mul_right n (show k + 1 ≤ K from hk)
    rwa [Nat.succ_mul, Nat.mul_comm k] at this
  rw [Nat.mod_eq_of_lt (a := n * k) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The 256 entries at `p` are `w`. -/
def SlidesAt (m : MemoryState) (p : Pointer) (w : BitVec 4096) : Prop :=
  p.offset.toNat + 512 ≤ 2 ^ 64 ∧ ∃ blk : LiveBlock, m.live? p.id = some blk ∧
    p.offsetInBits + 4096 ≤ blk.lengthInBits ∧ blk.bytes.extractLsb' p.offsetInBits 4096 = w

theorem SlidesAt.of_live?_eq {m m' : MemoryState} {p : Pointer} {w : BitVec 4096}
    (h : m'.live? p.id = m.live? p.id) (hs : SlidesAt m p w) : SlidesAt m' p w :=
  ⟨hs.1, hs.2.elim fun blk ⟨hb, hl, hw⟩ => ⟨blk, h.trans hb, hl, hw⟩⟩

/-- Splicing `w` at `p` leaves `w` there. -/
theorem SlidesAt.splice {m : MemoryState} {p : Pointer} (h : IsSlidesPtr m p)
    (w : BitVec 4096) : SlidesAt (m.splice p w) p w :=
  h.1.elim fun blk ⟨hblk, hlen⟩ => by
    simp only [LiveBlock.lengthInBits] at hlen
    exact ⟨h.2, _, splicedLive m p blk (by simp [MemoryState.live?, hblk]) w,
      by simp only [LiveBlock.lengthInBits]; omega, extractLsb'_spliceBits _ _ _ (by omega)⟩

/-- Entry `k` of the 4096 bits at `off`. -/
theorem extract_slot {n : Nat} (b : BitVec n) (off : Nat) {k : Nat} (hk : k < 256) :
    b.extractLsb' (off + 16 * k) 16 = Wnaf.slot (b.extractLsb' off 4096) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Wnaf.slot, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show 16 * k + i < 4096 by omega]
  congr 1; omega

/-- Loading entry `k` of `SlidesAt … w` reads `slot w k`. -/
theorem run_load_slides {m : MemoryState} {p : Pointer} {w : BitVec 4096} (hs : SlidesAt m p w)
    {k : Nat} (hk : k < 256) :
    (load (.value (Wnaf.slotPtr p k)) (.bitvec (.concrete 16))).run m
      = .value (.value (Wnaf.slot w k), m) :=
  hs.2.elim fun blk ⟨hb, hl, hw⟩ => by
    rw [run_load (p := Wnaf.slotPtr p k) (getElem?_of_live? hb) (by
      simp only [LLVM.Ty.width]; rw [Wnaf.slotPtr_offsetInBits hs.1 hk]; omega)]
    simp only [LLVM.Ty.unflatten, LLVM.Ty.width]
    rw [Wnaf.slotPtr_offsetInBits hs.1 hk, extract_slot _ _ hk, hw]

/-- `peel_load_slides hs, hk, hp` runs the `load` of slide entry `k`: `hs : SlidesAt …`,
`hk : k < 256`, `hp` the pointer operand's `hv`. -/
macro "peel_load_slides " hs:term ", " hk:term ", " hp:term : tactic =>
  `(tactic| rw [BlockCom.run_denote_var_of_value (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, $hp:term]
      rw [run_liftM (Common.DoubleScalarMulBase.run_load_slides $hs $hk)]; rfl)])

/-- `fd_curve25519_scalar_wnaf` returns, writing some `w` at `slides` whose digits are zero or odd,
within `±B` for `bits = 4, 8`, and sum to `n`'s low 255 bits. -/
theorem wnaf_run (slides n : Pointer) (bits : BitVec 32) (B : ℤ) (s : GlobalState) (hs : s.WF)
    (hsl : IsSlidesPtr s.mem slides) (hn : IsByteBufPtr s.mem n)
    (hbits : bits = 4#32 ∧ B = 15 ∨ bits = 8#32 ∧ B = 255) :
    ∃ s' : GlobalState, StateT.run (runFunction (fd_curve25519_scalar_wnaf.denote
        (Ctxt.Valuation.ofHVector [.value bits, .value n, .value slides]ₕ))) s = .value ([]ₕ, s')
      ∧ ∃ w : BitVec (256 * 16), ({ s with mem := s.mem.splice slides w } : GlobalState) ≈ s'
        ∧ DigitVals w B
        ∧ (slides.id ≠ n.id → digitSum w 256 = ((readBuf hn).toNat % 2 ^ 255 : ℕ)) :=
  (fd_curve25519_scalar_wnaf_conforms slides n bits s hs hsl hn
    (by rcases hbits with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)).elim
    fun s' h => h.elim fun hrun h => h.elim fun w h =>
    have hw := h.1; have hd := h.2.1; have hsum := h.2.2
    ⟨s', hrun, w, hw.symm, fun j hj => by
      obtain ⟨h1, h2⟩ := hd j hj
      refine ⟨h1, ?_⟩
      have hx : Wnaf.slot w j = 0 → (Wnaf.slot w j).toInt = 0 := fun h => h ▸ rfl
      change (Wnaf.slot w j = 0 ∨ (Wnaf.slot w j).toInt % 2 = 1) at h1
      change (Wnaf.slot w j).toInt.natAbs ≤ 2 ^ bits.toNat at h2
      rw [abs_le]
      rcases hbits with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [show (4#32).toNat = 4 from rfl, show (8#32).toNat = 8 from rfl] at h2 <;>
        rcases h1 with h1 | h1 <;> [have := hx h1; skip; have := hx h1; skip] <;> omega,
      fun hne => hsum (by rcases hbits with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide) hne⟩

end Firedancer.Common.DoubleScalarMulBase
