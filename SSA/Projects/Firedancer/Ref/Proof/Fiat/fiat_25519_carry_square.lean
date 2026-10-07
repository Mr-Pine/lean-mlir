module

public import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_carry_square
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_carry_square
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
public import SSA.Projects.Firedancer.Ref.Proof.Limb
public import SSA.Projects.Firedancer.Ref.Proof.CarryChain

@[expose] public section


namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! ### Widening helpers for the doubled and `38`-scaled operands

`fiat_25519_carry_mul` only ever widens a limb or a limb times `19`; squaring
also widens a limb doubled by an `shl` and a limb times `38`. -/

private theorem toNat_zx38 {n : ℕ} (h : n * 38 < 2 ^ 64) :
    (BitVec.zeroExtend 128 (BitVec.ofNat 64 n * 38#64)).toNat = n * 38 := by
  rw [BitVec.toNat_setWidth_of_le (by omega), BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (38#64).toNat = 38 from by decide]
  omega

private theorem toNat_zx2 {n : ℕ} (h : n * 2 < 2 ^ 64) :
    (BitVec.zeroExtend 128 (BitVec.ofNat 64 n <<< 1#64)).toNat = n * 2 := by
  rw [BitVec.toNat_setWidth_of_le (by omega),
    show BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 n <<< (1 : ℕ) from rfl,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega

private theorem toNat_zx_mul_zx38 {m n : ℕ} (hm : m < 2 ^ 64) (hn : n * 38 < 2 ^ 64) :
    (BitVec.zeroExtend 128 (BitVec.ofNat 64 m)
      * BitVec.zeroExtend 128 (BitVec.ofNat 64 n * 38#64)).toNat = m * (n * 38) := by
  rw [toNat_mul128 (by rw [toNat_zx hm]; omega) (by rw [toNat_zx38 hn]; omega),
    toNat_zx hm, toNat_zx38 hn]

private theorem toNat_zx_mul_zx2 {m n : ℕ} (hm : m < 2 ^ 64) (hn : n * 2 < 2 ^ 64) :
    (BitVec.zeroExtend 128 (BitVec.ofNat 64 m)
      * BitVec.zeroExtend 128 (BitVec.ofNat 64 n <<< 1#64)).toNat = m * (n * 2) := by
  rw [toNat_mul128 (by rw [toNat_zx hm]; omega) (by rw [toNat_zx2 hn]; omega),
    toNat_zx hm, toNat_zx2 hn]

/-- A column of three products, left-associated as the region accumulates it. -/
private theorem toNat_col3 {u₁ u₂ u₃ : BitVec 128} {n₁ n₂ n₃ : ℕ}
    (h₁ : u₁.toNat = n₁) (h₂ : u₂.toNat = n₂) (h₃ : u₃.toNat = n₃)
    (hb : n₁ + n₂ + n₃ < 2 ^ 128) : (u₁ + u₂ + u₃).toNat = n₁ + n₂ + n₃ := by
  rw [toNat_add (by rw [toNat_add (by omega), h₁, h₂]; omega), toNat_add (by omega), h₁, h₂, h₃]

private lemma limb_mul38_le {x y : ℕ} (hx : x ≤ 0x18000000000000) (hy : y ≤ 0x18000000000000) :
    x * (y * 19 * 2) ≤ 342 * 2 ^ 102 :=
  calc x * (y * 19 * 2) = x * y * 38 := by ring
    _ ≤ 9 * 2 ^ 102 * 38 := Nat.mul_le_mul_right _ (limb_mul_le hx hy)
    _ = 342 * 2 ^ 102 := by ring

private lemma limb_mul2_le {x y : ℕ} (hx : x ≤ 0x18000000000000) (hy : y ≤ 0x18000000000000) :
    x * (y * 2) ≤ 18 * 2 ^ 102 :=
  calc x * (y * 2) = x * y * 2 := by ring
    _ ≤ 9 * 2 ^ 102 * 2 := Nat.mul_le_mul_right _ (limb_mul_le hx hy)
    _ = 18 * 2 ^ 102 := by ring

/-- The same per-column worst cases `product_columns_le` gives, reached with one
`38`-scaled product where the multiply has two `19`-scaled ones. -/
private lemma carry_square_columns_le (a : Fin 5 → ℕ) (ha : ∀ i, a i ≤ 0x18000000000000) :
    a 0 * a 0 + (a 1 * (a 4 * 19 * 2) + a 2 * (a 3 * 19 * 2)) ≤ 693 * 2 ^ 102
      ∧ a 0 * (a 1 * 2) + (a 2 * (a 4 * 19 * 2) + a 3 * (a 3 * 19)) ≤ 531 * 2 ^ 102
      ∧ a 0 * (a 2 * 2) + (a 1 * a 1 + a 3 * (a 4 * 19 * 2)) ≤ 369 * 2 ^ 102
      ∧ a 0 * (a 3 * 2) + (a 1 * (a 2 * 2) + a 4 * (a 4 * 19)) ≤ 207 * 2 ^ 102
      ∧ a 0 * (a 4 * 2) + (a 1 * (a 3 * 2) + a 2 * a 2) ≤ 45 * 2 ^ 102 := by
  have m : ∀ i j, a i * a j ≤ 9 * 2 ^ 102 := fun i j => limb_mul_le (ha i) (ha j)
  have m38 : ∀ i j, a i * (a j * 19 * 2) ≤ 342 * 2 ^ 102 := fun i j => limb_mul38_le (ha i) (ha j)
  have m2 : ∀ i j, a i * (a j * 2) ≤ 18 * 2 ^ 102 := fun i j => limb_mul2_le (ha i) (ha j)
  have m19 : ∀ i j, a i * (a j * 19) ≤ 171 * 2 ^ 102 := fun i j => limb_mul19_le (ha i) (ha j)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have k1 := m 0 0; have k2 := m38 1 4; have k3 := m38 2 3; omega
  · have k1 := m2 0 1; have k2 := m38 2 4; have k3 := m19 3 3; omega
  · have k1 := m2 0 2; have k2 := m 1 1; have k3 := m38 3 4; omega
  · have k1 := m2 0 3; have k2 := m2 1 2; have k3 := m19 4 4; omega
  · have k1 := m2 0 4; have k2 := m2 1 3; have k3 := m 2 2; omega

/-- Squaring is the general multiply with both operands equal. The columns are
`carry_product_repr`'s, regrouped as the region accumulates them -- the C's
`x24`, then `x30` down to `x27`. -/
lemma carry_product_repr_self_eq (a : Fin 5 → ℕ) :
    carry_product_repr a a = carry_chain
      (a 0 * a 0 + (a 1 * (a 4 * 19 * 2) + a 2 * (a 3 * 19 * 2)))
      (a 0 * (a 1 * 2) + (a 2 * (a 4 * 19 * 2) + a 3 * (a 3 * 19)))
      (a 0 * (a 2 * 2) + (a 1 * a 1 + a 3 * (a 4 * 19 * 2)))
      (a 0 * (a 3 * 2) + (a 1 * (a 2 * 2) + a 4 * (a 4 * 19)))
      (a 0 * (a 4 * 2) + (a 1 * (a 3 * 2) + a 2 * a 2)) := by
  rw [carry_product_repr_eq]
  congr 1 <;> ring

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 20000 in
theorem fiat_25519_carry_square_conforms (o p: Pointer) (s: GlobalState)
  (hs : s.WF)
  (ho : IsFieldElemPtr s.mem o)
  (hp : IsFieldElemPtr s.mem p)
  (hplimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x18000000000000) :
  fiat_25519_carry_square_spec o p s ho hp := by
    simp only [fiat_25519_carry_square_spec, Cfg.denote]

    obtain ⟨pblk, hpblk, hplen⟩ := id hp.left
    obtain ⟨pinput, hpinput⟩ := exists_limbs hpblk
    let output := carry_product_repr pinput pinput
    let outputBV := BitVec.ofNat 64 ∘ output

    have hpb : ∀ i, pinput i ≤ 0x18000000000000 := fun i => hplimb i _ (hpinput i)
    have hcb : ∀ i, output i ≤ 0x8000000000000 := carry_product_bounds pinput pinput hpb hpb
    have hlimb : ∀ i : Fin 5, (outputBV i).toNat = output i := by
      intro i
      have hi : output i < 2 ^ 64 := by have := hcb i; omega
      show (BitVec.ofNat 64 (output i)).toNat = output i
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

    refine ⟨outputBV, ?value, ?bounds, ?exec, ?zero⟩

    case value =>
      have hread : readFieldElem? o (s.mem.splice o (packLimbs outputBV))
          = some (decodeFieldElem fun i => (outputBV i).toNat) := by
        rw [readFieldElem?_splice _ ho.left]
        simp only [extractLsb'_packLimbs]
      have hpread : readFieldElem? p s.mem = some (decodeFieldElem pinput) := by
        simp [readFieldElem?, hpinput, vec_eq]
      rw [readFieldElem_eq_of hread, readFieldElem_eq_of hpread,
        show (fun i : Fin 5 => (outputBV i).toNat) = output from funext hlimb]
      exact carry_product_eq_value pinput pinput hpb hpb
    case bounds =>
      intro i
      simp only [readLimb, limbReadbackPack s.mem o outputBV ho.left i, Option.get_some, hlimb]
      exact hcb i
    case zero =>
      intro hz
      have h0 : ∀ i, output i = 0 := fun i => by
        have := (limbReadbackPack s.mem o outputBV ho.left i).symm.trans (hz i)
        rw [hlimb i] at this
        exact Option.some.inj this
      have hp0 := carry_product_repr_eq_zero pinput pinput hpb hpb h0
      exact fun i => (hpinput i).trans (by rw [hp0.elim id id i])

    case exec =>
    obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState,
        m = ((((s.mem.splice o (outputBV 0)).splice (o.withOffset 8) (outputBV 1)).splice
              (o.withOffset 16) (outputBV 2)).splice (o.withOffset 24) (outputBV 3)).splice
              (o.withOffset 32) (outputBV 4) := ⟨_, rfl⟩
    refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
    case equiv =>
      have hnone : ∀ (b : BlockId), s.alloc.nextFreeBlock ≤ b.id → outMem.live? b = none := by
        rw [houtMem]
        exact fun b hb => live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none
          (live?_splice_eq_none (live?_splice_eq_none (hs b hb)))))
      refine GlobalState.Equiv.trans ?_ (GlobalState.Equiv.symm
        (killFrom_equiv_of_none (s := s) (m := outMem) hnone))
      rw [houtMem]
      exact GlobalState.Equiv.symm
        (splice5_equiv (outputBV 0) (outputBV 1) (outputBV 2) (outputBV 3) (outputBV 4) ho)

    denote_step_all v 6
    denote_eval v 0 6
    simp only [LLVM.const?] at hv0 hv1 hv2 hv3 hv4 hv5 hv6
    subst hv0 hv1 hv2 hv3 hv4 hv5 hv6

    have hpoff : ∀ (i : Fin 5) (off : BitVec 64), off.toNat = 8 * i.toNat →
        (p.withOffset off).offsetInBits = p.offsetInBits + 64 * i.toNat :=
      fun i _ ho => limbOffsetInBits hp.right (by have : i.toNat < 5 := i.isLt; omega) ho
    have hpbits : ∀ (i : Fin 5) (off : ℕ), off = p.offsetInBits + 64 * i.toNat →
        pblk.bytes.extractLsb' off 64 = BitVec.ofNat 64 (pinput i) := limbBits hpblk hpinput

    peel_gep_limb 4, p, hp.left, s, p
    peel_limb 4, p₄, hp₄, pblk, hpblk, pl
    rw [show pl₄ = BitVec.ofNat 64 (pinput 4) from hpl₄.trans (hpbits 4 _ (hpoff 4 32 (by simp)))]
    clear hpl₄ pl₄

    denote_step_all v 11
    peel_gep_limb 3, p, hp.left, s, p
    peel_limb 3, p₃, hp₃, pblk, hpblk, pl
    rw [show pl₃ = BitVec.ofNat 64 (pinput 3) from hpl₃.trans (hpbits 3 _ (hpoff 3 24 (by simp)))]
    clear hpl₃ pl₃

    denote_step_all v 16
    peel_gep_limb 2, p, hp.left, s, p
    peel_limb 2, p₂, hp₂, pblk, hpblk, pl
    rw [show pl₂ = BitVec.ofNat 64 (pinput 2) from hpl₂.trans (hpbits 2 _ (hpoff 2 16 (by simp)))]
    clear hpl₂ pl₂

    denote_step_all v 19
    peel_gep_limb 1, p, hp.left, s, p
    peel_limb 1, p₁, hp₁, pblk, hpblk, pl
    rw [show pl₁ = BitVec.ofNat 64 (pinput 1) from hpl₁.trans (hpbits 1 _ (hpoff 1 8 (by simp)))]
    clear hpl₁ pl₁

    denote_step_all v 42
    peel_limb 0, p, hp.left, pblk, hpblk, pl
    rw [show pl₀ = BitVec.ofNat 64 (pinput 0) from hpl₀.trans (hpbits 0 _ (by simp))]
    clear hpl₀ pl₀

    denote_step_all v 93
    denote_eval v 9 93

    have key : v89 = PoisonOr.value (outputBV 0) ∧ v92 = PoisonOr.value (outputBV 1)
        ∧ v93 = PoisonOr.value (outputBV 2) ∧ v79 = PoisonOr.value (outputBV 3)
        ∧ v85 = PoisonOr.value (outputBV 4) := by
      have h64 : ∀ i, pinput i < 2 ^ 64 := fun i => by have := hpb i; omega
      have h19 : ∀ i, pinput i * 19 < 2 ^ 64 := fun i => by have := hpb i; omega
      have h38 : ∀ i, pinput i * 38 < 2 ^ 64 := fun i => by have := hpb i; omega
      have h2 : ∀ i, pinput i * 2 < 2 ^ 64 := fun i => by have := hpb i; omega

      -- %9-%22: the scaled and doubled limbs, the C's `x1`-`x8`. These stay as
      -- expressions rather than atoms: the widening lemmas below match on the
      -- `* 19#64` / `* 38#64` / `<<< 1#64` a product's operand is built from.
      eval_llvm 9
      eval_llvm 10
      eval_llvm 11
      eval_llvm 14
      eval_llvm 15
      eval_llvm 16
      eval_llvm 19
      eval_llvm 22

      -- %23-%51: the fifteen products, `x9`-`x23`
      eval_llvm 23
      eval_llvm 24
      eval_llvm 25 as x9
      eval_llvm 26
      eval_llvm 27
      eval_llvm 28 as x10
      eval_llvm 29
      eval_llvm 30 as x11
      eval_llvm 31
      eval_llvm 32 as x12
      eval_llvm 33
      eval_llvm 34 as x13
      eval_llvm 35 as x14
      eval_llvm 36
      eval_llvm 37 as x15
      eval_llvm 38
      eval_llvm 39 as x16
      eval_llvm 40
      eval_llvm 41 as x17
      eval_llvm 42 as x18
      eval_llvm 44
      eval_llvm 45
      eval_llvm 46 as x19
      eval_llvm 47 as x20
      eval_llvm 48 as x21
      eval_llvm 49
      eval_llvm 50 as x22
      eval_llvm 51 as x23

      -- %52-%64: the five columns, `x24` and `x27`-`x30`, plus `x25`/`x26`
      eval_llvm 52
      eval_llvm 53 as x24
      eval_llvm 54 as x25
      eval_llvm 55
      eval_llvm 56 as x26
      eval_llvm 57
      eval_llvm 58 as x27
      eval_llvm 59
      eval_llvm 60 as x28
      eval_llvm 61
      eval_llvm 62 as x29
      eval_llvm 63
      eval_llvm 64 as x30

      -- %65-%85: the carry chain, `x31`-`x42`
      eval_llvm 65
      eval_llvm 66 as x31
      eval_llvm 67 as x32
      eval_llvm 68
      eval_llvm 69 as x33
      eval_llvm 70
      eval_llvm 71 as x34
      eval_llvm 72 as x35
      eval_llvm 73
      eval_llvm 74 as x36
      eval_llvm 75
      eval_llvm 76 as x37
      eval_llvm 77 as x38
      eval_llvm 78
      eval_llvm 79 as x39
      eval_llvm 80
      eval_llvm 81 as x40
      eval_llvm 82
      eval_llvm 83 as x41
      eval_llvm 84
      eval_llvm 85 as x42

      -- %86-%89: the top carry, folded back into limb 0
      eval_llvm 86 as x43
      eval_llvm 87 as x44
      eval_llvm 88 as x45
      eval_llvm 89 as x46

      -- each product in the form `carry_product_repr_self_eq` names it
      have n9 : x9.toNat = pinput 4 * (pinput 4 * 19) := by
        rw [← hx9, toNat_zx19_mul_zx (h19 4) (h64 4)]; ring
      have n10 : x10.toNat = pinput 3 * (pinput 4 * 19 * 2) := by
        rw [← hx10, toNat_zx_mul_zx38 (h64 3) (h38 4)]; ring
      have n11 : x11.toNat = pinput 3 * (pinput 3 * 19) := by
        rw [← hx11, toNat_zx19_mul_zx (h19 3) (h64 3)]; ring
      have n12 : x12.toNat = pinput 2 * (pinput 4 * 19 * 2) := by
        rw [← hx12, toNat_zx_mul_zx38 (h64 2) (h38 4)]; ring
      have n13 : x13.toNat = pinput 2 * (pinput 3 * 19 * 2) := by
        rw [← hx13, toNat_zx_mul_zx38 (h64 2) (h38 3)]; ring
      have n14 : x14.toNat = pinput 2 * pinput 2 := by
        rw [← hx14, toNat_zx_mul_zx (h64 2) (h64 2)]
      have n15 : x15.toNat = pinput 1 * (pinput 4 * 19 * 2) := by
        rw [← hx15, toNat_zx_mul_zx38 (h64 1) (h38 4)]; ring
      have n16 : x16.toNat = pinput 1 * (pinput 3 * 2) := by
        rw [← hx16, toNat_zx_mul_zx2 (h64 1) (h2 3)]
      have n17 : x17.toNat = pinput 1 * (pinput 2 * 2) := by
        rw [← hx17, toNat_zx_mul_zx2 (h64 1) (h2 2)]
      have n18 : x18.toNat = pinput 1 * pinput 1 := by
        rw [← hx18, toNat_zx_mul_zx (h64 1) (h64 1)]
      have n19 : x19.toNat = pinput 0 * (pinput 4 * 2) := by
        rw [← hx19, toNat_zx_mul_zx2 (h64 0) (h2 4)]
      have n20 : x20.toNat = pinput 0 * (pinput 3 * 2) := by
        rw [← hx20, toNat_zx_mul_zx2 (h64 0) (h2 3)]
      have n21 : x21.toNat = pinput 0 * (pinput 2 * 2) := by
        rw [← hx21, toNat_zx_mul_zx2 (h64 0) (h2 2)]
      have n22 : x22.toNat = pinput 0 * (pinput 1 * 2) := by
        rw [← hx22, toNat_zx_mul_zx2 (h64 0) (h2 1)]
      have n23 : x23.toNat = pinput 0 * pinput 0 := by
        rw [← hx23, toNat_zx_mul_zx (h64 0) (h64 0)]

      -- product bounds, so the column sums stay linear for omega
      have m : ∀ i j, pinput i * pinput j ≤ 9 * 2 ^ 102 :=
        fun i j => limb_mul_le (hpb i) (hpb j)
      have m19 : ∀ i j, pinput i * (pinput j * 19) ≤ 171 * 2 ^ 102 :=
        fun i j => limb_mul19_le (hpb i) (hpb j)
      have m38 : ∀ i j, pinput i * (pinput j * 19 * 2) ≤ 342 * 2 ^ 102 :=
        fun i j => limb_mul38_le (hpb i) (hpb j)
      have m2 : ∀ i j, pinput i * (pinput j * 2) ≤ 18 * 2 ^ 102 :=
        fun i j => limb_mul2_le (hpb i) (hpb j)
      have q00 := m 0 0; have q11 := m 1 1; have q22 := m 2 2
      have r44 := m19 4 4; have r33 := m19 3 3
      have t14 := m38 1 4; have t23 := m38 2 3; have t24 := m38 2 4; have t34 := m38 3 4
      have u01 := m2 0 1; have u02 := m2 0 2; have u03 := m2 0 3; have u04 := m2 0 4
      have u12 := m2 1 2; have u13 := m2 1 3

      -- the five columns, grouped as `carry_product_repr_self_eq` names them
      have N0 : x24.toNat = pinput 0 * pinput 0
          + (pinput 1 * (pinput 4 * 19 * 2) + pinput 2 * (pinput 3 * 19 * 2)) := by
        rw [← hx24, toNat_col3 n15 n13 n23 (by omega)]; ring
      have N1 : x30.toNat = pinput 0 * (pinput 1 * 2)
          + (pinput 2 * (pinput 4 * 19 * 2) + pinput 3 * (pinput 3 * 19)) := by
        rw [← hx30, toNat_col3 n12 n11 n22 (by omega)]; ring
      have N2 : x29.toNat = pinput 0 * (pinput 2 * 2)
          + (pinput 1 * pinput 1 + pinput 3 * (pinput 4 * 19 * 2)) := by
        rw [← hx29, toNat_col3 n18 n10 n21 (by omega)]; ring
      have N3 : x28.toNat = pinput 0 * (pinput 3 * 2)
          + (pinput 1 * (pinput 2 * 2) + pinput 4 * (pinput 4 * 19)) := by
        rw [← hx28, toNat_col3 n17 n9 n20 (by omega)]; ring
      have N4 : x27.toNat = pinput 0 * (pinput 4 * 2)
          + (pinput 1 * (pinput 3 * 2) + pinput 2 * pinput 2) := by
        rw [← hx27, toNat_col3 n16 n14 n19 (by omega)]; ring
      obtain ⟨B0, B1, B2, B3, B4⟩ := carry_square_columns_le pinput hpb
      rw [← N0] at B0; rw [← N1] at B1; rw [← N2] at B2; rw [← N3] at B3; rw [← N4] at B4

      have n25 : x25.toNat = x24.toNat / 2 ^ 51 := by rw [← hx25]; exact shift_toNat128 x24
      have b25 : x25.toNat ≤ 693 * 2 ^ 51 := by rw [n25]; omega
      have n26 : x26.toNat = x24.toNat % 2 ^ 51 := by rw [← hx26]; exact trunc_mask_toNat x24
      have b26 : x26.toNat < 2 ^ 51 := by rw [n26]; omega
      have n31 : x31.toNat = x25.toNat + x30.toNat := by
        rw [← hx31, toNat_add (by rw [mask64_toNat]; omega), mask64_toNat,
          Nat.mod_eq_of_lt (by omega)]
        omega
      have b31 : x31.toNat ≤ 531 * 2 ^ 102 + 693 * 2 ^ 51 := by rw [n31]; omega
      have n32 : x32.toNat = x31.toNat / 2 ^ 51 := by rw [← hx32]; exact shift_toNat128 x31
      have b32 : x32.toNat ≤ 531 * 2 ^ 51 + 693 := by rw [n32]; omega
      have n33 : x33.toNat = x31.toNat % 2 ^ 51 := by rw [← hx33]; exact trunc_mask_toNat x31
      have b33 : x33.toNat < 2 ^ 51 := by rw [n33]; omega
      have n34 : x34.toNat = x32.toNat + x29.toNat := by
        rw [← hx34, toNat_add (by rw [mask64_toNat]; omega), mask64_toNat,
          Nat.mod_eq_of_lt (by omega)]
        omega
      have b34 : x34.toNat ≤ 369 * 2 ^ 102 + 531 * 2 ^ 51 + 693 := by rw [n34]; omega
      have n35 : x35.toNat = x34.toNat / 2 ^ 51 := by rw [← hx35]; exact shift_toNat128 x34
      have b35 : x35.toNat ≤ 369 * 2 ^ 51 + 532 := by rw [n35]; omega
      have n36 : x36.toNat = x34.toNat % 2 ^ 51 := by rw [← hx36]; exact trunc_mask_toNat x34
      have b36 : x36.toNat < 2 ^ 51 := by rw [n36]; omega
      have n37 : x37.toNat = x35.toNat + x28.toNat := by
        rw [← hx37, toNat_add (by rw [mask64_toNat]; omega), mask64_toNat,
          Nat.mod_eq_of_lt (by omega)]
        omega
      have b37 : x37.toNat ≤ 207 * 2 ^ 102 + 369 * 2 ^ 51 + 532 := by rw [n37]; omega
      have n38 : x38.toNat = x37.toNat / 2 ^ 51 := by rw [← hx38]; exact shift_toNat128 x37
      have b38 : x38.toNat ≤ 207 * 2 ^ 51 + 370 := by rw [n38]; omega
      have n39 : x39.toNat = x37.toNat % 2 ^ 51 := by rw [← hx39]; exact trunc_mask_toNat x37
      have n40 : x40.toNat = x38.toNat + x27.toNat := by
        rw [← hx40, toNat_add (by rw [mask64_toNat]; omega), mask64_toNat,
          Nat.mod_eq_of_lt (by omega)]
        omega
      have b40 : x40.toNat ≤ 45 * 2 ^ 102 + 207 * 2 ^ 51 + 370 := by rw [n40]; omega
      have n41 : x41.toNat = x40.toNat / 2 ^ 51 := by
        rw [← hx41, trunc_shift_toNat, Nat.mod_eq_of_lt (by omega)]
      have b41 : x41.toNat ≤ 45 * 2 ^ 51 + 208 := by rw [n41]; omega
      have n42 : x42.toNat = x40.toNat % 2 ^ 51 := by rw [← hx42]; exact trunc_mask_toNat x40
      have n43 : x43.toNat = x41.toNat * 19 := by rw [← hx43]; exact mul19_toNat (by omega)
      have b43 : x43.toNat ≤ 855 * 2 ^ 51 + 3952 := by rw [n43]; omega
      have n44 : x44.toNat = x26.toNat + x43.toNat := by
        rw [← hx44, toNat_add (by omega)]; omega
      have b44 : x44.toNat ≤ 856 * 2 ^ 51 + 3952 := by rw [n44]; omega
      have n45 : x45.toNat = x44.toNat / 2 ^ 51 := by rw [← hx45]; exact shift_toNat x44
      have b45 : x45.toNat ≤ 856 := by rw [n45]; omega
      have n46 : x46.toNat = x44.toNat % 2 ^ 51 := by rw [← hx46]; exact mask_toNat x44

      -- `%90`/`%93` carry `nsw, nuw`, so their bounds come first
      have hno47s : x45.saddOverflow x33 = false := saddOverflow_eq_false (by omega)
      have hno47u : x45.uaddOverflow x33 = false := uaddOverflow_eq_false (by omega)
      eval_llvm 90 [hno47s, hno47u] as x47
      eval_llvm 91 as x48
      eval_llvm 92 as x49
      have n47 : x47.toNat = x45.toNat + x33.toNat := by
        rw [← hx47, toNat_add (by omega)]
      have n48 : x48.toNat = x47.toNat / 2 ^ 51 := by rw [← hx48]; exact shift_toNat x47
      have b48 : x48.toNat ≤ 1 := by rw [n48]; omega
      have n49 : x49.toNat = x47.toNat % 2 ^ 51 := by rw [← hx49]; exact mask_toNat x47
      have hno50s : x48.saddOverflow x36 = false := saddOverflow_eq_false (by omega)
      have hno50u : x48.uaddOverflow x36 = false := uaddOverflow_eq_false (by omega)
      eval_llvm 93 [hno50s, hno50u] as x50
      have n50 : x50.toNat = x48.toNat + x36.toNat := by
        rw [← hx50, toNat_add (by omega)]

      -- the registers the stores consume are the chain's limbs
      have t48 : x48.toNat % 2 ^ 8 = x48.toNat := Nat.mod_eq_of_lt (by omega)
      have hout : output = ![x46.toNat, x49.toNat, x50.toNat, x39.toNat, x42.toNat] := by
        show carry_product_repr pinput pinput = _
        rw [carry_product_repr_self_eq, ← N0, ← N1, ← N2, ← N3, ← N4]
        simp only [carry_chain]
        rw [← n25, ← n26, ← n31, ← n32, ← n33, ← n34, ← n35, ← n36, ← n37, ← n38, ← n39,
          ← n40, ← n41, ← n42, ← n43, ← n44, ← n45, ← n46, ← n47, ← n48, t48, ← n49, ← n50]
      have hbv : ∀ (u : BitVec 64) (i : Fin 5), u.toNat = output i → u = outputBV i :=
        fun _ _ h => eq_ofNat_of_toNat h
      exact ⟨hv89.trans (congrArg _ (hbv _ 0 (by simp [hout]))),
        hv92.trans (congrArg _ (hbv _ 1 (by simp [hout]))),
        hv93.trans (congrArg _ (hbv _ 2 (by simp [hout]))),
        hv79.trans (congrArg _ (hbv _ 3 (by simp [hout]))),
        hv85.trans (congrArg _ (hbv _ 4 (by simp [hout])))⟩

    obtain ⟨k0, k1, k2, k3, k4⟩ := key
    rw [k0, k1, k2, k3, k4]

    store_limbs outputBV, o, ho.left, s

    simp only [BlockCom.denote_term, Terminator.denote_ret, houtMem,
      hs₁, hs₂, hs₃, hs₄, o₁, o₂, o₃, o₄, simp_denote, simp_sllvm]

end Firedancer.Ref
