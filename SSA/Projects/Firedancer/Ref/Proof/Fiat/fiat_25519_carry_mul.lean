import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_carry_mul
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_carry_mul
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Limb
import SSA.Projects.Firedancer.Ref.Proof.CarryChain


namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 20000 in
theorem fiat_25519_carry_mul_conforms (o p q: Pointer) (s: GlobalState)
  (hs : s.WF)
  (ho : IsFieldElemPtr s.mem o)
  (hp : IsFieldElemPtr s.mem p)
  (hq : IsFieldElemPtr s.mem q)
  (hplimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x18000000000000)
  (hqlimb : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ 0x18000000000000) :
  fiat_25519_carry_mul_spec o p q s hp hq := by
    simp only [fiat_25519_carry_mul_spec, Cfg.denote]

    obtain ⟨pblk, hpblk, hplen⟩ := id hp.left
    obtain ⟨pinput, hpinput⟩ := exists_limbs hpblk
    obtain ⟨qblk, hqblk, hqlen⟩ := id hq.left
    obtain ⟨qinput, hqinput⟩ := exists_limbs hqblk
    let output := carry_product_repr pinput qinput
    let outputBV := BitVec.ofNat 64 ∘ output

    have hpb : ∀ i, pinput i ≤ 0x18000000000000 := fun i => hplimb i _ (hpinput i)
    have hqb : ∀ i, qinput i ≤ 0x18000000000000 := fun i => hqlimb i _ (hqinput i)
    have hcb : ∀ i, output i ≤ 0x8000000000000 := carry_product_bounds pinput qinput hpb hqb
    have hlimb : ∀ i : Fin 5, (outputBV i).toNat = output i := by
      intro i
      have hi : output i < 2 ^ 64 := by have := hcb i; omega
      show (BitVec.ofNat 64 (output i)).toNat = output i
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

    refine ⟨packLimbs outputBV, ?repr, ?exec, ?bound⟩
    case repr =>
      have hext : (fun i : Fin 5 =>
          ((packLimbs outputBV).extractLsb' (64 * i.toNat) 64).toNat) = output := by
        funext i
        rw [extractLsb'_packLimbs]
        fin_cases i <;> simpa using hlimb _
      rw [hext]
      simp only [readFieldElem, readFieldElem?, hpinput, hqinput, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def, Option.get_some, vec_eq]
      exact carry_product_eq_value pinput qinput hpb hqb
    case bound =>
      intro i l hl
      rw [limbReadbackPack s.mem o outputBV (show Fits s.mem o (5 * 64) from ho.left) i] at hl
      rw [← Option.some.inj hl]
      fin_cases i <;> simpa [hlimb] using hcb _

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

    denote_step_all v 4
    denote_eval v 0 4
    simp only [LLVM.const?] at hv0 hv1 hv2 hv3 hv4
    subst hv0 hv1 hv2 hv3 hv4

    have hpoff : ∀ (i : Fin 5) (off : BitVec 64), off.toNat = 8 * i.toNat →
        (p.withOffset off).offsetInBits = p.offsetInBits + 64 * i.toNat :=
      fun i _ ho => limbOffsetInBits hp.right (by have : i.toNat < 5 := i.isLt; omega) ho
    have hqoff : ∀ (i : Fin 5) (off : BitVec 64), off.toNat = 8 * i.toNat →
        (q.withOffset off).offsetInBits = q.offsetInBits + 64 * i.toNat :=
      fun i _ ho => limbOffsetInBits hq.right (by have : i.toNat < 5 := i.isLt; omega) ho
    have hpbits : ∀ (i : Fin 5) (off : ℕ), off = p.offsetInBits + 64 * i.toNat →
        pblk.bytes.extractLsb' off 64 = BitVec.ofNat 64 (pinput i) := limbBits hpblk hpinput
    have hqbits : ∀ (i : Fin 5) (off : ℕ), off = q.offsetInBits + 64 * i.toNat →
        qblk.bytes.extractLsb' off 64 = BitVec.ofNat 64 (qinput i) := limbBits hqblk hqinput

    peel_gep_limb 4, p, hp.left, s, p
    peel_limb 4, p₄, hp₄, pblk, hpblk, pl
    rw [show pl₄ = BitVec.ofNat 64 (pinput 4) from hpl₄.trans (hpbits 4 _ (hpoff 4 32 (by simp)))]
    clear hpl₄ pl₄

    denote_step_all v 7
    peel_gep_limb 4, q, hq.left, s, q
    peel_limb 4, q₄, hq₄, qblk, hqblk, ql
    rw [show ql₄ = BitVec.ofNat 64 (qinput 4) from hql₄.trans (hqbits 4 _ (hqoff 4 32 (by simp)))]
    clear hql₄ ql₄
    denote_step_all v 12
    peel_gep_limb 3, q, hq.left, s, q
    peel_limb 3, q₃, hq₃, qblk, hqblk, ql
    rw [show ql₃ = BitVec.ofNat 64 (qinput 3) from hql₃.trans (hqbits 3 _ (hqoff 3 24 (by simp)))]
    clear hql₃ ql₃
    denote_step_all v 17
    peel_gep_limb 2, q, hq.left, s, q
    peel_limb 2, q₂, hq₂, qblk, hqblk, ql
    rw [show ql₂ = BitVec.ofNat 64 (qinput 2) from hql₂.trans (hqbits 2 _ (hqoff 2 16 (by simp)))]
    clear hql₂ ql₂
    denote_step_all v 22
    peel_gep_limb 1, q, hq.left, s, q
    peel_limb 1, q₁, hq₁, qblk, hqblk, ql
    rw [show ql₁ = BitVec.ofNat 64 (qinput 1) from hql₁.trans (hqbits 1 _ (hqoff 1 8 (by simp)))]
    clear hql₁ ql₁

    denote_step_all v 27
    peel_gep_limb 3, p, hp.left, s, p
    peel_limb 3, p₃, hp₃, pblk, hpblk, pl
    rw [show pl₃ = BitVec.ofNat 64 (pinput 3) from hpl₃.trans (hpbits 3 _ (hpoff 3 24 (by simp)))]
    clear hpl₃ pl₃
    denote_step_all v 33
    peel_gep_limb 2, p, hp.left, s, p
    peel_limb 2, p₂, hp₂, pblk, hpblk, pl
    rw [show pl₂ = BitVec.ofNat 64 (pinput 2) from hpl₂.trans (hpbits 2 _ (hpoff 2 16 (by simp)))]
    clear hpl₂ pl₂
    denote_step_all v 38
    peel_gep_limb 1, p, hp.left, s, p
    peel_limb 1, p₁, hp₁, pblk, hpblk, pl
    rw [show pl₁ = BitVec.ofNat 64 (pinput 1) from hpl₁.trans (hpbits 1 _ (hpoff 1 8 (by simp)))]
    clear hpl₁ pl₁

    denote_step_all v 42
    peel_limb 0, q, hq.left, qblk, hqblk, ql
    rw [show ql₀ = BitVec.ofNat 64 (qinput 0) from hql₀.trans (hqbits 0 _ (by simp))]
    clear hql₀ ql₀

    denote_step_all v 57
    peel_limb 0, p, hp.left, pblk, hpblk, pl
    rw [show pl₀ = BitVec.ofNat 64 (pinput 0) from hpl₀.trans (hpbits 0 _ (by simp))]
    clear hpl₀ pl₀

    -- `%58` was the last load, so the rest is pure up to `%117`; `%118` on are
    -- the stores' geps, which need the state a store leaves.
    denote_step_all v 117
    denote_eval v 7 117

    -- What the five stores are handed, proven against this small goal rather
    -- than the program term, which is rewritten exactly five times.
    have key : v113 = PoisonOr.value (outputBV 0) ∧ v116 = PoisonOr.value (outputBV 1)
        ∧ v117 = PoisonOr.value (outputBV 2) ∧ v99 = PoisonOr.value (outputBV 3)
        ∧ v109 = PoisonOr.value (outputBV 4) := by
      have hp64 : ∀ i, pinput i < 2 ^ 64 := fun i => by have := hpb i; omega
      have hq64 : ∀ i, qinput i < 2 ^ 64 := fun i => by have := hqb i; omega
      have hq19 : ∀ i, qinput i * 19 < 2 ^ 64 := fun i => by have := hqb i; omega

      -- %7-%65: the twenty-five products
      eval_llvm 7
      eval_llvm 10
      eval_llvm 11
      eval_llvm 12 as x1
      eval_llvm 15
      eval_llvm 16
      eval_llvm 17 as x2
      eval_llvm 20
      eval_llvm 21
      eval_llvm 22 as x3
      eval_llvm 25
      eval_llvm 26
      eval_llvm 27 as x4
      eval_llvm 30
      eval_llvm 31 as x5
      eval_llvm 32 as x6
      eval_llvm 33 as x7
      eval_llvm 36
      eval_llvm 37 as x8
      eval_llvm 38 as x9
      eval_llvm 41
      eval_llvm 42 as x10
      eval_llvm 44
      eval_llvm 45 as x11
      eval_llvm 46
      eval_llvm 47 as x12
      eval_llvm 48 as x13
      eval_llvm 49
      eval_llvm 50 as x14
      eval_llvm 51 as x15
      eval_llvm 52 as x16
      eval_llvm 53
      eval_llvm 54 as x17
      eval_llvm 55 as x18
      eval_llvm 56 as x19
      eval_llvm 57 as x20
      eval_llvm 59
      eval_llvm 60
      eval_llvm 61 as x21
      eval_llvm 62 as x22
      eval_llvm 63 as x23
      eval_llvm 64 as x24
      eval_llvm 65 as x25

      -- %66-%72: column 0, carry `x27`, limb `x28`
      eval_llvm 66
      eval_llvm 67
      eval_llvm 68
      eval_llvm 69 as x26
      eval_llvm 70 as x27
      eval_llvm 71
      eval_llvm 72 as x28

      -- %73-%82: column 1 (`x32`); `%73` belongs to column 2
      eval_llvm 73
      eval_llvm 74
      eval_llvm 75
      eval_llvm 76
      eval_llvm 77 as x32
      eval_llvm 78
      eval_llvm 79 as x33
      eval_llvm 80 as x34
      eval_llvm 81
      eval_llvm 82 as x35

      -- %83-%90: column 2 (`x31`)
      eval_llvm 83
      eval_llvm 84
      eval_llvm 85
      eval_llvm 86 as x31
      eval_llvm 87 as x36
      eval_llvm 88 as x37
      eval_llvm 89
      eval_llvm 90 as x38

      -- %91-%99: column 3 (`x30`)
      eval_llvm 91
      eval_llvm 92
      eval_llvm 93
      eval_llvm 94
      eval_llvm 95 as x30
      eval_llvm 96 as x39
      eval_llvm 97 as x40
      eval_llvm 98
      eval_llvm 99 as x41

      -- %100-%109: column 4 (`x29`)
      eval_llvm 100
      eval_llvm 101
      eval_llvm 102
      eval_llvm 103
      eval_llvm 104 as x29
      eval_llvm 105 as x42
      eval_llvm 106
      eval_llvm 107 as x43
      eval_llvm 108
      eval_llvm 109 as x44

      -- %110-%113: the top carry, folded back into limb 0
      eval_llvm 110 as x45
      eval_llvm 111 as x46
      eval_llvm 112 as x47
      eval_llvm 113 as x48

      -- each product in the form `carry_product_repr` writes it
      have n1 : x1.toNat = pinput 4 * (qinput 4 * 19) := by
        rw [← hx1, toNat_zx19_mul_zx (hq19 4) (hp64 4)]; ring
      have n2 : x2.toNat = pinput 4 * (qinput 3 * 19) := by
        rw [← hx2, toNat_zx19_mul_zx (hq19 3) (hp64 4)]; ring
      have n3 : x3.toNat = pinput 4 * (qinput 2 * 19) := by
        rw [← hx3, toNat_zx19_mul_zx (hq19 2) (hp64 4)]; ring
      have n4 : x4.toNat = pinput 4 * (qinput 1 * 19) := by
        rw [← hx4, toNat_zx19_mul_zx (hq19 1) (hp64 4)]; ring
      have n5 : x5.toNat = pinput 3 * (qinput 4 * 19) := by
        rw [← hx5, toNat_zx_mul_zx19 (hp64 3) (hq19 4)]
      have n6 : x6.toNat = pinput 3 * (qinput 3 * 19) := by
        rw [← hx6, toNat_zx_mul_zx19 (hp64 3) (hq19 3)]
      have n7 : x7.toNat = pinput 3 * (qinput 2 * 19) := by
        rw [← hx7, toNat_zx_mul_zx19 (hp64 3) (hq19 2)]
      have n8 : x8.toNat = pinput 2 * (qinput 4 * 19) := by
        rw [← hx8, toNat_zx_mul_zx19 (hp64 2) (hq19 4)]
      have n9 : x9.toNat = pinput 2 * (qinput 3 * 19) := by
        rw [← hx9, toNat_zx_mul_zx19 (hp64 2) (hq19 3)]
      have n10 : x10.toNat = pinput 1 * (qinput 4 * 19) := by
        rw [← hx10, toNat_zx_mul_zx19 (hp64 1) (hq19 4)]
      have n11 : x11.toNat = pinput 4 * qinput 0 := by
        rw [← hx11, toNat_zx_mul_zx (hq64 0) (hp64 4)]; ring
      have n12 : x12.toNat = pinput 3 * qinput 1 := by
        rw [← hx12, toNat_zx_mul_zx (hp64 3) (hq64 1)]
      have n13 : x13.toNat = pinput 3 * qinput 0 := by
        rw [← hx13, toNat_zx_mul_zx (hq64 0) (hp64 3)]; ring
      have n14 : x14.toNat = pinput 2 * qinput 2 := by
        rw [← hx14, toNat_zx_mul_zx (hp64 2) (hq64 2)]
      have n15 : x15.toNat = pinput 2 * qinput 1 := by
        rw [← hx15, toNat_zx_mul_zx (hp64 2) (hq64 1)]
      have n16 : x16.toNat = pinput 2 * qinput 0 := by
        rw [← hx16, toNat_zx_mul_zx (hq64 0) (hp64 2)]; ring
      have n17 : x17.toNat = pinput 1 * qinput 3 := by
        rw [← hx17, toNat_zx_mul_zx (hp64 1) (hq64 3)]
      have n18 : x18.toNat = pinput 1 * qinput 2 := by
        rw [← hx18, toNat_zx_mul_zx (hp64 1) (hq64 2)]
      have n19 : x19.toNat = pinput 1 * qinput 1 := by
        rw [← hx19, toNat_zx_mul_zx (hp64 1) (hq64 1)]
      have n20 : x20.toNat = pinput 1 * qinput 0 := by
        rw [← hx20, toNat_zx_mul_zx (hq64 0) (hp64 1)]; ring
      have n21 : x21.toNat = pinput 0 * qinput 4 := by
        rw [← hx21, toNat_zx_mul_zx (hp64 0) (hq64 4)]
      have n22 : x22.toNat = pinput 0 * qinput 3 := by
        rw [← hx22, toNat_zx_mul_zx (hp64 0) (hq64 3)]
      have n23 : x23.toNat = pinput 0 * qinput 2 := by
        rw [← hx23, toNat_zx_mul_zx (hp64 0) (hq64 2)]
      have n24 : x24.toNat = pinput 0 * qinput 1 := by
        rw [← hx24, toNat_zx_mul_zx (hp64 0) (hq64 1)]
      have n25 : x25.toNat = pinput 0 * qinput 0 := by
        rw [← hx25, toNat_zx_mul_zx (hp64 0) (hq64 0)]

      -- product bounds, so the column sums stay linear for omega
      have m : ∀ i j, pinput i * qinput j ≤ 9 * 2 ^ 102 :=
        fun i j => limb_mul_le (hpb i) (hqb j)
      have m19 : ∀ i j, pinput i * (qinput j * 19) ≤ 171 * 2 ^ 102 :=
        fun i j => limb_mul19_le (hpb i) (hqb j)
      have p00 := m 0 0; have p01 := m 0 1; have p02 := m 0 2; have p03 := m 0 3
      have p04 := m 0 4; have p10 := m 1 0; have p11 := m 1 1; have p12 := m 1 2
      have p13 := m 1 3; have p20 := m 2 0; have p21 := m 2 1; have p22 := m 2 2
      have p30 := m 3 0; have p31 := m 3 1; have p40 := m 4 0
      have r14 := m19 1 4; have r23 := m19 2 3; have r32 := m19 3 2; have r41 := m19 4 1
      have r24 := m19 2 4; have r33 := m19 3 3; have r42 := m19 4 2
      have r34 := m19 3 4; have r43 := m19 4 3; have r44 := m19 4 4

      -- the five columns, grouped as `carry_product_repr_eq` names them
      have N0 : x26.toNat = pinput 0 * qinput 0 + (pinput 1 * (qinput 4 * 19)
          + (pinput 2 * (qinput 3 * 19) + (pinput 3 * (qinput 2 * 19)
            + pinput 4 * (qinput 1 * 19)))) := by
        rw [← hx26, toNat_col5 n7 n4 n9 n10 n25 (by omega)]; ring
      have N1 : x32.toNat = pinput 0 * qinput 1 + (pinput 1 * qinput 0
          + (pinput 2 * (qinput 4 * 19) + (pinput 3 * (qinput 3 * 19)
            + pinput 4 * (qinput 2 * 19)))) := by
        rw [← hx32, toNat_col5 n6 n3 n8 n20 n24 (by omega)]; ring
      have N2 : x31.toNat = pinput 0 * qinput 2 + (pinput 1 * qinput 1
          + (pinput 2 * qinput 0 + (pinput 3 * (qinput 4 * 19)
            + pinput 4 * (qinput 3 * 19)))) := by
        rw [← hx31, toNat_col5 n5 n2 n19 n16 n23 (by omega)]; ring
      have N3 : x30.toNat = pinput 0 * qinput 3 + (pinput 1 * qinput 2
          + (pinput 2 * qinput 1 + (pinput 3 * qinput 0 + pinput 4 * (qinput 4 * 19)))) := by
        rw [← hx30, toNat_col5 n15 n1 n18 n13 n22 (by omega)]; ring
      have N4 : x29.toNat = pinput 0 * qinput 4 + (pinput 1 * qinput 3
          + (pinput 2 * qinput 2 + (pinput 3 * qinput 1 + pinput 4 * qinput 0))) := by
        rw [← hx29, toNat_col5 n14 n12 n17 n11 n21 (by omega)]; ring
      obtain ⟨B0, B1, B2, B3, B4⟩ := product_columns_le pinput qinput hpb hqb
      rw [← N0] at B0; rw [← N1] at B1; rw [← N2] at B2; rw [← N3] at B3; rw [← N4] at B4

      have n27 : x27.toNat = x26.toNat / 2 ^ 51 := by rw [← hx27]; exact shift_toNat128 x26
      have b27 : x27.toNat ≤ 693 * 2 ^ 51 := by rw [n27]; omega
      have n28 : x28.toNat = x26.toNat % 2 ^ 51 := by rw [← hx28]; exact trunc_mask_toNat x26
      have b28 : x28.toNat < 2 ^ 51 := by rw [n28]; omega
      have n33 : x33.toNat = x27.toNat + x32.toNat := by
        rw [← hx33, toNat_add (by rw [mask64_toNat]; omega), mask64_toNat,
          Nat.mod_eq_of_lt (by omega)]
        omega
      have b33 : x33.toNat ≤ 531 * 2 ^ 102 + 693 * 2 ^ 51 := by rw [n33]; omega
      have n34 : x34.toNat = x33.toNat / 2 ^ 51 := by rw [← hx34]; exact shift_toNat128 x33
      have b34 : x34.toNat ≤ 531 * 2 ^ 51 + 693 := by rw [n34]; omega
      have n35 : x35.toNat = x33.toNat % 2 ^ 51 := by rw [← hx35]; exact trunc_mask_toNat x33
      have b35 : x35.toNat < 2 ^ 51 := by rw [n35]; omega
      have n36 : x36.toNat = x34.toNat + x31.toNat := by
        rw [← hx36, toNat_add (by rw [mask64_toNat]; omega), mask64_toNat,
          Nat.mod_eq_of_lt (by omega)]
        omega
      have b36 : x36.toNat ≤ 369 * 2 ^ 102 + 531 * 2 ^ 51 + 693 := by rw [n36]; omega
      have n37 : x37.toNat = x36.toNat / 2 ^ 51 := by rw [← hx37]; exact shift_toNat128 x36
      have b37 : x37.toNat ≤ 369 * 2 ^ 51 + 532 := by rw [n37]; omega
      have n38 : x38.toNat = x36.toNat % 2 ^ 51 := by rw [← hx38]; exact trunc_mask_toNat x36
      have b38 : x38.toNat < 2 ^ 51 := by rw [n38]; omega
      have n39 : x39.toNat = x37.toNat + x30.toNat := by
        rw [← hx39, toNat_add (by rw [mask64_toNat]; omega), mask64_toNat,
          Nat.mod_eq_of_lt (by omega)]
        omega
      have b39 : x39.toNat ≤ 207 * 2 ^ 102 + 369 * 2 ^ 51 + 532 := by rw [n39]; omega
      have n40 : x40.toNat = x39.toNat / 2 ^ 51 := by rw [← hx40]; exact shift_toNat128 x39
      have b40 : x40.toNat ≤ 207 * 2 ^ 51 + 370 := by rw [n40]; omega
      have n41 : x41.toNat = x39.toNat % 2 ^ 51 := by rw [← hx41]; exact trunc_mask_toNat x39
      have n42 : x42.toNat = x40.toNat + x29.toNat := by
        rw [← hx42, toNat_add (by rw [mask64_toNat]; omega), mask64_toNat,
          Nat.mod_eq_of_lt (by omega)]
        omega
      have b42 : x42.toNat ≤ 45 * 2 ^ 102 + 207 * 2 ^ 51 + 370 := by rw [n42]; omega
      have n43 : x43.toNat = x42.toNat / 2 ^ 51 := by
        rw [← hx43, trunc_shift_toNat, Nat.mod_eq_of_lt (by omega)]
      have b43 : x43.toNat ≤ 45 * 2 ^ 51 + 208 := by rw [n43]; omega
      have n44 : x44.toNat = x42.toNat % 2 ^ 51 := by rw [← hx44]; exact trunc_mask_toNat x42
      have n45 : x45.toNat = x43.toNat * 19 := by
        rw [← hx45]; exact mul19_toNat (by omega)
      have b45 : x45.toNat ≤ 855 * 2 ^ 51 + 3952 := by rw [n45]; omega
      have n46 : x46.toNat = x28.toNat + x45.toNat := by
        rw [← hx46, toNat_add (by omega)]; omega
      have b46 : x46.toNat ≤ 856 * 2 ^ 51 + 3952 := by rw [n46]; omega
      have n47 : x47.toNat = x46.toNat / 2 ^ 51 := by rw [← hx47]; exact shift_toNat x46
      have b47 : x47.toNat ≤ 856 := by rw [n47]; omega
      have n48 : x48.toNat = x46.toNat % 2 ^ 51 := by rw [← hx48]; exact mask_toNat x46

      -- `%114`/`%117` carry `nsw, nuw`, so their bounds come first
      have hno49s : x47.saddOverflow x35 = false := saddOverflow_eq_false (by omega)
      have hno49u : x47.uaddOverflow x35 = false := uaddOverflow_eq_false (by omega)
      eval_llvm 114 [hno49s, hno49u] as x49
      eval_llvm 115 as x50
      eval_llvm 116 as x51
      have n49 : x49.toNat = x47.toNat + x35.toNat := by
        rw [← hx49, toNat_add (by omega)]
      have n50 : x50.toNat = x49.toNat / 2 ^ 51 := by rw [← hx50]; exact shift_toNat x49
      have b50 : x50.toNat ≤ 1 := by rw [n50]; omega
      have n51 : x51.toNat = x49.toNat % 2 ^ 51 := by rw [← hx51]; exact mask_toNat x49
      have hno52s : x50.saddOverflow x38 = false := saddOverflow_eq_false (by omega)
      have hno52u : x50.uaddOverflow x38 = false := uaddOverflow_eq_false (by omega)
      eval_llvm 117 [hno52s, hno52u] as x52
      have n52 : x52.toNat = x50.toNat + x38.toNat := by
        rw [← hx52, toNat_add (by omega)]

      -- the registers the stores consume are `carry_product_repr`'s limbs
      have t50 : x50.toNat % 2 ^ 8 = x50.toNat := Nat.mod_eq_of_lt (by omega)
      have hout : output = ![x48.toNat, x51.toNat, x52.toNat, x41.toNat, x44.toNat] := by
        show carry_product_repr pinput qinput = _
        rw [carry_product_repr_eq, ← N0, ← N1, ← N2, ← N3, ← N4]
        simp only [carry_chain]
        rw [← n27, ← n28, ← n33, ← n34, ← n35, ← n36, ← n37, ← n38, ← n39, ← n40, ← n41,
          ← n42, ← n43, ← n44, ← n45, ← n46, ← n47, ← n48, ← n49, ← n50, t50, ← n51, ← n52]
      have hbv : ∀ (u : BitVec 64) (i : Fin 5), u.toNat = output i → u = outputBV i :=
        fun _ _ h => eq_ofNat_of_toNat h
      exact ⟨hv113.trans (congrArg _ (hbv _ 0 (by simp [hout]))),
        hv116.trans (congrArg _ (hbv _ 1 (by simp [hout]))),
        hv117.trans (congrArg _ (hbv _ 2 (by simp [hout]))),
        hv99.trans (congrArg _ (hbv _ 3 (by simp [hout]))),
        hv109.trans (congrArg _ (hbv _ 4 (by simp [hout])))⟩

    obtain ⟨e117, e120, e121, e103, e113⟩ := key
    rw [e117, e120, e121, e103, e113]

    -- the five stores, limb 0 first
    store_limbs outputBV, o, ho.left, s

    -- `llvm.return`: nothing is left but the state
    simp only [BlockCom.denote_term, Terminator.denote_ret, simp_sllvm, houtMem,
      hs₁, hs₂, hs₃, hs₄, o₁, o₂, o₃, o₄]
    rfl

end Firedancer.Ref
