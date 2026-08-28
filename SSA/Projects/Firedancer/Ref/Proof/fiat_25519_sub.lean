import SSA.Projects.Firedancer.Ref.Spec.fiat_25519_sub
import SSA.Projects.Firedancer.Ref.Mlir.fiat_25519_sub
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations


namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

def sub_repr (p q : Fin 5 → Nat) :=
  let x1 := (0xfffffffffffda + p 0) - q 0
  let x2 := (0xffffffffffffe + p 1) - q 1
  let x3 := (0xffffffffffffe + p 2) - q 2
  let x4 := (0xffffffffffffe + p 3) - q 3
  let x5 := (0xffffffffffffe + p 4) - q 4
  ![x1, x2, x3, x4, x5]

lemma sub_repr_bounds (p q : Fin 5 → Nat) (i: Fin 5)
  (hpbounds : ∀ (i : Fin 5), p i ≤ 0x8000000000000) : sub_repr p q i ≤ 0x18000000000000 := by
    -- only `p`'s bound matters: `-` is truncated, so subtracting `q i` can only
    -- lower the limb. omega needs the bounds at the same atoms the goal has, so
    -- they are instantiated before the case split.
    have h0 := hpbounds 0; have h1 := hpbounds 1; have h2 := hpbounds 2
    have h3 := hpbounds 3; have h4 := hpbounds 4
    simp only [sub_repr]
    fin_cases i <;> simp <;> omega

/-- One limb of the region's `add bias; sub` pair, over `toNat`. At fiat's input
bound the bias outweighs `q`'s limb on its own, so neither the `add` nor the
`sub` wraps and the 64-bit chain agrees with `sub_repr`'s `ℕ` one. -/
theorem sub_limb_toNat {a b : BitVec 64} {c m n : ℕ} (ha : a.toNat = m) (hb : b.toNat = n)
    (hn : n ≤ 0x8000000000000) (hm : m ≤ 0x8000000000000)
    (hc : 0x8000000000000 ≤ c) (hc' : c < 2 ^ 53) :
    ((a + BitVec.ofNat 64 c) - b).toNat = (c + m) - n := by
  have hadd : (a + BitVec.ofNat 64 c).toNat = m + c := by
    rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_sub, hadd, hb]
  omega

lemma sub_repr_correct (q r : Fin 5 → Nat)
  (hr : ∀ (i : Fin 5), r i ≤ 0x8000000000000) : decodeFieldElem (sub_repr q r) = (decodeFieldElem q) - (decodeFieldElem r) := by
  have p_separation : decodeFieldElem (sub_repr q r) = (decodeFieldElem ![0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe]) + decodeFieldElem q - decodeFieldElem r := by
    simp [decodeFieldElem, sub_repr]
    -- each limb's `-` is a genuine subtraction: the bias alone already exceeds
    -- `q i`, so `Nat.cast_sub` applies and the whole thing is linear
    have e0 : r 0 ≤ 0xfffffffffffda + q 0 := by have := hr 0; omega
    have e1 : r 1 ≤ 0xffffffffffffe + q 1 := by have := hr 1; omega
    have e2 : r 2 ≤ 0xffffffffffffe + q 2 := by have := hr 2; omega
    have e3 : r 3 ≤ 0xffffffffffffe + q 3 := by have := hr 3; omega
    have e4 : r 4 ≤ 0xffffffffffffe + q 4 := by have := hr 4; omega
    rw [Nat.cast_sub e0, Nat.cast_sub e1, Nat.cast_sub e2, Nat.cast_sub e3, Nat.cast_sub e4]
    push_cast
    ring
  -- the bias is exactly `2 * p`, hence `0` in `ZMod p` -- as is `↑p` itself
  have p_decode : decodeFieldElem ![0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe] = p := by
    have hS : (4503599627370458 + 4503599627370494 * 2 ^ 51 + 4503599627370494 * 2 ^ 102
        + 4503599627370494 * 2 ^ 153 + 4503599627370494 * 2 ^ 204 : ℕ) = 2 * _root_.p := by
      norm_num [_root_.p]
    have hcast := congrArg (fun n : ℕ => (n : ZMod _root_.p)) hS
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_self,
      mul_zero] at hcast
    simpa [decodeFieldElem] using hcast
  rw [p_separation, p_decode, ZMod.natCast_self, zero_add]

set_option maxHeartbeats 3200000 in
theorem fiat_25519_sub_conforms (o p q: Pointer) (s: GlobalState)
  (hpbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x8000000000000)
  (hqbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ 0x8000000000000)
  (ho: IsFieldElemPtr s.mem o)
  (hp: IsFieldElemPtr s.mem p)
  (hq: IsFieldElemPtr s.mem q) :
  fiat_25519_sub_spec o p q s := by
    simp only [fiat_25519_sub_spec, Cfg.denote]

    obtain ⟨pblk, hpblk, hplen⟩ := id hp.left
    obtain ⟨qblk, hqblk, hqlen⟩ := id hq.left

    obtain ⟨pinput, hpinput⟩ : ∃ l : Fin 5 → ℕ, ∀ i, readLimb? p i s.mem = some (l i) :=
      ⟨fun i => (pblk.bytes.extractLsb' (p.offsetInBits + 64 * i.toNat) 64).toNat,
        fun i => by simp [readLimb?, MemoryState.live?, hpblk]⟩
    obtain ⟨qinput, hqinput⟩ : ∃ l : Fin 5 → ℕ, ∀ i, readLimb? q i s.mem = some (l i) :=
      ⟨fun i => (qblk.bytes.extractLsb' (q.offsetInBits + 64 * i.toNat) 64).toNat,
        fun i => by simp [readLimb?, MemoryState.live?, hqblk]⟩
    let output := sub_repr pinput qinput
    let outputBV := BitVec.ofNat 64 ∘ output

    refine ⟨outputBV 4 ++ outputBV 3 ++ outputBV 2 ++ outputBV 1 ++ outputBV 0, ?_⟩

    constructor
    case right =>
      simp [readFieldElem?, hqinput, hpinput, ho, limbReadback, outputBV]
      have pinput_bounds (j: Fin 5) : pinput j ≤ 0x8000000000000 := by simp only [hpinput, hpbounds j]
      have qinput_bounds (j: Fin 5) : qinput j ≤ 0x8000000000000 := by simp only [hqinput, hqbounds j]
      have output_bounds (i: Fin 5) : output i ≤ 0x18000000000000 := by
        simp only [output]
        simp only [sub_repr_bounds pinput qinput i pinput_bounds]
      have loose_output_bounds (i: Fin 5) : output i < 18446744073709551616 :=
        (output_bounds i).trans_lt (by norm_num)
      simp [loose_output_bounds, Nat.mod_eq_of_lt]
      -- both halves read the limbs back out of a literal vector
      have vec_eq {α : Type} (f: Fin 5 → α) : ![f 0, f 1, f 2, f 3, f 4] = f := by
        funext i; fin_cases i <;> rfl
      constructor
      simp only [vec_eq, HSub.hSub, output, sub_repr_correct pinput qinput qinput_bounds]

      intro i
      -- the stored vector is `output` pushed through `ofNat`, limb by limb; the
      -- `ofNat` truncation can only lower a limb, so the bound carries over
      simp only [vec_eq (fun j => BitVec.ofNat 64 (output j)), BitVec.toNat_ofNat]
      exact (Nat.mod_le _ _).trans (output_bounds i)

    let output_state : GlobalState :=
      { s with
        mem := ((((s.mem.splice o (outputBV 0)).splice (o.withOffset 8) (outputBV 1)).splice
                  (o.withOffset 16) (outputBV 2)).splice (o.withOffset 24) (outputBV 3)).splice
                  (o.withOffset 32) (outputBV 4) }
    refine ⟨output_state, ?_, ?_⟩
    pick_goal 2

    simp [output_state, GlobalState.equiv_def]
    intro p
    obtain ⟨oblk, hoblk, holen⟩ := id ho.left

    by_cases h: o.id = p
    case neg =>
      -- an unrelated block: every splice here is at `q.id`, so none is visible.
      -- `getElem?_splice_ne` is stated over `m[_]?`, so it has to fire before
      -- `getElem?_eq` rewrites that into the underlying map lookup.
      simp only [MemoryState.live?]
      have h₄ : (o.withOffset 32#64).id ≠ p := by simp [Pointer.withOffset, h]
      have h₃ : (o.withOffset 24#64).id ≠ p := by simp [Pointer.withOffset, h]
      have h₂ : (o.withOffset 16#64).id ≠ p := by simp [Pointer.withOffset, h]
      have h₁ : (o.withOffset 8#64).id ≠ p := by simp [Pointer.withOffset, h]
      simp only [getElem?_splice_ne h₄, getElem?_splice_ne h₃, getElem?_splice_ne h₂, getElem?_splice_ne h₁, getElem?_splice_ne h]
    case pos =>
      simp only [MemoryState.live?]
      rw [← h]
      simp only [getElem?_splice_self (w := 320) (x := outputBV 4 ++ outputBV 3 ++ outputBV 2 ++ outputBV 1 ++ outputBV 0) hoblk]

      have hoffo : ∀ (k : ℕ) (off : BitVec 64), k ≤ 4 → off.toNat = 8 * k →
          (o.withOffset off).offsetInBits = o.offsetInBits + 64 * k := by
        rintro k off hk hoff
        have hadd : (o.offset + off).toNat = o.offset.toNat + off.toNat := by
          rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
        simp only [Pointer.withOffset, Pointer.offsetInBits, hadd, hoff]
        omega
      have o₁ : (o.withOffset 8#64).offsetInBits = o.offsetInBits + 64 := by
        rw [hoffo 1 8#64 (by omega) (by simp)]
      have o₂ : (o.withOffset 16#64).offsetInBits = o.offsetInBits + 128 := by
        rw [hoffo 2 16#64 (by omega) (by simp)]
      have o₃ : (o.withOffset 24#64).offsetInBits = o.offsetInBits + 192 := by
        rw [hoffo 3 24#64 (by omega) (by simp)]
      have o₄ : (o.withOffset 32#64).offsetInBits = o.offsetInBits + 256 := by
        rw [hoffo 4 32#64 (by omega) (by simp)]

      have hid : ∀ off : BitVec 64, (o.withOffset off).id = o.id := fun _ => rfl
      have k₀ := getElem?_splice_self (x := outputBV 0) hoblk
      have k₁ := getElem?_splice_self (p := o.withOffset 8#64) (x := outputBV 1) k₀
      rw [hid] at k₁
      have k₂ := getElem?_splice_self (p := o.withOffset 16#64) (x := outputBV 2) k₁
      rw [hid] at k₂
      have k₃ := getElem?_splice_self (p := o.withOffset 24#64) (x := outputBV 3) k₂
      rw [hid] at k₃
      have k₄ := getElem?_splice_self (p := o.withOffset 32#64) (x := outputBV 4) k₃
      rw [hid] at k₄
      rw [k₄, o₁, o₂, o₃, o₄]
      simp only [Option.some.injEq, LiveBlock.mk.injEq, true_and]
      clear o₁ o₂ o₃ o₄ k₀ k₁ k₂ k₃ k₄

      simp only [spliceBits_append]
      have assoc : (outputBV 4 ++ outputBV 3 ++ outputBV 2 ++ outputBV 1 ++ outputBV 0) = (outputBV 4 ++ (outputBV 3 ++ (outputBV 2 ++ (outputBV 1 ++ outputBV 0)))) := by
        simp only [BitVec.append_assoc, BitVec.cast_eq]

      rw [assoc]

    denote_step_all v 5
    denote_eval v 0 5
    simp only [LLVM.const?] at hv0 hv1 hv2 hv3 hv4 hv5
    subst hv0 hv1 hv2 hv3 hv4 hv5

    peel_limb 0, p, hp.left, pblk, hpblk, plimb
    denote_step_all v 7
    denote_eval v 7 7
    simp [LLVM.add, LLVM.add?] at hv7
    peel_limb 0, q, hq.left, qblk, hqblk, qlimb
    denote_step_all v 9
    denote_eval v 9 9
    simp [LLVM.sub, LLVM.sub?, hv7] at hv9
    set x1 := (plimb₀ + 0xfffffffffffda#64) - qlimb₀ with hx1
    subst hv9
    denote_clear v 7 9

    peel_gep_limb 1, p, hp.left, s, p
    peel_limb 1, p₁, hp₁, pblk, hpblk, plimb
    denote_step_all v 12
    denote_eval v 12 12
    simp [LLVM.add, LLVM.add?] at hv12
    peel_gep_limb 1, q, hq.left, s, q
    peel_limb 1, q₁, hq₁, qblk, hqblk, qlimb
    denote_step_all v 15
    denote_eval v 15 15
    simp [LLVM.sub, LLVM.sub?, hv12] at hv15
    set x2 := (plimb₁ + 0xffffffffffffe#64) - qlimb₁
    subst hv15
    denote_clear v 12 15

    peel_gep_limb 2, p, hp.left, s, p
    peel_limb 2, p₂, hp₂, pblk, hpblk, plimb
    denote_step_all v 18
    denote_eval v 18 18
    simp [LLVM.add, LLVM.add?] at hv18
    peel_gep_limb 2, q, hq.left, s, q
    peel_limb 2, q₂, hq₂, qblk, hqblk, qlimb
    denote_step_all v 21
    denote_eval v 21 21
    simp [LLVM.sub, LLVM.sub?, hv18] at hv21
    set x3 := (plimb₂ + 0xffffffffffffe#64) - qlimb₂
    subst hv21
    denote_clear v 18 21

    peel_gep_limb 3, p, hp.left, s, p
    peel_limb 3, p₃, hp₃, pblk, hpblk, plimb
    denote_step_all v 24
    denote_eval v 24 24
    simp [LLVM.add, LLVM.add?] at hv24
    peel_gep_limb 3, q, hq.left, s, q
    peel_limb 3, q₃, hq₃, qblk, hqblk, qlimb
    denote_step_all v 27
    denote_eval v 27 27
    simp [LLVM.sub, LLVM.sub?, hv24] at hv27
    set x4 := (plimb₃ + 0xffffffffffffe#64) - qlimb₃
    subst hv27
    denote_clear v 24 27

    peel_gep_limb 4, p, hp.left, s, p
    peel_limb 4, p₄, hp₄, pblk, hpblk, plimb
    denote_step_all v 30
    denote_eval v 30 30
    simp [LLVM.add, LLVM.add?] at hv30
    peel_gep_limb 4, q, hq.left, s, q
    peel_limb 4, q₄, hq₄, qblk, hqblk, qlimb
    denote_step_all v 33
    denote_eval v 33 33
    simp [LLVM.sub, LLVM.sub?, hv30] at hv33
    set x5 := (plimb₄ + 0xffffffffffffe#64) - qlimb₄
    subst hv33
    denote_clear v 30 33

    -- a loaded limb is the spec's: `readLimb?` reads the same range of the same
    -- block, once the `getelementptr` offset is normalised. `hp'`/`hq'` are what
    -- rule out the pointer wrapping.
    have hpl : ∀ (i : Fin 5) (d : BitVec 64), d.toNat = 8 * i.toNat →
        (pblk.bytes.extractLsb' (p.withOffset d).offsetInBits 64).toNat = pinput i := by
      rintro i d hd
      have h5 : i.toNat < 5 := i.isLt
      have hadd : (p.offset + d).toNat = p.offset.toNat + d.toNat := by
        rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [show (p.withOffset d).offsetInBits = p.offsetInBits + 64 * i.toNat by
        simp only [Pointer.withOffset, Pointer.offsetInBits, hadd, hd]; omega]
      simpa [readLimb?, MemoryState.live?, hpblk] using hpinput i
    have hql : ∀ (i : Fin 5) (d : BitVec 64), d.toNat = 8 * i.toNat →
        (qblk.bytes.extractLsb' (q.withOffset d).offsetInBits 64).toNat = qinput i := by
      rintro i d hd
      have h5 : i.toNat < 5 := i.isLt
      have hadd : (q.offset + d).toNat = q.offset.toNat + d.toNat := by
        rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [show (q.withOffset d).offsetInBits = q.offsetInBits + 64 * i.toNat by
        simp only [Pointer.withOffset, Pointer.offsetInBits, hadd, hd]; omega]
      simpa [readLimb?, MemoryState.live?, hqblk] using hqinput i
    have pb : ∀ i : Fin 5, pinput i ≤ 0x8000000000000 := fun i => hpbounds i _ (hpinput i)
    have qb : ∀ i : Fin 5, qinput i ≤ 0x8000000000000 := fun i => hqbounds i _ (hqinput i)
    -- limb 0 is loaded straight off the base pointer, with no `getelementptr`
    have m1 : x1.toNat = (0xfffffffffffda + pinput 0) - qinput 0 :=
      sub_limb_toNat (by simpa [readLimb?, MemoryState.live?, hpblk, hplimb₀] using hpinput 0)
        (by simpa [readLimb?, MemoryState.live?, hqblk, hqlimb₀] using hqinput 0)
        (qb 0) (pb 0) (by norm_num) (by norm_num)
    have m2 : x2.toNat = (0xffffffffffffe + pinput 1) - qinput 1 :=
      sub_limb_toNat (by rw [hplimb₁]; exact hpl 1 8#64 (by simp))
        (by rw [hqlimb₁]; exact hql 1 8#64 (by simp))
        (qb 1) (pb 1) (by norm_num) (by norm_num)
    have m3 : x3.toNat = (0xffffffffffffe + pinput 2) - qinput 2 :=
      sub_limb_toNat (by rw [hplimb₂]; exact hpl 2 16#64 (by simp))
        (by rw [hqlimb₂]; exact hql 2 16#64 (by simp))
        (qb 2) (pb 2) (by norm_num) (by norm_num)
    have m4 : x4.toNat = (0xffffffffffffe + pinput 3) - qinput 3 :=
      sub_limb_toNat (by rw [hplimb₃]; exact hpl 3 24#64 (by simp))
        (by rw [hqlimb₃]; exact hql 3 24#64 (by simp))
        (qb 3) (pb 3) (by norm_num) (by norm_num)
    have m5 : x5.toNat = (0xffffffffffffe + pinput 4) - qinput 4 :=
      sub_limb_toNat (by rw [hplimb₄]; exact hpl 4 32#64 (by simp))
        (by rw [hqlimb₄]; exact hql 4 32#64 (by simp))
        (qb 4) (pb 4) (by norm_num) (by norm_num)

    have hout : ∀ (v : BitVec 64) (i : Fin 5), v.toNat = output i → v = outputBV i := by
      intro v i h
      show v = BitVec.ofNat 64 (output i)
      rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    -- `output i` is `sub_repr pinput qinput i`, which reduces straight to `mᵢ`'s
    -- right-hand side. Routing through `![x1.toNat, ..]` instead makes the kernel
    -- unfold the `xᵢ` limb chain and blow its stack.
    have e1 : x1 = outputBV 0 := hout _ 0 m1
    have e2 : x2 = outputBV 1 := hout _ 1 m2
    have e3 : x3 = outputBV 2 := hout _ 2 m3
    have e4 : x4 = outputBV 3 := hout _ 3 m4
    have e5 : x5 = outputBV 4 := hout _ 4 m5
    rw [e1, e2, e3, e4, e5]

    peel_store (outputBV 0), o, ho.left, s
    set s₁ : GlobalState := { s with mem := s.mem.splice o (outputBV 0) } with hs₁
    have f₁ : Fits s₁.mem o (5 * 64) := fits_splice ho.left

    peel_gep_limb 1, o, f₁, s₁, o
    peel_store (outputBV 1), o₁, ho₁, s₁
    set s₂ : GlobalState := { s₁ with mem := s₁.mem.splice o₁ (outputBV 1) } with hs₂
    have f₂ : Fits s₂.mem o (5 * 64) := fits_splice f₁

    peel_gep_limb 2, o, f₂, s₂, o
    peel_store (outputBV 2), o₂, ho₂, s₂
    set s₃ : GlobalState := { s₂ with mem := s₂.mem.splice o₂ (outputBV 2) } with hs₃
    have f₃ : Fits s₃.mem o (5 * 64) := fits_splice f₂

    peel_gep_limb 3, o, f₃, s₃, o
    peel_store (outputBV 3), o₃, ho₃, s₃
    set s₄ : GlobalState := { s₃ with mem := s₃.mem.splice o₃ (outputBV 3) } with hs₄
    have f₄ : Fits s₄.mem o (5 * 64) := fits_splice f₃

    peel_gep_limb 4, o, f₄, s₄, o
    peel_store (outputBV 4), o₄, ho₄, s₄


    simp only [BlockCom.denote_term, Terminator.denote_ret, output_state,
      hs₁, hs₂, hs₃, hs₄, o₁, o₂, o₃, o₄, simp_denote, simp_sllvm]

end Firedancer.Ref
