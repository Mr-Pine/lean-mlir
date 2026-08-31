import SSA.Projects.Firedancer.Ref.Spec.fiat_25519_carry
import SSA.Projects.Firedancer.Ref.Mlir.fiat_25519_carry
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Limb


namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

def carry_repr (input : Fin 5 → Nat) :=
  let x1 := input 0
  let x2 := (x1 / 2^51) + input 1
  let x3 := (x2 / 2^51) + input 2
  let x4 := (x3 / 2^51) + input 3
  let x5 := (x4 / 2^51) + input 4
  let x6 := (x1 % 2^51) + (x5 / 2^51) * 0x13
  let x7 := (x6 / 2^51 % 2^8) + (x2 % 2^51)
  let x8 := x6 % 2^51
  let x9 := x7 % 2^51
  let x10 := (x7 / 2^51 % 2^8) + (x3 % 2^51)
  let x11 := x4 % 2^51
  let x12 := x5 % 2^51
  ![x8, x9, x10, x11, x12]

/-- Every carry the chain produces, given loose limbs: at most 3 out of each of
the five base carries, at most 1 out of the two that the `% 2^8` truncations sit
on. Stated over named atoms because omega cannot find these through five nested
divisions on its own. -/
private lemma carry_chain_bounds (a0 a1 a2 a3 a4 c1 c2 c3 c4 c5 c6 c7 : ℕ)
    (h0 : a0 ≤ 0x18000000000000) (h1 : a1 ≤ 0x18000000000000)
    (h2 : a2 ≤ 0x18000000000000) (h3 : a3 ≤ 0x18000000000000)
    (h4 : a4 ≤ 0x18000000000000)
    (e1 : c1 = a0 / 2 ^ 51) (e2 : c2 = (c1 + a1) / 2 ^ 51)
    (e3 : c3 = (c2 + a2) / 2 ^ 51) (e4 : c4 = (c3 + a3) / 2 ^ 51)
    (e5 : c5 = (c4 + a4) / 2 ^ 51) (e6 : c6 = (a0 % 2 ^ 51 + c5 * 19) / 2 ^ 51)
    (e7 : c7 = (c6 % 2 ^ 8 + (c1 + a1) % 2 ^ 51) / 2 ^ 51) :
    c1 ≤ 3 ∧ c2 ≤ 3 ∧ c3 ≤ 3 ∧ c4 ≤ 3 ∧ c5 ≤ 3 ∧ c6 ≤ 1 ∧ c7 ≤ 1 := by
  have b1 : c1 ≤ 3 := by omega
  have b2 : c2 ≤ 3 := by omega
  have b3 : c3 ≤ 3 := by omega
  have b4 : c4 ≤ 3 := by omega
  have b5 : c5 ≤ 3 := by omega
  have b6 : c6 ≤ 1 := by omega
  have b7 : c7 ≤ 1 := by omega
  exact ⟨b1, b2, b3, b4, b5, b6, b7⟩

open Lean Elab Tactic in
/-- The shared opening of both carry proofs: name the seven carries as `c1 … c7`
with defining equations `e1 … e7`, bring their bounds in as `b1 … b7`, make the
names opaque, and discharge the two `% 2^8` truncations. What is left is linear
in named atoms, which is the only shape omega can handle here.

Expects `input` and `h0 … h4` in scope, and a goal mentioning the chain. -/
local elab "carry_setup" : tactic => do
  let name (s : String) := mkIdent (Name.mkSimple s)
  let c i := name s!"c{i}"
  let e i := name s!"e{i}"
  let b i := name s!"b{i}"
  let h i := name s!"h{i}"
  let inp := name "input"
  let t6 := name "t6"
  let t7 := name "t7"
  evalTactic (← `(tactic| set $(c 1):ident := ($inp 0) / 2 ^ 51 with $(e 1):ident))
  evalTactic (← `(tactic| set $(c 2):ident := ($(c 1) + $inp 1) / 2 ^ 51 with $(e 2):ident))
  evalTactic (← `(tactic| set $(c 3):ident := ($(c 2) + $inp 2) / 2 ^ 51 with $(e 3):ident))
  evalTactic (← `(tactic| set $(c 4):ident := ($(c 3) + $inp 3) / 2 ^ 51 with $(e 4):ident))
  evalTactic (← `(tactic| set $(c 5):ident := ($(c 4) + $inp 4) / 2 ^ 51 with $(e 5):ident))
  evalTactic (← `(tactic|
    set $(c 6):ident := (($inp 0) % 2 ^ 51 + $(c 5) * 19) / 2 ^ 51 with $(e 6):ident))
  evalTactic (← `(tactic|
    set $(c 7):ident := ($(c 6) % 2 ^ 8 + ($(c 1) + $inp 1) % 2 ^ 51) / 2 ^ 51 with $(e 7):ident))
  evalTactic (← `(tactic|
    obtain ⟨$(b 1):ident, $(b 2):ident, $(b 3):ident, $(b 4):ident, $(b 5):ident, $(b 6):ident,
        $(b 7):ident⟩ :=
      carry_chain_bounds ($inp 0) ($inp 1) ($inp 2) ($inp 3) ($inp 4)
        $(c 1) $(c 2) $(c 3) $(c 4) $(c 5) $(c 6) $(c 7)
        $(h 0) $(h 1) $(h 2) $(h 3) $(h 4)
        $(e 1) $(e 2) $(e 3) $(e 4) $(e 5) $(e 6) $(e 7)))
  evalTactic (← `(tactic|
    have $t6:ident : $(c 6) % 2 ^ 8 = $(c 6) := Nat.mod_eq_of_lt (by omega)))
  evalTactic (← `(tactic|
    have $t7:ident : $(c 7) % 2 ^ 8 = $(c 7) := Nat.mod_eq_of_lt (by omega)))
  evalTactic (← `(tactic| rw [$t6:term] at $(e 7):ident))
  evalTactic (← `(tactic| rw [$t6:term, $t7:term]))

/-- The chain trades one `2^255` out of the top limb for `19` in the bottom one,
so the represented element is unchanged. The bound is what keeps the two `% 2^8`
carry truncations from losing anything. -/
lemma carry_eq_value (input : Fin 5 → Nat) (hi : ∀ i : Fin 5, input i ≤ 0x18000000000000) :
    decodeFieldElem input = decodeFieldElem (carry_repr input) := by
  have h0 := hi 0; have h1 := hi 1; have h2 := hi 2; have h3 := hi 3; have h4 := hi 4
  obtain ⟨x8, x9, x10, x11, x12, c5, hrepr, key⟩ :
      ∃ x8 x9 x10 x11 x12 c5 : ℕ,
        carry_repr input = ![x8, x9, x10, x11, x12] ∧
        input 0 + input 1 * 2 ^ 51 + input 2 * 2 ^ 102 + input 3 * 2 ^ 153
              + input 4 * 2 ^ 204 + 19 * c5
          = x8 + x9 * 2 ^ 51 + x10 * 2 ^ 102 + x11 * 2 ^ 153 + x12 * 2 ^ 204
              + c5 * 2 ^ 255 := by
    refine ⟨_, _, _, _, _,
      ((((input 0 / 2 ^ 51 + input 1) / 2 ^ 51 + input 2) / 2 ^ 51 + input 3) / 2 ^ 51
        + input 4) / 2 ^ 51, rfl, ?_⟩
    carry_setup
    omega
  have h255 : (2 : ZMod _root_.p) ^ 255 = 19 := by
    have hp : (2 : ℕ) ^ 255 = _root_.p + 19 := by norm_num [_root_.p]
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self, zero_add]
      using congrArg (fun n : ℕ => (n : ZMod _root_.p)) hp
  have hcast := congrArg (fun n : ℕ => (n : ZMod _root_.p)) key
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
  rw [hrepr]
  have v0 : ((0 : Fin 5) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 5) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have v4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  simp only [decodeFieldElem, Fin.toNat_eq_val, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, v0, v1, v2, v3, v4]
  linear_combination hcast + (c5 : ZMod _root_.p) * h255

/-- fiat's tight bound, and it is tight: `carry_repr` can land exactly on `2^51`
(e.g. `![2^51-1, 2^51-1, 2^51-1, 0, 2^51]`), so this cannot be strengthened to
`<`. Both constants are fiat-crypto's inclusive `[0x0 ~> _]` bounds. -/
lemma carry_bounds (input : Fin 5 → Nat) (hi : ∀ i : Fin 5, input i ≤ 0x18000000000000) :
    ∀ i : Fin 5, carry_repr input i ≤ 0x8000000000000 := by
  have h0 := hi 0; have h1 := hi 1; have h2 := hi 2; have h3 := hi 3; have h4 := hi 4
  intro i
  simp only [carry_repr]
  carry_setup
  -- one bound per limb, each small enough for omega
  have k0 : (input 0 % 2 ^ 51 + c5 * 19) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  have k1 : (c6 + (c1 + input 1) % 2 ^ 51) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  have k2 : c7 + (c2 + input 2) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  have k3 : (c3 + input 3) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  have k4 : (c4 + input 4) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  exact forall_fin5 k0 k1 k2 k3 k4 i

/-! ### The carry chain over `BitVec 64`

`fiat_25519_carry` runs `carry_repr`'s chain in 64-bit registers. At fiat's input
bound no step wraps, so each register's `toNat` is exactly the corresponding `ℕ`
step -- which is what discharges the region's `nsw`/`nuw` overflow flags. The
invariant carried along is `≤ 0x18000000000003`: fiat's limb bound plus the most
a carry can add. -/

/-- One `lshr 51; add limb` step, over `toNat`. -/
theorem carry_step_toNat {prev : BitVec 64} {n : ℕ}
    (hprev : prev.toNat ≤ 0x18000000000003) (hn : n ≤ 0x18000000000000) :
    ((prev >>> 51#64) + BitVec.ofNat 64 n).toNat = prev.toNat / 2 ^ 51 + n := by
  rw [BitVec.toNat_add, shift_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- ... and the same step preserves the invariant. -/
theorem carry_step_le {prev : BitVec 64} {n : ℕ}
    (hprev : prev.toNat ≤ 0x18000000000003) (hn : n ≤ 0x18000000000000) :
    ((prev >>> 51#64) + BitVec.ofNat 64 n).toNat ≤ 0x18000000000003 := by
  rw [carry_step_toNat hprev hn]; omega

open Lean Elab Tactic in
/-- `peel_input i, p, hp, s` consumes limb `i`'s `getelementptr` and `load`, and
leaves its value as `input i` rather than as block bytes: `peel_gep_limb` + `peel_limb`,
then `limb<i> = BitVec.ofNat 64 (input i)` rewritten into the goal, so the stepper
produces every later `hv<n>` in terms of `input`.

Carry-proof-local: it reads `hbits`, `hoff` and `input` out of the context by
name, the way `peel_limb` reads `s`. For `i = 0` there is no gep -- use
`peel_limb 0, p, hp, blk, hblk` and `hbits 0 p.offsetInBits (by simp)` directly. -/
elab "peel_input " i:num ", " p:term ", " hp:term ", " st:term : tactic => do
  let num := i.getNat
  let offBytes := Syntax.mkNumLit (toString (num * 8))
  let s := subscript num
  let ptr := mkIdent (Name.mkSimple ("p" ++ s))
  let hptr := mkIdent (Name.mkSimple ("hp" ++ s))
  let limb := mkIdent (Name.mkSimple ("limb" ++ s))
  let hlimb := mkIdent (Name.mkSimple ("hlimb" ++ s))
  let hin := mkIdent (Name.mkSimple ("hin" ++ s))
  let hbits := mkIdent (Name.mkSimple "hbits")
  let hoff := mkIdent (Name.mkSimple "hoff")
  let inp := mkIdent (Name.mkSimple "input")
  let baseblk := mkIdent (Name.mkSimple "blk")
  let basehblk := mkIdent (Name.mkSimple "hblk")
  evalTactic (← `(tactic| peel_gep_limb $i, $p, $hp, $st, p))
  evalTactic (← `(tactic| peel_limb $i, $ptr, $hptr, $baseblk, $basehblk))
  evalTactic (← `(tactic| have $hin:ident : $limb = BitVec.ofNat 64 ($inp $i) :=
      Eq.trans $hlimb ($hbits $i _ ($hoff $i $offBytes (by simp)))))
  evalTactic (← `(tactic| rw [$hin:ident]))
  evalTactic (← `(tactic| clear $hin $hlimb $limb $hptr))

set_option maxHeartbeats 3200000 in
theorem fiat_25519_carry_conforms (q p₀: Pointer) (s: GlobalState)
  (hlimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p₀ i s.mem = some l → l ≤ 0x18000000000000)
  (hq : IsFieldElemPtr s.mem q)
  (hp₀ : IsFieldElemPtr s.mem p₀) :
  fiat_25519_carry_spec q p₀ s := by
    simp only [fiat_25519_carry_spec, Cfg.denote]

    obtain ⟨blk, hblk, hlen⟩ := id hp₀.left
    obtain ⟨input, hinput⟩ := exists_limbs hblk
    let output := carry_repr input
    let outputBV := BitVec.ofNat 64 ∘ output

    refine ⟨outputBV 4 ++ outputBV 3 ++ outputBV 2 ++ outputBV 1 ++ outputBV 0, ?_⟩

    constructor
    pick_goal 2

    simp [readFieldElem?, hq, limbReadback s.mem q, outputBV, hinput]

    have hb : ∀ i : Fin 5, input i ≤ 0x18000000000000 := fun i => hlimb i _ (hinput i)
    have hcb := carry_bounds input hb

    constructor
    · -- the carried limbs decode to the input's value: every 64-bit truncation
      -- is an identity, so this is `carry_eq_value` verbatim
      have hvin : (![input 0, input 1, input 2, input 3, input 4] : Fin 5 → ℕ) = input := by
        funext i; fin_cases i <;> rfl
      have hvout : (![output 0 % 18446744073709551616, output 1 % 18446744073709551616,
          output 2 % 18446744073709551616, output 3 % 18446744073709551616,
          output 4 % 18446744073709551616] : Fin 5 → ℕ) = carry_repr input := by
        funext i
        fin_cases i <;> exact Nat.mod_eq_of_lt ((hcb _).trans_lt (by norm_num))
      rw [hvin, hvout]
      exact (carry_eq_value input hb).symm
    · -- every limb is within fiat's bound, hence small enough that `ofNat` does
      -- not truncate
      intro i
      fin_cases i <;> exact (Nat.mod_le _ _).trans (hcb _)

    -- What the region actually leaves behind: five 64-bit writes at `q`, eight
    -- bytes apart, in program order. That this is the spec's single 320-bit
    -- splice is the `≈` obligation below.
    let output_state : GlobalState :=
      { s with
        mem := ((((s.mem.splice q (outputBV 0)).splice (q.withOffset 8) (outputBV 1)).splice
                  (q.withOffset 16) (outputBV 2)).splice (q.withOffset 24) (outputBV 3)).splice
                  (q.withOffset 32) (outputBV 4) }
    refine ⟨output_state, ?_, ?_⟩

    simp only [fiat_25519_carry]

    denote_step_all v 6
    denote_eval v 0 6
    simp only [LLVM.const?] at hv0 hv1 hv2 hv3 hv4 hv5 hv6
    subst hv0 hv1 hv2 hv3 hv4 hv5 hv6

    peel_load (.bitvec (.concrete 64)), blk, p₀, hblk, s

    denote_step_all v 8
    denote_eval v 8 8
    have hbits : ∀ (i : Fin 5) (off : ℕ), off = p₀.offsetInBits + 64 * i.toNat →
        blk.bytes.extractLsb' off 64 = BitVec.ofNat 64 (input i) := limbBits hblk hinput
    have hoff : ∀ (i : Fin 5) (o : BitVec 64), o.toNat = 8 * i.toNat →
        (p₀.withOffset o).offsetInBits = p₀.offsetInBits + 64 * i.toNat :=
      fun i _ ho => limbOffsetInBits hp₀.right (by have : i.toNat < 5 := i.isLt; omega) ho

    -- `%7` has no gep, so its value is limb 0 at the bare offset. Rewrite it in
    -- the *goal*, not just in `hv8`: `%7` is used again at `%24`, and anything
    -- left in the valuation spine comes back as block bytes.
    have hin₀ : blk.bytes.extractLsb' p₀.offsetInBits 64 = BitVec.ofNat 64 (input 0) :=
      hbits 0 p₀.offsetInBits (by simp)
    rw [hin₀]

    eval_llvm 8 [hin₀] as x2₀

    -- %9-%10: limb 1's address and value
    peel_input 1, p₀, hp₀.left, s

    denote_step_all v 12
    denote_eval v 11 12
    eval_llvm 11 as x2
    eval_llvm 12 as x3₀

    peel_input 2, p₀, hp₀.left, s
    denote_step_all v 16
    denote_eval v 15 16
    eval_llvm 15 as x3
    eval_llvm 16 as x4₀

    peel_input 3, p₀, hp₀.left, s
    denote_step_all v 20
    denote_eval v 19 20
    eval_llvm 19 as x4
    eval_llvm 20 as x5₀

    peel_input 4, p₀, hp₀.left, s
    denote_step_all v 23
    denote_eval v 23 23
    eval_llvm 23 as x5

    -- The chain, over `toNat`: `x<k>` is `carry_repr`'s `x<k>`, and every step
    -- stays inside the invariant, so nothing wrapped. These are the facts the
    -- region's `nsw`/`nuw` flags need.
    have hb : ∀ i : Fin 5, input i ≤ 0x18000000000000 := fun i => hlimb i _ (hinput i)
    have b1 : (BitVec.ofNat 64 (input 0)).toNat ≤ 0x18000000000003 := by
      rw [BitVec.toNat_ofNat]; have := hb 0; omega
    have n2 : x2.toNat = (BitVec.ofNat 64 (input 0)).toNat / 2 ^ 51 + input 1 := by
      rw [← hx2, ← hx2₀]; exact carry_step_toNat b1 (hb 1)
    have b2 : x2.toNat ≤ 0x18000000000003 := by
      rw [← hx2, ← hx2₀]; exact carry_step_le b1 (hb 1)
    have n3 : x3.toNat = x2.toNat / 2 ^ 51 + input 2 := by
      rw [← hx3, ← hx3₀]; exact carry_step_toNat b2 (hb 2)
    have b3 : x3.toNat ≤ 0x18000000000003 := by
      rw [← hx3, ← hx3₀]; exact carry_step_le b2 (hb 2)
    have n4 : x4.toNat = x3.toNat / 2 ^ 51 + input 3 := by
      rw [← hx4, ← hx4₀]; exact carry_step_toNat b3 (hb 3)
    have b4 : x4.toNat ≤ 0x18000000000003 := by
      rw [← hx4, ← hx4₀]; exact carry_step_le b3 (hb 3)
    have n5 : x5.toNat = x4.toNat / 2 ^ 51 + input 4 := by
      rw [← hx5, ← hx5₀]; exact carry_step_toNat b4 (hb 4)
    have b5 : x5.toNat ≤ 0x18000000000003 := by
      rw [← hx5, ← hx5₀]; exact carry_step_le b4 (hb 4)
    -- the top carry, which is what `%26`'s `mul 19` consumes
    have s5 : (x5 >>> 51#64).toNat ≤ 3 := by rw [shift_toNat]; omega

    denote_step_all v 27
    denote_eval v 24 27
    eval_llvm 24
    eval_llvm 25
    obtain ⟨g26s, g26u⟩ := mul19_no_overflow s5
    eval_llvm 26 [g26s, g26u]
    obtain ⟨g27s, g27u⟩ := add_no_overflow (u := (x5 >>> 51#64) * 19#64)
      (v := BitVec.ofNat 64 (input 0) &&& 2251799813685247#64)
      (by rw [mul19_toNat (by omega), mask_toNat]; omega)
    eval_llvm 27 [g27s, g27u] as x6

    -- `%28` is `x6`'s carry, at most 1: `%27` added only `3 * 19` on top of a
    -- masked limb. `%29` is a masked limb.
    have b6 : x6.toNat ≤ 2 ^ 51 + 56 := by
      rw [← hx6]; exact mul19_add_toNat_le s5 (mask_toNat_lt _)
    denote_step_all v 30
    denote_eval v 28 30
    eval_llvm 28
    eval_llvm 29
    obtain ⟨g30s, g30u⟩ := add_no_overflow (u := x6 >>> 51#64)
      (v := x2 &&& 2251799813685247#64) (by rw [shift_toNat, mask_toNat]; omega)
    eval_llvm 30 [g30s, g30u] as x7

    denote_step_all v 32
    denote_eval v 31 32
    eval_llvm 31 as x8
    eval_llvm 32 as x9

    -- `%33` is `x7`'s carry. `x7` is a carry of at most 1 on top of a masked
    -- limb, so it barely exceeds `2^51` and carries at most 1 itself.
    have b7 : x7.toNat ≤ 2 ^ 51 + 2 := by
      rw [← hx7]; exact add_toNat_le (by rw [shift_toNat]; omega) (mask_toNat_lt _)
    denote_step_all v 35
    denote_eval v 33 35
    eval_llvm 33
    eval_llvm 34
    obtain ⟨g35s, g35u⟩ := add_no_overflow (u := x7 >>> 51#64)
      (v := x3 &&& 2251799813685247#64) (by rw [shift_toNat, mask_toNat]; omega)
    eval_llvm 35 [g35s, g35u] as x10

    denote_step_all v 37
    denote_eval v 36 37
    eval_llvm 36 as x11
    eval_llvm 37 as x12

    -- The five registers the stores consume are `carry_repr`'s limbs. `n2 … n5`
    -- already put `x2 … x5` on the `ℕ` chain; these carry that through the
    -- final `lshr`/`and` layer. `carry_repr`'s two `% 2 ^ 8` carry truncations
    -- are identities here, because `b6`/`b7` keep both carries at most 1.
    have ha0 : (BitVec.ofNat 64 (input 0)).toNat = input 0 := by
      rw [BitVec.toNat_ofNat]; have := hb 0; omega
    have c1 : x2.toNat = input 0 / 2 ^ 51 + input 1 := by rw [n2, ha0]
    have n6 : x6.toNat = input 0 % 2 ^ 51 + x5.toNat / 2 ^ 51 * 19 := by
      rw [← hx6, mul19_add_toNat s5 (mask_toNat_lt _), shift_toNat, mask_toNat, ha0]
      omega
    have n7 : x7.toNat = x6.toNat / 2 ^ 51 + x2.toNat % 2 ^ 51 := by
      rw [← hx7, add_toNat (by rw [shift_toNat]; omega) (mask_toNat_lt _), shift_toNat, mask_toNat]
    have n10 : x10.toNat = x7.toNat / 2 ^ 51 + x3.toNat % 2 ^ 51 := by
      rw [← hx10, add_toNat (by rw [shift_toNat]; omega) (mask_toNat_lt _), shift_toNat, mask_toNat]

    have hchain : carry_repr input
        = ![x8.toNat, x9.toNat, x10.toNat, x11.toNat, x12.toNat] := by
      have m8 : x8.toNat = x6.toNat % 2 ^ 51 := by rw [← hx8, mask_toNat]
      have m9 : x9.toNat = x7.toNat % 2 ^ 51 := by rw [← hx9, mask_toNat]
      have m11 : x11.toNat = x4.toNat % 2 ^ 51 := by rw [← hx11, mask_toNat]
      have m12 : x12.toNat = x5.toNat % 2 ^ 51 := by rw [← hx12, mask_toNat]
      have t6 : x6.toNat / 2 ^ 51 % 2 ^ 8 = x6.toNat / 2 ^ 51 := Nat.mod_eq_of_lt (by omega)
      have t7 : x7.toNat / 2 ^ 51 % 2 ^ 8 = x7.toNat / 2 ^ 51 := Nat.mod_eq_of_lt (by omega)
      simp only [carry_repr]
      rw [← c1, ← n3, ← n4, ← n5, ← n6, t6, ← n7, t7, ← n10, ← m8, ← m9, ← m11, ← m12]

    -- `x<k> = outputBV i` -- so the stores below write the spec's limbs, and
    -- `output_state` is exactly the state the run ends in
    have hout : ∀ (u : BitVec 64) (i : Fin 5), u.toNat = output i → u = outputBV i :=
      fun _ _ h => eq_ofNat_of_toNat h
    rw [hout x8 0 (by simp [output, hchain])] at hv31
    rw [hout x9 1 (by simp [output, hchain])] at hv32
    rw [hout x10 2 (by simp [output, hchain])] at hv35
    rw [hout x11 3 (by simp [output, hchain])] at hv36
    rw [hout x12 4 (by simp [output, hchain])] at hv37
    rw [hv31, hv32, hv35, hv36, hv37]

    -- The five stores, limb 0 first. A `store` binds nothing, so `peel_store`
    -- only moves the state; naming each state keeps the next `Fits` obligation
    -- -- and the `getelementptr` that follows it -- readable. `fits_splice`
    -- carries `q`'s room across a store, since a store changes no block's size.
    store_limbs outputBV, q, hq.left, s

    -- `llvm.return`: nothing is left but the state, which is `output_state`
    simp only [BlockCom.denote_term, Terminator.denote_ret, output_state, simp_sllvm,
      hs₁, hs₂, hs₃, hs₄, q₁, q₂, q₃, q₄]
    rfl

    exact GlobalState.Equiv.symm (splice5_equiv (outputBV 0) (outputBV 1) (outputBV 2)
      (outputBV 3) (outputBV 4) hq)

end Firedancer.Ref
