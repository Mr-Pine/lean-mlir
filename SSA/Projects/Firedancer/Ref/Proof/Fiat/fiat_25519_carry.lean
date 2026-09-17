module

public import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_carry
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_carry
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
public import SSA.Projects.Firedancer.Ref.Proof.Limb

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

def carry_repr (input : Fin 5 → Nat) :=
  let x1 := input 0
  let x2 := (x1 / 2 ^ 51) + input 1
  let x3 := (x2 / 2 ^ 51) + input 2
  let x4 := (x3 / 2 ^ 51) + input 3
  let x5 := (x4 / 2 ^ 51) + input 4
  let x6 := (x1 % 2 ^ 51) + (x5 / 2 ^ 51) * 0x13
  let x7 := (x6 / 2 ^ 51 % 2 ^ 8) + (x2 % 2 ^ 51)
  let x8 := x6 % 2 ^ 51
  let x9 := x7 % 2 ^ 51
  let x10 := (x7 / 2 ^ 51 % 2 ^ 8) + (x3 % 2 ^ 51)
  let x11 := x4 % 2 ^ 51
  let x12 := x5 % 2 ^ 51
  ![x8, x9, x10, x11, x12]

/-- Every carry the chain produces, given loose limbs: at most 3 out of each of
the five base carries, at most 1 out of the two that the `% 2^8` truncations sit
on. Stated over named atoms because omega cannot find these through five nested
divisions on its own. -/
private lemma carry_chain_bounds (a0 a1 a2 a3 a4 c1 c2 c3 c4 c5 c6 c7 : ℕ)
    (h0 : a0 ≤ 0x18000000000000) (h1 : a1 ≤ 0x18000000000000) (h2 : a2 ≤ 0x18000000000000)
    (h3 : a3 ≤ 0x18000000000000) (h4 : a4 ≤ 0x18000000000000) (e1 : c1 = a0 / 2 ^ 51)
    (e2 : c2 = (c1 + a1) / 2 ^ 51) (e3 : c3 = (c2 + a2) / 2 ^ 51) (e4 : c4 = (c3 + a3) / 2 ^ 51)
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
  evalTactic
      (←
        `(tactic| set $(c 6):ident := (($inp 0) % 2 ^ 51 + $(c 5) * 19) / 2 ^ 51 with $(e 6):ident))
  evalTactic
      (←
        `(tactic|
            set $(c 7):ident := ($(c 6) % 2 ^ 8 + ($(c 1) + $inp 1) % 2 ^ 51) / 2 ^ 51 with
              $(e 7):ident))
  evalTactic
      (←
        `(tactic|
            obtain
              ⟨$(b 1):ident, $(b 2):ident, $(b 3):ident, $(b 4):ident, $(b 5):ident, $(b 6):ident,
                $(b 7):ident⟩ :=
              carry_chain_bounds ($inp 0) ($inp 1) ($inp 2) ($inp 3) ($inp 4) $(c 1) $(c 2) $(c 3)
                $(c 4) $(c 5) $(c 6) $(c 7) $(h 0) $(h 1) $(h 2) $(h 3) $(h 4) $(e 1) $(e 2) $(e 3)
                $(e 4) $(e 5) $(e 6) $(e 7)))
  evalTactic (← `(tactic| have $t6:ident : $(c 6) % 2 ^ 8 = $(c 6) := Nat.mod_eq_of_lt (by omega)))
  evalTactic (← `(tactic| have $t7:ident : $(c 7) % 2 ^ 8 = $(c 7) := Nat.mod_eq_of_lt (by omega)))
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
        input 0 + input 1 * 2 ^ 51 + input 2 * 2 ^ 102 + input 3 * 2 ^ 153 + input 4 * 2 ^ 204 +
            19 * c5 =
          x8 + x9 * 2 ^ 51 + x10 * 2 ^ 102 + x11 * 2 ^ 153 + x12 * 2 ^ 204 + c5 * 2 ^ 255 :=
    by
    refine
      ⟨_, _, _, _, _,
        ((((input 0 / 2 ^ 51 + input 1) / 2 ^ 51 + input 2) / 2 ^ 51 + input 3) / 2 ^ 51 +
            input 4) /
          2 ^ 51,
        rfl, ?_⟩
    carry_setup
    omega
  have h255 : (2 : ZMod _root_.p) ^ 255 = 19 := by
    have hp : (2 : ℕ) ^ 255 = _root_.p + 19 := by norm_num [_root_.p]
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self, zero_add] using
      congrArg (fun n : ℕ => (n : ZMod _root_.p)) hp
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

/-- All-zero carried limbs come only from an all-zero input. -/
lemma carry_repr_eq_zero (input : Fin 5 → ℕ) (hi : ∀ i : Fin 5, input i ≤ 0x18000000000000)
    (h : ∀ i, carry_repr input i = 0) : ∀ i, input i = 0 := by
  have h0 := hi 0; have h1 := hi 1; have h2 := hi 2; have h3 := hi 3; have h4 := hi 4
  have z0 := h 0; have z1 := h 1; have z2 := h 2; have z3 := h 3; have z4 := h 4
  simp only [carry_repr, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at z0 z1 z2 z3 z4
  suffices hz : input 0 = 0 ∧ input 1 = 0 ∧ input 2 = 0 ∧ input 3 = 0 ∧ input 4 = 0 by
    intro i; fin_cases i <;> simp [hz]
  -- the carries as atoms, so omega sees a linear chain
  generalize input 0 = a0 at *
  generalize input 1 = a1 at *
  generalize input 2 = a2 at *
  generalize input 3 = a3 at *
  generalize input 4 = a4 at *
  generalize hc1 : a0 / 2 ^ 51 = c1 at *
  generalize hc2 : (c1 + a1) / 2 ^ 51 = c2 at *
  generalize hc3 : (c2 + a2) / 2 ^ 51 = c3 at *
  generalize hc4 : (c3 + a3) / 2 ^ 51 = c4 at *
  generalize hc5 : (c4 + a4) / 2 ^ 51 = c5 at *
  have b5 : c5 ≤ 3 := by omega
  generalize hc6 : (a0 % 2 ^ 51 + c5 * 19) / 2 ^ 51 = c6 at *
  have t6 : c6 % 2 ^ 8 = c6 := Nat.mod_eq_of_lt (by omega)
  rw [t6] at z1 z2
  generalize hc7 : (c6 + (c1 + a1) % 2 ^ 51) / 2 ^ 51 = c7 at *
  have t7 : c7 % 2 ^ 8 = c7 := Nat.mod_eq_of_lt (by omega)
  rw [t7] at z2
  omega

/-! ### The carry chain over `BitVec 64`

`fiat_25519_carry` runs `carry_repr`'s chain in 64-bit registers. At fiat's input
bound no step wraps, so each register's `toNat` is exactly the corresponding `ℕ`
step -- which is what discharges the region's `nsw`/`nuw` overflow flags. The
invariant carried along is `≤ 0x18000000000003`: fiat's limb bound plus the most
a carry can add. -/

/-- `lshr 51`, over `toNat`. -/
theorem shr51_toNat (x : BitVec 64) : (x >>> (51 : ℕ)).toNat = x.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- One `lshr 51; add limb` step, over `toNat`. -/
theorem carry_step_toNat {prev : BitVec 64} {n : ℕ} (hprev : prev.toNat ≤ 0x18000000000003)
    (hn : n ≤ 0x18000000000000) :
    ((prev >>> (51 : ℕ)) + BitVec.ofNat 64 n).toNat = prev.toNat / 2 ^ 51 + n := by
  rw [BitVec.toNat_add, shr51_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- ... and the same step preserves the invariant. -/
theorem carry_step_le {prev : BitVec 64} {n : ℕ} (hprev : prev.toNat ≤ 0x18000000000003)
    (hn : n ≤ 0x18000000000000) :
    ((prev >>> (51 : ℕ)) + BitVec.ofNat 64 n).toNat ≤ 0x18000000000003 := by
  rw [carry_step_toNat hprev hn]; omega

/-- The chain's registers as `denote_step_reduce` leaves them: no `nsw`/`nuw` guard
fires, and the stored `%27 %28 %31 %32 %33` are `carry_repr`'s limbs. -/
theorem carry_registers {x2 x3 x4 x5 x6 x7 x10 : BitVec 64} (input : Fin 5 → ℕ)
    (hb : ∀ i : Fin 5, input i ≤ 0x18000000000000)
    (hx2 : x2 = (BitVec.ofNat 64 (input 0) >>> (51 : ℕ)) + BitVec.ofNat 64 (input 1))
    (hx3 : x3 = (x2 >>> (51 : ℕ)) + BitVec.ofNat 64 (input 2))
    (hx4 : x4 = (x3 >>> (51 : ℕ)) + BitVec.ofNat 64 (input 3))
    (hx5 : x5 = (x4 >>> (51 : ℕ)) + BitVec.ofNat 64 (input 4))
    (hx6 : x6 = (x5 >>> (51 : ℕ)) * 19#64 + (BitVec.ofNat 64 (input 0) &&& 2251799813685247#64))
    (hx7 : x7 = (x6 >>> (51 : ℕ)) + (x2 &&& 2251799813685247#64))
    (hx10 : x10 = (x7 >>> (51 : ℕ)) + (x3 &&& 2251799813685247#64)) :
    ((x5 >>> (51 : ℕ)).smulOverflow 19#64 = false ∧ (x5 >>> (51 : ℕ)).umulOverflow 19#64 = false) ∧
      (((x5 >>> (51 : ℕ)) * 19#64).saddOverflow
            (BitVec.ofNat 64 (input 0) &&& 2251799813685247#64) =
          false ∧
        ((x5 >>> (51 : ℕ)) * 19#64).uaddOverflow
            (BitVec.ofNat 64 (input 0) &&& 2251799813685247#64) =
          false) ∧
      ((x6 >>> (51 : ℕ)).saddOverflow (x2 &&& 2251799813685247#64) = false ∧
        (x6 >>> (51 : ℕ)).uaddOverflow (x2 &&& 2251799813685247#64) = false) ∧
      ((x7 >>> (51 : ℕ)).saddOverflow (x3 &&& 2251799813685247#64) = false ∧
        (x7 >>> (51 : ℕ)).uaddOverflow (x3 &&& 2251799813685247#64) = false) ∧
      x6 &&& 2251799813685247#64 = (BitVec.ofNat 64 ∘ carry_repr input) 0 ∧
      x7 &&& 2251799813685247#64 = (BitVec.ofNat 64 ∘ carry_repr input) 1 ∧
      x10 = (BitVec.ofNat 64 ∘ carry_repr input) 2 ∧
      x4 &&& 2251799813685247#64 = (BitVec.ofNat 64 ∘ carry_repr input) 3 ∧
      x5 &&& 2251799813685247#64 = (BitVec.ofNat 64 ∘ carry_repr input) 4 := by
  -- first pass: every register is at most `0x18000000000003`
  have ha0 : (BitVec.ofNat 64 (input 0)).toNat = input 0 := by
    rw [BitVec.toNat_ofNat]; have := hb 0; omega
  have b1 : (BitVec.ofNat 64 (input 0)).toNat ≤ 0x18000000000003 := by
    rw [ha0]; have := hb 0; omega
  have c1 : x2.toNat = input 0 / 2 ^ 51 + input 1 := by rw [hx2, carry_step_toNat b1 (hb 1), ha0]
  have b2 : x2.toNat ≤ 0x18000000000003 := hx2 ▸ carry_step_le b1 (hb 1)
  have n3 : x3.toNat = x2.toNat / 2 ^ 51 + input 2 := hx3 ▸ carry_step_toNat b2 (hb 2)
  have b3 : x3.toNat ≤ 0x18000000000003 := hx3 ▸ carry_step_le b2 (hb 2)
  have n4 : x4.toNat = x3.toNat / 2 ^ 51 + input 3 := hx4 ▸ carry_step_toNat b3 (hb 3)
  have b4 : x4.toNat ≤ 0x18000000000003 := hx4 ▸ carry_step_le b3 (hb 3)
  have n5 : x5.toNat = x4.toNat / 2 ^ 51 + input 4 := hx5 ▸ carry_step_toNat b4 (hb 4)
  have b5 : x5.toNat ≤ 0x18000000000003 := hx5 ▸ carry_step_le b4 (hb 4)
  -- second pass: the top carry is at most 3, the two after it at most 1
  have s5 : (x5 >>> (51 : ℕ)).toNat ≤ 3 := by
    rw [shr51_toNat]; omega
  have b6 : x6.toNat ≤ 2 ^ 51 + 56 := hx6 ▸ mul19_add_toNat_le s5 (mask_toNat_lt _)
  have s6 : (x6 >>> (51 : ℕ)).toNat ≤ 3 := by
    rw [shr51_toNat]; omega
  have b7 : x7.toNat ≤ 2 ^ 51 + 2 := hx7 ▸ add_toNat_le s6 (mask_toNat_lt _)
  have s7 : (x7 >>> (51 : ℕ)).toNat ≤ 3 := by
    rw [shr51_toNat]; omega
  have n6 : x6.toNat = input 0 % 2 ^ 51 + x5.toNat / 2 ^ 51 * 19 := by
    rw [hx6, mul19_add_toNat s5 (mask_toNat_lt _), shr51_toNat, mask_toNat, ha0]
    omega
  have n7 : x7.toNat = x6.toNat / 2 ^ 51 + x2.toNat % 2 ^ 51 := by
    rw [hx7, add_toNat s6 (mask_toNat_lt _), shr51_toNat, mask_toNat]
  have n10 : x10.toNat = x7.toNat / 2 ^ 51 + x3.toNat % 2 ^ 51 := by
    rw [hx10, add_toNat s7 (mask_toNat_lt _), shr51_toNat, mask_toNat]
  -- `carry_repr`'s two `% 2 ^ 8` truncations are identities: both carries are at most 1
  have hchain :
    carry_repr input =
      ![(x6 &&& 2251799813685247#64).toNat, (x7 &&& 2251799813685247#64).toNat, x10.toNat,
        (x4 &&& 2251799813685247#64).toNat, (x5 &&& 2251799813685247#64).toNat] := by
    have t6 : x6.toNat / 2 ^ 51 % 2 ^ 8 = x6.toNat / 2 ^ 51 := Nat.mod_eq_of_lt (by omega)
    have t7 : x7.toNat / 2 ^ 51 % 2 ^ 8 = x7.toNat / 2 ^ 51 := Nat.mod_eq_of_lt (by omega)
    simp only [carry_repr]
    rw [← c1, ← n3, ← n4, ← n5, ← n6, t6, ← n7, t7, ← n10, mask_toNat, mask_toNat, mask_toNat,
      mask_toNat]
  refine
    ⟨mul19_no_overflow s5, add_no_overflow ?_, add_no_overflow ?_, add_no_overflow ?_,
      eq_ofNat_of_toNat
        (by
          rw [hchain]; rfl),
      eq_ofNat_of_toNat
        (by
          rw [hchain]; rfl),
      eq_ofNat_of_toNat
        (by
          rw [hchain]; rfl),
      eq_ofNat_of_toNat
        (by
          rw [hchain]; rfl),
      eq_ofNat_of_toNat
        (by
          rw [hchain]; rfl)⟩
  · rw [mul19_toNat (by omega), mask_toNat]; omega
  · rw [shr51_toNat, mask_toNat]; omega
  · rw [shr51_toNat, mask_toNat]; omega

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
theorem fiat_25519_carry_conforms (q p₀ : Pointer) (s : GlobalState) (hs : s.WF)
    (hlimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p₀ i s.mem = some l → l ≤ 0x18000000000000)
    (hq : IsFieldElemPtr s.mem q) (hp₀ : IsFieldElemPtr s.mem p₀) :
    fiat_25519_carry_spec q p₀ s := by
  simp only [fiat_25519_carry_spec, Cfg.denote]
  obtain ⟨blk, hblk, hlen⟩ := id hp₀.left
  obtain ⟨input, hinput⟩ := exists_limbs hblk
  let output := carry_repr input
  let outputBV := BitVec.ofNat 64 ∘ output
  have hb : ∀ i : Fin 5, input i ≤ 0x18000000000000 := fun i => hlimb i _ (hinput i)
  have hcb := carry_bounds input hb
  refine ⟨packLimbs outputBV, ?_, ?val, ?bnd, ?zero⟩
  case zero =>
    intro hz
    have h0 : ∀ i, carry_repr input i = 0 := fun i => by
      have := (limbReadbackPack s.mem q outputBV hq.left i).symm.trans (hz i)
      simp only [outputBV, Function.comp, BitVec.toNat_ofNat, Option.some.injEq] at this
      rwa [Nat.mod_eq_of_lt ((hcb i).trans_lt (by norm_num))] at this
    exact fun i => (hinput i).trans (by rw [carry_repr_eq_zero input hb h0 i])
  case val =>
    simp [readFieldElem?, hq, limbReadbackPack s.mem q, outputBV, hinput]
    -- the carried limbs decode to the input's value: every 64-bit truncation
    -- is an identity, so this is `carry_eq_value` verbatim
    have hvin : (![input 0, input 1, input 2, input 3, input 4] : Fin 5 → ℕ) = input := by
      funext i; fin_cases i <;> rfl
    have hvout :
      (![output 0 % 18446744073709551616, output 1 % 18446744073709551616,
            output 2 % 18446744073709551616, output 3 % 18446744073709551616,
            output 4 % 18446744073709551616] :
          Fin 5 → ℕ) =
        carry_repr input := by
      funext i
      fin_cases i <;> exact Nat.mod_eq_of_lt ((hcb _).trans_lt (by norm_num))
    rw [hvin, hvout]
    exact (carry_eq_value input hb).symm
  case bnd =>
    simp [readFieldElem?, hq, limbReadbackPack s.mem q, outputBV, hinput]
    -- every limb is within fiat's bound, hence small enough that `ofNat` does
    -- not truncate
    intro i
    fin_cases i <;> exact (Nat.mod_le _ _).trans (hcb _)
  -- What the region actually leaves behind: five 64-bit writes at `q`, eight
  -- bytes apart, in program order. That this is the spec's single 320-bit
  -- splice is the `≈` obligation below.
  obtain ⟨outMem, houtMem⟩ :
    ∃ m : MemoryState,
      m =
        ((((s.mem.splice q (outputBV 0)).splice (q.withOffset 8) (outputBV 1)).splice
                  (q.withOffset 16) (outputBV 2)).splice
              (q.withOffset 24) (outputBV 3)).splice
          (q.withOffset 32) (outputBV 4) :=
    ⟨_, rfl⟩
  refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
  case
    equiv =>
    have hnone : ∀ (b : BlockId), s.alloc.nextFreeBlock ≤ b.id → outMem.live? b = none := by
      rw [houtMem]
      exact fun b hb =>
        live?_splice_eq_none
          (live?_splice_eq_none
            (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (hs b hb)))))
    refine
      GlobalState.Equiv.trans ?_
        (GlobalState.Equiv.symm (killFrom_equiv_of_none (s := s) (m := outMem) hnone))
    rw [houtMem]
    exact
      GlobalState.Equiv.symm
        (splice5_equiv (outputBV 0) (outputBV 1) (outputBV 2) (outputBV 3) (outputBV 4) hq)
  simp only [fiat_25519_carry]
  denote_step_reduce v 2 [LLVM.const?] fold
  subst hv0 hv1 hv2
  peel_load (.bitvec (.concrete 64)), blk, p₀, hblk, s
  have hbits :
    ∀ (i : Fin 5) (off : ℕ),
      off = p₀.offsetInBits + 64 * i.toNat →
        blk.bytes.extractLsb' off 64 = BitVec.ofNat 64 (input i) :=
    limbBits hblk hinput
  have hoff :
    ∀ (i : Fin 5) (o : BitVec 64),
      o.toNat = 8 * i.toNat → (p₀.withOffset o).offsetInBits = p₀.offsetInBits + 64 * i.toNat :=
    fun i _ ho =>
    limbOffsetInBits hp₀.right
      (by
        have : i.toNat < 5 := i.isLt; omega)
      ho
  -- `%3` is limb 0, with no gep; rewritten in the goal because `%20` reads it again
  rw [hbits 0 p₀.offsetInBits (by simp)]
  denote_step_reduce v 4 [LLVM.lshr, LLVM.lshr?]
  -- `%5 … %19`: the first pass, one limb at a time
  peel_input 1, p₀, hp₀.left, s
  denote_step_reduce v 8 [LLVM.add, LLVM.add?, LLVM.lshr, LLVM.lshr?, hv4] fold
  peel_input 2, p₀, hp₀.left, s
  denote_step_reduce v 12 [LLVM.add, LLVM.add?, LLVM.lshr, LLVM.lshr?, hv8] fold
  peel_input 3, p₀, hp₀.left, s
  denote_step_reduce v 16 [LLVM.add, LLVM.add?, LLVM.lshr, LLVM.lshr?, hv12] fold
  peel_input 4, p₀, hp₀.left, s
  denote_step_reduce v 19 [LLVM.add, LLVM.add?, hv16]
  -- `%20 … %33`: the second pass, its stored registers rewritten to `outputBV`
  have hb : ∀ i : Fin 5, input i ≤ 0x18000000000000 := fun i => hlimb i _ (hinput i)
  have hr := carry_registers input hb rfl rfl rfl rfl rfl rfl rfl
  have ho : ∀ i, BitVec.ofNat 64 (carry_repr input i) = outputBV i := fun _ => rfl
  denote_step_reduce v 33 [LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.mul, LLVM.mul?,
    LLVM.add, LLVM.add?, hv7, hv11, hv15, hv19, hr, ho] fold
  rw [hv27, hv28, hv31, hv32, hv33]
  store_limbs outputBV, q, hq.left, s
  -- `llvm.return`: nothing is left but the state, which is `outMem`
  simp_return
  simp [houtMem, hs₁, hs₂, hs₃, hs₄, q₁, q₂, q₃, q₄]

end Firedancer.Ref
