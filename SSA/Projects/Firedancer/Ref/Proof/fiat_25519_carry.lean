import SSA.Projects.Firedancer.Ref.Spec.fiat_25519_carry
import SSA.Projects.Firedancer.Ref.Mlir.fiat_25519_carry
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations


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
  -- one bound per limb, small enough for omega; `simp` then only has to pick
  -- the right component out of `![...]`
  have k0 : (input 0 % 2 ^ 51 + c5 * 19) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  have k1 : (c6 + (c1 + input 1) % 2 ^ 51) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  have k2 : c7 + (c2 + input 2) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  have k3 : (c3 + input 3) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  have k4 : (c4 + input 4) % 2 ^ 51 ≤ 0x8000000000000 := by omega
  norm_num at k0 k1 k2 k3 k4
  fin_cases i <;> simp <;> omega

/-! ### The carry chain over `BitVec 64`

`fiat_25519_carry` runs `carry_repr`'s chain in 64-bit registers. At fiat's input
bound no step wraps, so each register's `toNat` is exactly the corresponding `ℕ`
step -- which is what discharges the region's `nsw`/`nuw` overflow flags. The
invariant carried along is `≤ 0x18000000000003`: fiat's limb bound plus the most
a carry can add. -/

/-- One `lshr 51; add limb` step, over `toNat`. -/
theorem carry_step_toNat {prev : BitVec 64} {n : ℕ}
    (hprev : prev.toNat ≤ 0x18000000000003) (hn : n ≤ 0x18000000000000) :
    ((prev >>> (51 : ℕ)) + BitVec.ofNat 64 n).toNat = prev.toNat / 2 ^ 51 + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- ... and the same step preserves the invariant. -/
theorem carry_step_le {prev : BitVec 64} {n : ℕ}
    (hprev : prev.toNat ≤ 0x18000000000003) (hn : n ≤ 0x18000000000000) :
    ((prev >>> (51 : ℕ)) + BitVec.ofNat 64 n).toNat ≤ 0x18000000000003 := by
  rw [carry_step_toNat hprev hn]; omega

/-- A shift by 51 is division, over `toNat`. -/
theorem shift_toNat (x : BitVec 64) : (x >>> (51 : ℕ)).toNat = x.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The region's `and` with `2^51 - 1` is reduction mod `2^51`, over `toNat`. -/
theorem mask_toNat (a : BitVec 64) : (a &&& 2251799813685247#64).toNat = a.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]

/-- ... so it bounds a limb below `2^51`. -/
theorem mask_toNat_lt (a : BitVec 64) : (a &&& 2251799813685247#64).toNat < 2 ^ 51 := by
  rw [mask_toNat]; omega

/-- `%26`/`%27`'s `nsw, nuw` guards. All four are `decide` of arithmetic --
the unsigned pair over `toNat`, the signed pair over `toInt` -- and
`toInt_eq_toNat_of_lt` puts them on the same footing, so the carry bound and the
limb bound kill all four at once. -/
theorem mul19_add_no_overflow (c m : BitVec 64) (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (if c.smulOverflow 19#64 = true then (PoisonOr.poison : PoisonOr (BitVec 64))
     else if c.umulOverflow 19#64 = true then PoisonOr.poison
     else if (c * 19#64).saddOverflow m = true then PoisonOr.poison
     else if (c * 19#64).uaddOverflow m = true then PoisonOr.poison
     else PoisonOr.value (c * 19#64 + m))
      = PoisonOr.value (c * 19#64 + m) := by
  have h19 : (19#64).toInt = 19 := by decide
  have hmul : (c * 19#64).toNat = c.toNat * 19 := by
    rw [BitVec.toNat_mul]; simp; omega
  have hci : c.toInt = (c.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hmi : m.toInt = (m.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hpi : (c * 19#64).toInt = ((c * 19#64).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  simp only [BitVec.smulOverflow, BitVec.umulOverflow, BitVec.saddOverflow,
    BitVec.uaddOverflow, hci, hmi, hpi, hmul, h19, BitVec.toNat_ofNat]
  rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega),
    if_neg (by simp; omega)]

/-- A plain `nsw, nuw` add of a small carry onto a masked limb -- `%30` and the
stores' accumulators, which have no `mul` in front. -/
theorem add_no_overflow (c m : BitVec 64) (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (if c.saddOverflow m = true then (PoisonOr.poison : PoisonOr (BitVec 64))
     else if c.uaddOverflow m = true then PoisonOr.poison
     else PoisonOr.value (c + m))
      = PoisonOr.value (c + m) := by
  have hci : c.toInt = (c.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hmi : m.toInt = (m.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  simp only [BitVec.saddOverflow, BitVec.uaddOverflow, hci, hmi]
  rw [if_neg (by simp; omega), if_neg (by simp; omega)]

/-- `%26`/`%27` over `toNat`: at a `≤ 3` carry and a masked limb, neither the
`mul` nor the `add` wraps. -/
theorem mul19_add_toNat {c m : BitVec 64} (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (c * 19#64 + m).toNat = c.toNat * 19 + m.toNat := by
  have hmul : (c * 19#64).toNat = c.toNat * 19 := by
    rw [BitVec.toNat_mul]; simp; omega
  rw [BitVec.toNat_add, hmul, Nat.mod_eq_of_lt (by omega)]

/-- `%27`'s value sits just above a masked limb, so its own carry is at most 1 --
which is what lets `%30` reuse the `≤ 3` bound. -/
theorem mul19_add_toNat_le {c m : BitVec 64} (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (c * 19#64 + m).toNat ≤ 2 ^ 51 + 56 := by
  rw [mul19_add_toNat hc hm]; omega

/-- ... and the same for a carry added onto a masked limb with no `mul`, which
is what each later accumulator (`%30`, `%35`) produces. -/
theorem add_toNat {c m : BitVec 64} (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (c + m).toNat = c.toNat + m.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem add_toNat_le {c m : BitVec 64} (hc : c.toNat ≤ 3) (hm : m.toNat < 2 ^ 51) :
    (c + m).toNat ≤ 2 ^ 51 + 2 := by
  rw [add_toNat hc hm]; omega

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
    obtain ⟨input, hinput⟩ : ∃ l : Fin 5 → ℕ, ∀ i, readLimb? p₀ i s.mem = some (l i) :=
      ⟨fun i => (blk.bytes.extractLsb' (p₀.offsetInBits + 64 * i.toNat) 64).toNat,
        fun i => by simp [readLimb?, MemoryState.live?, hblk]⟩
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

    denote_step v 6
    denote_eval v 6 6
    subst hv6

    peel_load (.bitvec (.concrete 64)), blk, p₀, hblk, s

    denote_step_all v 8
    denote_eval v 8 8
    -- The source limbs, as `BitVec`s: `hinput` is stated through `readLimb?`,
    -- which simp drives all the way down to `Nat` shifts, so it never meets the
    -- `BitVec.extractLsb'` the stepper leaves in `hv<i>`. The offset is taken as
    -- a parameter rather than written `p₁.offsetInBits + 64 * i.toNat`, because
    -- that is not syntactically what each load leaves behind -- limb 0 has no
    -- `getelementptr` at all -- and simp will not match it up to arithmetic.
    have hbits : ∀ (i : Fin 5) (off : ℕ), off = p₀.offsetInBits + 64 * i.toNat →
        blk.bytes.extractLsb' off 64 = BitVec.ofNat 64 (input i) := by
      rintro i off rfl
      have h := hinput i
      simp only [readLimb?, MemoryState.live?, hblk, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.some.injEq] at h
      rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

    -- `peel_gep_limb`'s pointers do not wrap (`hp₀'`), so limb `i` sits exactly
    -- `64 * i` bits into the block -- the offset `hbits` asks for.
    have hoff : ∀ (i : Fin 5) (o : BitVec 64), o.toNat = 8 * i.toNat →
        (p₀.withOffset o).offsetInBits = p₀.offsetInBits + 64 * i.toNat := by
      intro i o ho
      have h2 : i.toNat < 5 := i.isLt
      have hadd : (p₀.offset + o).toNat = p₀.offset.toNat + o.toNat := by
        rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      simp only [Pointer.withOffset, Pointer.offsetInBits, hadd, ho]
      omega

    -- `%7` has no gep, so its value is limb 0 at the bare offset. Rewrite it in
    -- the *goal*, not just in `hv8`: `%7` is used again at `%24`, and anything
    -- left in the valuation spine comes back as block bytes.
    have hin₀ : blk.bytes.extractLsb' p₀.offsetInBits 64 = BitVec.ofNat 64 (input 0) :=
      hbits 0 p₀.offsetInBits (by simp)
    rw [hin₀]

    simp [LLVM.const?, LLVM.lshr, LLVM.lshr?, hin₀] at hv8
    set x2₀ : BitVec 64 := BitVec.ofNat 64 (input 0) >>> (51 : ℕ) with hx2₀
    subst hv8

    -- %9-%10: limb 1's address and value
    peel_input 1, p₀, hp₀.left, s

    denote_step_all v 12
    denote_eval v 11 12
    simp [LLVM.add, LLVM.add?, LLVM.const?, LLVM.lshr, LLVM.lshr?] at hv11 hv12
    set x2 := x2₀ + BitVec.ofNat 64 (input 1) with hx2
    simp [hv11] at hv12
    set x3₀ : BitVec 64 := x2 >>> (51 : ℕ) with hx3₀
    subst hv11 hv12

    peel_input 2, p₀, hp₀.left, s
    denote_step_all v 16
    denote_eval v 15 16
    simp [LLVM.add, LLVM.add?, LLVM.const?, LLVM.lshr, LLVM.lshr?] at hv15 hv16
    set x3 := x3₀ + BitVec.ofNat 64 (input 2) with hx3
    simp [hv15] at hv16
    set x4₀ : BitVec 64 := x3 >>> (51 : ℕ) with hx4₀
    subst hv15 hv16

    peel_input 3, p₀, hp₀.left, s
    denote_step_all v 20
    denote_eval v 19 29
    simp [LLVM.add, LLVM.add?, LLVM.const?, LLVM.lshr, LLVM.lshr?] at hv19 hv20
    set x4 := x4₀ + BitVec.ofNat 64 (input 3) with hx4
    simp [hv19] at hv20
    set x5₀ : BitVec 64 := x4 >>> (51 : ℕ) with hx5₀
    subst hv19 hv20

    peel_input 4, p₀, hp₀.left, s
    denote_step_all v 23
    denote_eval v 23 23
    simp [LLVM.add, LLVM.add?, LLVM.add, LLVM.add?] at hv23
    set x5 := x5₀ + BitVec.ofNat 64 (input 4) with hx5
    subst hv23

    -- The chain, over `toNat`: `x<k>` is `carry_repr`'s `x<k>`, and every step
    -- stays inside the invariant, so nothing wrapped. These are the facts the
    -- region's `nsw`/`nuw` flags need.
    have hb : ∀ i : Fin 5, input i ≤ 0x18000000000000 := fun i => hlimb i _ (hinput i)
    have b1 : (BitVec.ofNat 64 (input 0)).toNat ≤ 0x18000000000003 := by
      rw [BitVec.toNat_ofNat]; have := hb 0; omega
    have n2 : x2.toNat = (BitVec.ofNat 64 (input 0)).toNat / 2 ^ 51 + input 1 := by
      rw [hx2, hx2₀]; exact carry_step_toNat b1 (hb 1)
    have b2 : x2.toNat ≤ 0x18000000000003 := by
      rw [hx2, hx2₀]; exact carry_step_le b1 (hb 1)
    have n3 : x3.toNat = x2.toNat / 2 ^ 51 + input 2 := by
      rw [hx3, hx3₀]; exact carry_step_toNat b2 (hb 2)
    have b3 : x3.toNat ≤ 0x18000000000003 := by
      rw [hx3, hx3₀]; exact carry_step_le b2 (hb 2)
    have n4 : x4.toNat = x3.toNat / 2 ^ 51 + input 3 := by
      rw [hx4, hx4₀]; exact carry_step_toNat b3 (hb 3)
    have b4 : x4.toNat ≤ 0x18000000000003 := by
      rw [hx4, hx4₀]; exact carry_step_le b3 (hb 3)
    have n5 : x5.toNat = x4.toNat / 2 ^ 51 + input 4 := by
      rw [hx5, hx5₀]; exact carry_step_toNat b4 (hb 4)
    have b5 : x5.toNat ≤ 0x18000000000003 := by
      rw [hx5, hx5₀]; exact carry_step_le b4 (hb 4)
    -- the top carry, which is what `%26`'s `mul 19` consumes
    -- stated over `x5.toNat >>> 51`, which is omega's normal form for the
    -- shift; a `BitVec`-level statement lands on a different atom.
    have hc5 : x5.toNat >>> 51 ≤ 3 := by rw [Nat.shiftRight_eq_div_pow]; omega
    denote_step v 27
    denote_eval v 27 27
    simp [LLVM.add, LLVM.add?, LLVM.const?, LLVM.and, LLVM.and?, LLVM.add, LLVM.add?, LLVM.lshr, LLVM.lshr?, LLVM.mul, LLVM.mul?] at hv27

    -- %26/%27 carry `nsw, nuw`; `rw` unifies `c`/`m` out of `hv27` and leaves
    -- the two bounds, which are the carry chain and the mask.
    rw [mul19_add_no_overflow] at hv27
    rotate_left
    · rw [shift_toNat]; omega
    · exact mask_toNat_lt _
    rotate_left
    set x6 := x5 >>> (51 : Nat) * 19#64 + ((BitVec.ofNat 64 (input 0)) &&& 0x7ffffffffffff#64) with hx6
    subst hv27

    denote_step v 30
    denote_eval v 30 30
    simp [LLVM.add, LLVM.add?, LLVM.const?, LLVM.and, LLVM.and?, LLVM.add, LLVM.add?, LLVM.lshr, LLVM.lshr?] at hv30

    -- %30's `nsw, nuw`: `%28` is `x6`'s carry, at most 1 because `%27` only
    -- added `3 * 19` on top of a masked limb; `%29` is a masked limb.
    have b6 : x6.toNat ≤ 2 ^ 51 + 56 := by
      rw [hx6]; exact mul19_add_toNat_le (by rw [shift_toNat]; omega) (mask_toNat_lt _)
    rw [add_no_overflow] at hv30
    rotate_left
    · rw [shift_toNat]; omega
    · exact mask_toNat_lt _
    rotate_left
    set x7 := x6 >>> (51 : Nat) + (x2 &&& 0x7ffffffffffff#64) with hx7
    subst hv30

    denote_step_all v 32
    denote_eval v 31 32
    simp [LLVM.const?, LLVM.and, LLVM.and?] at hv31 hv32
    set x8 := (x6 &&& 0x7ffffffffffff#64) with hx8
    set x9 := (x7 &&& 0x7ffffffffffff#64) with hx9
    subst hv31 hv32

    denote_step v 35
    denote_eval v 35 35
    simp [LLVM.add, LLVM.add?, LLVM.const?, LLVM.and, LLVM.and?, LLVM.add, LLVM.add?, LLVM.lshr, LLVM.lshr?] at hv35

    -- %35's `nsw, nuw`: `%33` is `x7`'s carry. `x7` is `x6`'s carry (at most 1)
    -- on top of a masked limb, so it barely exceeds `2^51` and carries at most 1.
    have b7 : x7.toNat ≤ 2 ^ 51 + 2 := by
      rw [hx7]; exact add_toNat_le (by rw [shift_toNat]; omega) (mask_toNat_lt _)
    rw [add_no_overflow] at hv35
    rotate_left
    · rw [shift_toNat]; omega
    · exact mask_toNat_lt _
    rotate_left
    set x10 := x7 >>> (51 : Nat) + (x3 &&& 0x7ffffffffffff#64) with hx10
    subst hv35

    denote_step_all v 37
    denote_eval v 36 37
    simp [LLVM.const?, LLVM.and, LLVM.and?] at hv36 hv37
    set x11 := x4 &&& 0x7ffffffffffff#64 with hx11
    set x12 := x5 &&& 0x7ffffffffffff#64 with hx12
    subst hv36 hv37

    -- The five registers the stores consume are `carry_repr`'s limbs. `n2 … n5`
    -- already put `x2 … x5` on the `ℕ` chain; these carry that through the
    -- final `lshr`/`and` layer. `carry_repr`'s two `% 2 ^ 8` carry truncations
    -- are identities here, because `b6`/`b7` keep both carries at most 1.
    have ha0 : (BitVec.ofNat 64 (input 0)).toNat = input 0 := by
      rw [BitVec.toNat_ofNat]; have := hb 0; omega
    have c1 : x2.toNat = input 0 / 2 ^ 51 + input 1 := by rw [n2, ha0]
    have n6 : x6.toNat = input 0 % 2 ^ 51 + x5.toNat / 2 ^ 51 * 19 := by
      rw [hx6, mul19_add_toNat (by rw [shift_toNat]; omega) (mask_toNat_lt _),
        shift_toNat, mask_toNat, ha0]
      omega
    have n7 : x7.toNat = x6.toNat / 2 ^ 51 + x2.toNat % 2 ^ 51 := by
      rw [hx7, add_toNat (by rw [shift_toNat]; omega) (mask_toNat_lt _), shift_toNat, mask_toNat]
    have n10 : x10.toNat = x7.toNat / 2 ^ 51 + x3.toNat % 2 ^ 51 := by
      rw [hx10, add_toNat (by rw [shift_toNat]; omega) (mask_toNat_lt _), shift_toNat, mask_toNat]

    have hchain : carry_repr input
        = ![x8.toNat, x9.toNat, x10.toNat, x11.toNat, x12.toNat] := by
      have m8 : x8.toNat = x6.toNat % 2 ^ 51 := by rw [hx8, mask_toNat]
      have m9 : x9.toNat = x7.toNat % 2 ^ 51 := by rw [hx9, mask_toNat]
      have m11 : x11.toNat = x4.toNat % 2 ^ 51 := by rw [hx11, mask_toNat]
      have m12 : x12.toNat = x5.toNat % 2 ^ 51 := by rw [hx12, mask_toNat]
      have t6 : x6.toNat / 2 ^ 51 % 2 ^ 8 = x6.toNat / 2 ^ 51 := Nat.mod_eq_of_lt (by omega)
      have t7 : x7.toNat / 2 ^ 51 % 2 ^ 8 = x7.toNat / 2 ^ 51 := Nat.mod_eq_of_lt (by omega)
      simp only [carry_repr]
      rw [← c1, ← n3, ← n4, ← n5, ← n6, t6, ← n7, t7, ← n10, ← m8, ← m9, ← m11, ← m12]

    -- `x<k> = outputBV i` -- so the stores below write the spec's limbs, and
    -- `output_state` is exactly the state the run ends in
    have hout : ∀ (v : BitVec 64) (i : Fin 5), v.toNat = output i → v = outputBV i := by
      intro v i h
      show v = BitVec.ofNat 64 (output i)
      rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have e8 : x8 = outputBV 0 := hout _ 0 (by simp [output, hchain])
    have e9 : x9 = outputBV 1 := hout _ 1 (by simp [output, hchain])
    have e10 : x10 = outputBV 2 := hout _ 2 (by simp [output, hchain])
    have e11 : x11 = outputBV 3 := hout _ 3 (by simp [output, hchain])
    have e12 : x12 = outputBV 4 := hout _ 4 (by simp [output, hchain])
    rw [e8, e9, e10, e11, e12]

    -- The five stores, limb 0 first. A `store` binds nothing, so `peel_store`
    -- only moves the state; naming each state keeps the next `Fits` obligation
    -- -- and the `getelementptr` that follows it -- readable. `fits_splice`
    -- carries `q`'s room across a store, since a store changes no block's size.
    peel_store (outputBV 0), q, hq.left, s
    set s₁ : GlobalState := { s with mem := s.mem.splice q (outputBV 0) } with hs₁
    have f₁ : Fits s₁.mem q (5 * 64) := fits_splice hq.left

    peel_gep_limb 1, q, f₁, s₁, q
    peel_store (outputBV 1), q₁, hq₁, s₁
    set s₂ : GlobalState := { s₁ with mem := s₁.mem.splice q₁ (outputBV 1) } with hs₂
    have f₂ : Fits s₂.mem q (5 * 64) := fits_splice f₁

    peel_gep_limb 2, q, f₂, s₂, q
    peel_store (outputBV 2), q₂, hq₂, s₂
    set s₃ : GlobalState := { s₂ with mem := s₂.mem.splice q₂ (outputBV 2) } with hs₃
    have f₃ : Fits s₃.mem q (5 * 64) := fits_splice f₂

    peel_gep_limb 3, q, f₃, s₃, q
    peel_store (outputBV 3), q₃, hq₃, s₃
    set s₄ : GlobalState := { s₃ with mem := s₃.mem.splice q₃ (outputBV 3) } with hs₄
    have f₄ : Fits s₄.mem q (5 * 64) := fits_splice f₃

    peel_gep_limb 4, q, f₄, s₄, q
    peel_store (outputBV 4), q₄, hq₄, s₄

    -- `llvm.return`: nothing is left but the state, which is `output_state`
    simp only [BlockCom.denote_term, Terminator.denote_ret, output_state, simp_sllvm,
      hs₁, hs₂, hs₃, hs₄, q₁, q₂, q₃, q₄]
    rfl

    simp [output_state, GlobalState.equiv_def]
    intro p
    obtain ⟨qblk, hqblk, hqlen⟩ := id hq.left

    by_cases h: q.id = p
    case neg =>
      -- an unrelated block: every splice here is at `q.id`, so none is visible.
      -- `getElem?_splice_ne` is stated over `m[_]?`, so it has to fire before
      -- `getElem?_eq` rewrites that into the underlying map lookup.
      simp only [MemoryState.live?]
      have h₄ : (q.withOffset 32#64).id ≠ p := by simp [Pointer.withOffset, h]
      have h₃ : (q.withOffset 24#64).id ≠ p := by simp [Pointer.withOffset, h]
      have h₂ : (q.withOffset 16#64).id ≠ p := by simp [Pointer.withOffset, h]
      have h₁ : (q.withOffset 8#64).id ≠ p := by simp [Pointer.withOffset, h]
      simp only [getElem?_splice_ne h₄, getElem?_splice_ne h₃, getElem?_splice_ne h₂, getElem?_splice_ne h₁, getElem?_splice_ne h]
    case pos =>
      simp only [MemoryState.live?]
      rw [← h]
      simp only [getElem?_splice_self (w := 320) (x := outputBV 4 ++ outputBV 3 ++ outputBV 2 ++ outputBV 1 ++ outputBV 0) hqblk]

      -- the four `getelementptr` destinations, in bits off `q`; `hq'` is what
      -- rules out the pointer wrapping
      have hoffq : ∀ (k : ℕ) (o : BitVec 64), k ≤ 4 → o.toNat = 8 * k →
          (q.withOffset o).offsetInBits = q.offsetInBits + 64 * k := by
        rintro k o hk ho
        have hadd : (q.offset + o).toNat = q.offset.toNat + o.toNat := by
          rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
        simp only [Pointer.withOffset, Pointer.offsetInBits, hadd, ho]
        omega
      have o₁ : (q.withOffset 8#64).offsetInBits = q.offsetInBits + 64 := by
        rw [hoffq 1 8#64 (by omega) (by simp)]
      have o₂ : (q.withOffset 16#64).offsetInBits = q.offsetInBits + 128 := by
        rw [hoffq 2 16#64 (by omega) (by simp)]
      have o₃ : (q.withOffset 24#64).offsetInBits = q.offsetInBits + 192 := by
        rw [hoffq 3 24#64 (by omega) (by simp)]
      have o₄ : (q.withOffset 32#64).offsetInBits = q.offsetInBits + 256 := by
        rw [hoffq 4 32#64 (by omega) (by simp)]

      -- peel the five stores off the right-hand state, innermost first: each
      -- sees the block the previous one left. `getElem?_splice_self` states its
      -- index as `p.id`, which for a `getelementptr` destination is `q.id` only
      -- after unfolding, so each step is refolded before it is used again.
      have hid : ∀ o : BitVec 64, (q.withOffset o).id = q.id := fun _ => rfl
      have k₀ := getElem?_splice_self (x := outputBV 0) hqblk
      have k₁ := getElem?_splice_self (p := q.withOffset 8#64) (x := outputBV 1) k₀
      rw [hid] at k₁
      have k₂ := getElem?_splice_self (p := q.withOffset 16#64) (x := outputBV 2) k₁
      rw [hid] at k₂
      have k₃ := getElem?_splice_self (p := q.withOffset 24#64) (x := outputBV 3) k₂
      rw [hid] at k₃
      have k₄ := getElem?_splice_self (p := q.withOffset 32#64) (x := outputBV 4) k₃
      rw [hid] at k₄
      rw [k₄, o₁, o₂, o₃, o₄]
      simp only [Option.some.injEq, LiveBlock.mk.injEq, true_and]
      clear o₁ o₂ o₃ o₄ k₀ k₁ k₂ k₃ k₄

      simp only [spliceBits_append]
      have assoc : (outputBV 4 ++ outputBV 3 ++ outputBV 2 ++ outputBV 1 ++ outputBV 0) = (outputBV 4 ++ (outputBV 3 ++ (outputBV 2 ++ (outputBV 1 ++ outputBV 0)))) := by
        simp only [BitVec.append_assoc, BitVec.cast_eq]

      rw [assoc]

end Firedancer.Ref
