module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Logic.Function.Iterate
public import MLIR.Run.Tactic
public import Examples.Mlir.fib

namespace Examples.Mlir

open MLIR

/-! ## Specification -/

@[expose] public section

/-- One pass of the loop: `(a, b) ↦ (b, b + a)`, in the program's operand order. -/
def fib.step (p : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (p.2, p.2 + p.1)

/-- `k` passes of the loop. -/
def fib.iter : Nat → BitVec 64 × BitVec 64 → BitVec 64 × BitVec 64
  | 0, p => p
  | k + 1, p => fib.iter k (fib.step p)

/-- `b` after `n` passes from `(a, b) = (0, 1)`. -/
def fib.spec (n : BitVec 64) : BitVec 64 :=
  (fib.iter n.toNat (0#64, 1#64)).1

theorem fib.iter.eq_mathlib : (a b : Nat) → (n : Nat) → (iter n (BitVec.ofNat 64 a, BitVec.ofNat 64 b)).1 = BitVec.ofNat 64 (((fun p => (p.2, p.1 + p.2))^[n] (a, b)).1)
| _, _, 0 => by simp [iter]
| a, b, n+1 => by
  simp [iter, step, ← BitVec.ofNat_add, eq_mathlib, Nat.add_comm]

theorem fib.spec.eq_mathlib : (n : Nat) → (n < 2^64) → fib.spec (n : BitVec 64) = (Nat.fib n : BitVec 64) := by
  intro n hn
  simp [spec, Nat.fib]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp [iter.eq_mathlib]

end

/-! ## Proof -/

/-! ### Proving loops

If the CFG contains a loop

```
    │
┌───▼───┐
│  head │◄────┐
└───┬───┘     │
    │         │
┌───▼───┐     │
│ inner │     │
└───┬───┘     │
    ├─────────┘
    │
┌───▼───┐
│  exit │
└───────┘
```

we prove the following statenent:

∀ iterationCounter loopVars env,
  <env entries hold (constants, loop counter, loop vars etc). Notated with `env ⊨ [%i := val, ...]`> →
  counter bounds →
  (∀ E', <env conditions on E' for exit> → func.runFrom E' ^exit S = K) →
  func.runFrom env ^head S = K

It states:
Under certain condition for the env,
if after the effect of the loop, the remainder of the program computes `K`,
then the program from the start of the loop also computes `K`.

It makes sense to prove this by induction
-/

/-- The counter's `n - 1`. -/
theorem fib.dec_eq (k : Nat) :
    BitVec.ofNat 64 k + 1#64 + 18446744073709551615#64 = BitVec.ofNat 64 k := by
    bv_decide

/-- The loop from `^bb1` with counter `m + 1` and `(a, b) = p`: after `m + 1` passes, `^bb2`
runs on the final `b`. -/
theorem fib.loop (S : GlobalState) (K : PoisonOr (Vals _ × GlobalState)) :
    ∀ counter (p : BitVec 64 × BitVec 64) (E : ⟪fib.Γ⟫),
      (E ⊨ [%0 := 0#64, %2 := 18446744073709551615#64, %4 := BitVec.ofNat 64 (counter + 1),
        %5 := p.2, %6 := p.1]) →
      counter + 1 < 2 ^ 64 →
      (∀ E' : ⟪fib.Γ⟫, (E' ⊨ [%10 := (fib.iter (counter + 1) p).1]) → fib.runFrom E' ^bb2 S = K) →
      fib.runFrom E ^bb1 S = K := by
  intro n
  induction n with
  | zero =>
    intro p E hEnv hn hcont
    block_init
    iterate 3 step_pure
    finish_block
    run_from using hcont
  | succ n ih =>
    intro p E hEnv hn hcont
    block_init
    iterate 3 step_pure
    finish_block
    · -- impossible `n = 0` case
      rw [BitVec.ofNat_add, dec_eq] at hbr
      have h := congrArg BitVec.toNat hbr
      simp at h
      rw [Nat.mod_eq_of_lt (by omega)] at h
      simp at h
    · rw [BitVec.ofNat_add, dec_eq] at hE
      run_from using ih (fib.step p) -- Step remaining loop steps
      run_from using hcont -- Step remaining function

/-- The counter on entering the loop is `n` itself. -/
theorem fib.ofNat_pred (n : BitVec 64) (h : n ≠ 0#64) : BitVec.ofNat 64 (n.toNat - 1 + 1) = n := by
  have h0 : n.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0), BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `fib` returns `spec n`. -/
public theorem fib.call_eq (n : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    fib.call (fib.args (.value n)) s = .value (.cons (.value (fib.spec n)) .nil, s) := by
  func_init
  block_init
  iterate 4 step_pure
  finish_block
  · -- `n = 0`: no passes, return `b = 1`
    block_init
    finish_block
    simp [hS, hbr, fib.spec, fib.iter]
  · -- `n ≠ 0`: run the loop `n` times
    have : n.toNat - 1 + 1 = n.toNat := Nat.succ_pred_eq_of_ne_zero (by simpa [BitVec.toNat_eq] using hbr)
    run_from using loop _ _ (n.toNat - 1) ⟨0, 1⟩
    block_init
    finish_block
    simp [hS, spec, this]

end Examples.Mlir
