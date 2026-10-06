import SSA.Projects.Agave.Ed25519.Proof.NAF.OperationWindow

/-!
# RIR carry, parity, truncation and digit emission

These are the instructions after the captured five-word window. Every emitted
overflow flag is retained. The width-eight branch deliberately stores the
low byte directly: subtraction of 256 is the same wrapping byte, while the
carry is extracted from the comparison. The `samesign` promise present in the
LLVM comparison (and not printed by the MLIR importer) is separately discharged.
-/
namespace Agave.Ed25519.NAF

open LeanMLIR.RIR

structure EmittedStep where
  digit : BitVec 8
  advance : BitVec 64
  carry : BitVec 64
  deriving DecidableEq

/-- Exact post-window RIR operation sequence, parameterized by the two source
widths. The even branch performs no output store; its digit field records zero. -/
def emittedStep (width : Nat) (raw carry : PoisonOr (BitVec 64)) : PoisonOr EmittedStep := do
  let window ← Operation.add { nsw := true, nuw := true } raw carry
  let low ← Operation.and (.value window) (.value 1)
  let even ← Operation.icmp .eq (.value low) (.value 0)
  if even = 1#1 then
    return ⟨0, 1, ← carry⟩
  else
    let high ← Operation.icmp .ugt (.value window) (.value (BitVec.ofNat 64 (2 ^ (width - 1) - 1)))
    let digit ← if width = 5 then do
      let truncated : BitVec 8 ← Operation.trunc { nsw := true, nuw := true } (.value window)
      let bias ← Operation.select (τ := .bv 8) (.value high) (.value (-32)) (.value 0)
      Operation.add { nsw := true } (.value bias) (.value truncated)
    else Operation.trunc {} (.value window)
    let nextCarry ← Operation.zext false (.value high)
    return ⟨digit, BitVec.ofNat 64 width, nextCarry⟩

/-- The finite post-window domain suffices to check every emitted arithmetic
promise and the byte result. There are 64 and 512 raw-window/carry pairs. -/
theorem emittedStep_small (width : Nat) (hw : Supported width) :
    ∀ raw : Fin (2 ^ width), ∀ carry : Fin 2,
      emittedStep width (.value (BitVec.ofNat 64 raw.val)) (.value (BitVec.ofNat 64 carry.val)) =
        .value ⟨BitVec.ofInt 8 (step width ⟨raw.val, carry.val⟩).digit,
          BitVec.ofNat 64 (step width ⟨raw.val, carry.val⟩).advance,
          BitVec.ofNat 64 (step width ⟨raw.val, carry.val⟩).next.carry⟩ := by
  rcases hw with rfl | rfl <;> decide +kernel

theorem step_mod_window (width tail carry : Nat) :
    (step width ⟨tail % 2 ^ width, carry⟩).digit = (step width ⟨tail, carry⟩).digit ∧
    (step width ⟨tail % 2 ^ width, carry⟩).advance = (step width ⟨tail, carry⟩).advance ∧
    (step width ⟨tail % 2 ^ width, carry⟩).next.carry = (step width ⟨tail, carry⟩).next.carry := by
  simp only [step, Nat.mod_mod]
  split_ifs <;> simp

/-- No intermediate arithmetic bound is assumed: modulo and the one-bit carry
invariant derive exactly the finite domain certified above. -/
theorem emittedStep_correct (width : Nat) (hw : Supported width) (s : State)
    (hc : s.carry ≤ 1) :
    emittedStep width (.value (BitVec.ofNat 64 (s.tail % 2 ^ width)))
      (.value (BitVec.ofNat 64 s.carry)) =
        .value ⟨BitVec.ofInt 8 (step width s).digit,
          BitVec.ofNat 64 (step width s).advance,
          BitVec.ofNat 64 (step width s).next.carry⟩ := by
  have h := emittedStep_small width hw
    ⟨s.tail % 2 ^ width, Nat.mod_lt _ (by positivity)⟩ ⟨s.carry, by omega⟩
  obtain ⟨hd, ha, hc'⟩ := step_mod_window width s.tail s.carry
  simpa only [hd, ha, hc'] using h

/-- LLVM's source `icmp samesign ugt` is valid at every reachable window;
the imported comparison therefore has the same defined semantics. -/
theorem window_compare_samesign (width : Nat) (hw : Supported width) :
    ∀ raw : Fin (2 ^ width), ∀ carry : Fin 2,
      (BitVec.ofNat 64 (raw.val + carry.val)).msb =
        (BitVec.ofNat 64 (2 ^ (width - 1) - 1)).msb := by
  rcases hw with rfl | rfl <;> decide +kernel

/-- All arithmetic from the two captured word loads through digit emission. -/
def capturedStep (width : Nat) (scalar : BitVec 256) (pos : Fin 256) (carry : Nat) :
    PoisonOr EmittedStep := do
  let raw ← WordWindow.capturedWindow (WordWindow.scalarBuffer scalar) pos width
  emittedStep width (.value raw) (.value (BitVec.ofNat 64 carry))

theorem capturedStep_correct (width : Nat) (hw : Supported width)
    (scalar : BitVec 256) (pos : Fin 256) (carry : Nat) (hc : carry ≤ 1) :
    capturedStep width scalar pos carry =
      .value ⟨BitVec.ofInt 8 (step width ⟨scalar.toNat / 2 ^ pos.val, carry⟩).digit,
        BitVec.ofNat 64 (step width ⟨scalar.toNat / 2 ^ pos.val, carry⟩).advance,
        BitVec.ofNat 64 (step width ⟨scalar.toNat / 2 ^ pos.val, carry⟩).next.carry⟩ := by
  have hv := WordWindow.capturedWindow_toNat scalar pos width hw
  have hraw : WordWindow.capturedWindow (WordWindow.scalarBuffer scalar) pos width =
      .value (BitVec.ofNat 64 ((scalar.toNat / 2 ^ pos.val) % 2 ^ width)) := by
    cases he : WordWindow.capturedWindow (WordWindow.scalarBuffer scalar) pos width with
    | poison =>
        simp only [he, PoisonOr.map_poison] at hv
        exact False.elim ((PoisonOr.poison_ne_value _) hv)
    | value raw =>
        simp only [he, PoisonOr.map_value, PoisonOr.value_inj] at hv
        rw [← hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [capturedStep, hraw, PoisonOr.value_bind]
  exact emittedStep_correct width hw ⟨scalar.toNat / 2 ^ pos.val, carry⟩ hc

end Agave.Ed25519.NAF
