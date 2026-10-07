import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Startup
import Mathlib.Tactic

/-! First arithmetic phase of the actual Montgomery body: live input loads,
zero extension, and the initial unsigned-no-overflow 128-bit product. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR

/-- Multiplying two widened u64 words is exact in u128, for arbitrary words.
Later accumulation bounds require the separate radix-52 limb invariant. -/
theorem widened_product_bound (a b : BitVec 64) :
    a.toNat * b.toNat < 2 ^ 128 := by
  have h := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt a.isLt) b.isLt
    (by decide : 0 < 2 ^ 64)
  norm_num at h ⊢
  exact h

theorem widened_mul_nuw (a b : BitVec 64) :
    Operation.mul { nuw := true } (.value (a.setWidth 128))
      (.value (b.setWidth 128)) =
      .value (a.setWidth 128 * b.setWidth 128) := by
  have h : (a.setWidth 128).umulOverflow (b.setWidth 128) = false := by
    simp only [BitVec.umulOverflow, BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
    simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]
    exact widened_product_bound a b
  simp [Operation.mul, h]

theorem widened_mul_toNat (a b : BitVec 64) :
    (a.setWidth 128 * b.setWidth 128).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128),
    BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
  exact Nat.mod_eq_of_lt (widened_product_bound a b)

/-- Register result of the two actual loads and the first wide product. -/
def inputProductEnv (E : Env program.Γ) (a b : BitVec 64) : Env program.Γ :=
  E[%33 := .value a, %34 := .value b,
    %35 := .value (a.setWidth 128), %36 := .value (b.setWidth 128),
    %37 := .value (b.setWidth 128 * a.setWidth 128)]

/-- Execute instructions 33--49 of the verbatim body, including the retained
lifetime/scope declarations. No limb-size assumption is necessary yet. -/
theorem input_product_run (p : Primitives) (E : Env program.Γ)
    (state : GlobalState) (left right : Pointer)
    (hleft : E.read (%arg1) = .value left)
    (hright : E.read (%arg2) = .value right)
    (hfitLeft : Fits state.mem left 64) (hfitRight : Fits state.mem right 64) :
    List.foldlM Instr.run E (((program.entry p).body.drop 33).take 17) state =
      .value (inputProductEnv E (state.mem.readAt left 64)
        (state.mem.readAt right 64), state) := by
  change E.args 1 = .value left at hleft
  change E.args 2 = .value right at hright
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    Operation.load, Operation.zext, UnOp.compute, BinOp.compute,
    inputProductEnv, widened_mul_nuw, hleft, hright, hfitLeft, hfitRight,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
