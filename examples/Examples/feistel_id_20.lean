module

public import MLIR.Run.Tactic
public import Examples.Mlir.feistel_id_20
public import Examples.feistel_id
public import Mathlib.Logic.Function.Iterate
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

namespace Examples.Mlir

open MLIR

/-! ## Specification -/

@[expose] public section

/-- One `encdec(lr, key)`: `right` and `left` (through the shift `sh`), `enc`, then `dec`. -/
def feistel_id_20.encdecRun (lr : Reg Γ (.bv 128)) (c64 : Dst Γ (.bv 128)) (key : Reg Γ (.bv 64))
    (right : Dst Γ (.bv 64)) (sh : Dst Γ (.bv 128)) (left : Dst Γ (.bv 64))
    (enc dec : Dst Γ (.bv 128)) : List (Instr Γ) :=
  [.unop (.trunc {}) right lr, .binop (.lshr false) sh lr (.val c64.i c64.h),
    .unop (.trunc { nuw := true }) left (.val sh.i sh.h),
    .call encrypt_round.call
      (.cons (.val left.i left.h) (.cons (.val right.i right.h) (.cons key .nil))) (.cons enc .nil),
    .call decrypt_round.call (.cons (.val enc.i enc.h) (.cons key .nil)) (.cons dec .nil)]

end

/-! ## Proof -/

/-- The `trunc nuw` of the high half: it fits in 64 bits. -/
theorem feistel_id_20.trunc_nuw (lr : BitVec 128) :
    ((lr >>> 64).setWidth 64).setWidth 128 = lr >>> 64 := by
  bv_decide

/-! ## Patterns

If you have a lot of repetition of very similar instructions, it makes sense to abstract their
behavior into a separate theorem. Such a theorem has a premise `blk.body.drop pos = <pattern> ++ rest`,
and a continuation premise `blk.runBodyFrom E[<writes in pattern>] (pos + <pattern>.length) S >>= g = K`
and states `(blk.runBodyFrom E pos S >>= g) = K`.

The pattern can then be applied with `step_pattern`.
-/

/-- One `encdec` round: `dec` holds `feistel_id.spec LR KEY`. -/
theorem feistel_id_20.runBodyFrom_encdecRun {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {lr : Reg Γ (.bv 128)} {c64 : Dst Γ (.bv 128)} {key : Reg Γ (.bv 64)}
    {right : Dst Γ (.bv 64)} {sh : Dst Γ (.bv 128)} {left : Dst Γ (.bv 64)}
    {enc dec : Dst Γ (.bv 128)} {rest : List (Instr Γ)} {LR : BitVec 128} {KEY : BitVec 64}
    {S : GlobalState} {g : ⟪Γ⟫ × GlobalState → PoisonOr β} {K : PoisonOr β} (hwf : S.WF)
    (hbody : blk.body.drop pos = feistel_id_20.encdecRun lr c64 key right sh left enc dec ++ rest)
    (hc : E ⊨ [c64 := 64#128, lr := LR, key := KEY])
    (hd : [right.i, sh.i, left.i, enc.i].Nodup)
    (hkr : key ≠ .val right.i right.h) (hkl : key ≠ .val left.i left.h)
    (hK : ∀ vr vs vl ve, (blk.runBodyFrom
        E[right := vr, sh := vs, left := vl, enc := ve, dec := .value LR]
        (pos + 5) S >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  -- `uint64_t encdec_right = (lr);`
  step_pure
  -- `uint64_t encdec_left = (lr) >> 64;`
  step_pure
  step_pure [feistel_id_20.trunc_nuw]
  -- `__uint128_t encdec_enc = encrypt_round(encdec_left, encdec_right, (key));`
  step_call using encrypt_round.call_eq
  -- `decrypt_round(encdec_enc, (key));`
  step_call using decrypt_round.call_eq
  subst hS
  have := feistel_id.spec_eq LR KEY
  rw [feistel_id.spec] at this
  rw [this] at hE
  rw [hE]
  exact hK _ _ _ _

/-- `feistel_id_20` returns `spec lr key`. -/
public theorem feistel_id_20.call_eq (lr : BitVec 128) (key : BitVec 64) (s : GlobalState)
    (hwf : s.WF) :
    feistel_id_20.call (feistel_id_20.args (.value lr) (.value key)) s =
      .value (.cons (.value (lr)) .nil, s) := by
  func_init
  block_init
  step_pure
  -- `for (int i = 0; i < 20; i++) lr = encdec(lr, key);`, unrolled
  repeat
    step_pattern using feistel_id_20.runBodyFrom_encdecRun
  finish_block
  simp [hS]

end Examples.Mlir
