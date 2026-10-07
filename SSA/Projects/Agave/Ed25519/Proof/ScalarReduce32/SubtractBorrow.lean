import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.SubtractionFlags
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Program

/-! Exact 18-instruction borrow window of Scalar::reduce. Every
retained `nsw` addition and the doubly flagged truncation are discharged. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Agave.Ed25519.ScalarReduce32.Execution

open LeanMLIR.RIR
open Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction

def subtractBorrowEnv (E : Env program.Γ) (x : Fin 5 → BitVec 52) : Env program.Γ :=
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  E[%309 := .value (d 0),
    %310 := .value (d 0 &&& 4503599627370495#64),
    %311 := .value ((d 0).sshiftRight 63),
    %312 := .value ((d 0).sshiftRight 63 + (-3916664325105025 : BitVec 64)),
    %313 := .value (d 1),
    %314 := .value (d 1 &&& 4503599627370495#64),
    %315 := .value ((d 1).sshiftRight 63),
    %316 := .value ((d 1).sshiftRight 63 + (-1367801 : BitVec 64)),
    %317 := .value (d 2),
    %318 := .value (d 2 &&& 4503599627370495#64),
    %319 := .value ((d 2).sshiftRight 63),
    %320 := .value (d 3),
    %321 := .value (d 3 &&& 4503599627370495#64),
    %322 := .value ((d 3).sshiftRight 63),
    %323 := .value ((x 4).setWidth 64 + (-17592186044416 : BitVec 64)),
    %324 := .value (d 4),
    %325 := .value (d 4 >>> 63),
    %326 := .value (borrowByte d)]

/-- Execute the actual subtraction window, retaining all source flags. -/
theorem subtract_borrow (E : Env program.Γ) (state : GlobalState)
    (x : Fin 5 → BitVec 52)
    (hx0 : E.read (%286) = .value ((x 0).setWidth 64))
    (hx1 : E.read (%294) = .value ((x 1).setWidth 64))
    (hx2 : E.read (%300) = .value ((x 2).setWidth 64))
    (hx3 : E.read (%306) = .value ((x 3).setWidth 64))
    (hx4 : E.read (%308) = .value ((x 4).setWidth 64))
    (hmask : E.read (%23) = .value 4503599627370495#64)
    (hneg0 : E.read (%35) = .value (-671914833335277 : BitVec 64))
    (hshift : E.read (%36) = .value 63#64)
    (hneg1 : E.read (%37) = .value (-3916664325105025 : BitVec 64))
    (hneg2 : E.read (%38) = .value (-1367801 : BitVec 64))
    (hneg4 : E.read (%39) = .value (-17592186044416 : BitVec 64)) :
    List.foldlM Instr.run E ((program.entry.body.drop 358).take 18) state =
      .value (subtractBorrowEnv E x, state) := by
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  have hx (i : Fin 5) : ((x i).setWidth 64).toNat < 2 ^ 52 := by
    simpa only [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] using (x i).isLt
  have hc := (borrowSteps_certificate x).1
  have hs := differences_refine x
  have hf0 := (limb_minus_constant ((x 0).setWidth 64) 671914833335277
    (hx 0) (by decide)).1
  have hf1 := middle_borrow_flags ((x 1).setWidth 64) 3916664325105025
    (borrowSteps x 0).2 (hx 1) (by decide) (hc 0).2
  have hf2 := middle_borrow_flags ((x 2).setWidth 64) 1367801
    (borrowSteps x 1).2 (hx 2) (by decide) (hc 1).2
  have hf3 := limb_plus_borrow ((x 3).setWidth 64) (borrowSteps x 2).2 (hx 3) (hc 2).2
  have ht := high_bit_trunc_flags (d 4)
  have h191 : Operation.add { nsw := true }
      (.value ((d 0).sshiftRight 63)) (.value (-3916664325105025 : BitVec 64)) =
      .value ((d 0).sshiftRight 63 + (-3916664325105025 : BitVec 64)) := by
    rw [(hs 0).2]
    exact hf1.1
  have h192 : Operation.add { nsw := true }
      (.value ((d 0).sshiftRight 63 + (-3916664325105025 : BitVec 64)))
      (.value ((x 1).setWidth 64)) = .value (d 1) := by
    change Operation.add _ _ _ = .value
      ((d 0).sshiftRight 63 + (-3916664325105025 : BitVec 64) + (x 1).setWidth 64)
    rw [(hs 0).2]
    exact hf1.2
  have h195 : Operation.add { nsw := true }
      (.value ((d 1).sshiftRight 63)) (.value (-1367801 : BitVec 64)) =
      .value ((d 1).sshiftRight 63 + (-1367801 : BitVec 64)) := by
    rw [(hs 1).2]
    exact hf2.1
  have h196 : Operation.add { nsw := true }
      (.value ((d 1).sshiftRight 63 + (-1367801 : BitVec 64)))
      (.value ((x 2).setWidth 64)) = .value (d 2) := by
    change Operation.add _ _ _ = .value
      ((d 1).sshiftRight 63 + (-1367801 : BitVec 64) + (x 2).setWidth 64)
    rw [(hs 1).2]
    exact hf2.2
  have h199 : Operation.add { nsw := true }
      (.value ((x 3).setWidth 64)) (.value ((d 2).sshiftRight 63)) = .value (d 3) := by
    change Operation.add _ _ _ = .value ((x 3).setWidth 64 + (d 2).sshiftRight 63)
    rw [(hs 2).2]
    exact hf3
  have hf4 := limb_minus_constant ((x 4).setWidth 64) 17592186044416
    (hx 4) (by decide)
  have hf4i : ((x 4).setWidth 64 + (-17592186044416 : BitVec 64)).toInt =
      (((x 4).setWidth 64).toNat : Int) - 17592186044416 := hf4.2
  have h324 : Operation.add { nsw := true }
      (.value ((x 4).setWidth 64 + (-17592186044416 : BitVec 64)))
      (.value ((d 3).sshiftRight 63)) = .value (d 4) := by
    change Operation.add _ _ _ = .value
      ((x 4).setWidth 64 + (-17592186044416 : BitVec 64) + (d 3).sshiftRight 63)
    rw [(hs 3).2]
    have hm := borrow_mask_toInt (borrowSteps x 3).2 (hc 3).2
    have hx4 := hx 4
    have hb3 := (hc 3).2
    exact (signed_add64 _ _
      (by rw [hf4i, hm]; norm_num at hx4 ⊢; omega)
      (by rw [hf4i, hm]; norm_num at hx4 ⊢; omega)).1
  simp [d, differences] at hf0 h191 h192 h195 h196 h199 hf4 h324 ht
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    subtractBorrowEnv, borrowByte, differences, d,
    hx0, hx1, hx2, hx3, hx4, hmask, hneg0, hneg1, hneg2, hneg4, hshift,
    hf0, h191, h192, h195, h196, h199, hf4.1, h324, ht,
    Operation.and, Operation.ashr, Operation.lshr,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.ScalarReduce32.Execution
