import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.SubtractionFlags

/-! Exact 18-instruction borrow window of the wide wrapper. Every
retained `nsw` addition and the doubly flagged truncation are discharged. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Subtraction

def wrapperBorrowEnv (E : Env program.Γ) (x : Fin 5 → BitVec 52) : Env program.Γ :=
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  E[%313 := .value (d 0),
    %314 := .value (d 0 &&& 4503599627370495#64),
    %315 := .value ((d 0).sshiftRight 63),
    %316 := .value ((d 0).sshiftRight 63 + (-3916664325105025 : BitVec 64)),
    %317 := .value (d 1),
    %318 := .value (d 1 &&& 4503599627370495#64),
    %319 := .value ((d 1).sshiftRight 63),
    %320 := .value ((x 2).setWidth 64 + (-1367801 : BitVec 64)),
    %321 := .value (d 2),
    %322 := .value (d 2 &&& 4503599627370495#64),
    %323 := .value ((d 2).sshiftRight 63),
    %324 := .value (d 3),
    %325 := .value (d 3 &&& 4503599627370495#64),
    %326 := .value ((d 3).sshiftRight 63),
    %327 := .value ((x 4).setWidth 64 + (-17592186044416 : BitVec 64)),
    %328 := .value (d 4),
    %329 := .value (d 4 >>> 63),
    %330 := .value (borrowByte d)]

/-- Execute the actual subtraction window, retaining all source flags. -/
theorem differences_top_certificate (x : Fin 5 → BitVec 52) :
    let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
    Operation.add { nsw := true } (.value ((x 4).setWidth 64))
        (.value (-17592186044416 : BitVec 64)) =
      .value ((x 4).setWidth 64 + (-17592186044416 : BitVec 64)) ∧
    Operation.add { nsw := true }
        (.value ((x 4).setWidth 64 + (-17592186044416 : BitVec 64)))
        (.value ((d 3).sshiftRight 63)) = .value (d 4) ∧
    (-(2 ^ 52 : Int) ≤ (d 4).toInt ∧ (d 4).toInt < 2 ^ 52) := by
  dsimp only
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  have hx : ((x 4).setWidth 64).toNat < 2 ^ 52 := by
    simpa only [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] using (x 4).isLt
  have hf := limb_minus_constant ((x 4).setWidth 64) 17592186044416 hx (by decide)
  have hi : ((x 4).setWidth 64 + (-17592186044416 : BitVec 64)).toInt =
      (((x 4).setWidth 64).toNat : Int) - 17592186044416 := by simpa using hf.2
  have hb := (borrowSteps_certificate x).1 3
  have hm : ((d 3).sshiftRight 63).toInt = -((borrowSteps x 3).2 : Int) := by
    rw [(differences_refine x 3).2]
    exact borrow_mask_toInt _ hb.2
  have hs := signed_add64 ((x 4).setWidth 64 + (-17592186044416 : BitVec 64))
    ((d 3).sshiftRight 63)
    (by rw [hi, hm]; norm_num at hx ⊢; omega)
    (by rw [hi, hm]; norm_num at hx ⊢; omega)
  refine ⟨by simpa using hf.1, hs.1, ?_⟩
  change -(2 ^ 52 : Int) ≤ (((x 4).setWidth 64 + (-17592186044416 : BitVec 64)) +
    (d 3).sshiftRight 63).toInt ∧
    (((x 4).setWidth 64 + (-17592186044416 : BitVec 64)) + (d 3).sshiftRight 63).toInt < 2 ^ 52
  rw [hs.2, hi, hm]
  norm_num at hx ⊢
  omega

theorem wrapper_borrow_run (p : Primitives) (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (x : Fin 5 → BitVec 52)
    (hx0 : E.read (%288) = .value ((x 0).setWidth 64))
    (hx1 : E.read (%294) = .value ((x 1).setWidth 64))
    (hx2 : E.read (%300) = .value ((x 2).setWidth 64))
    (hx3 : E.read (%306) = .value ((x 3).setWidth 64))
    (hx4 : E.read (%312) = .value ((x 4).setWidth 64))
    (hmask : E.read (%38) = .value 4503599627370495#64)
    (hneg0 : E.read (%41) = .value (-671914833335277 : BitVec 64))
    (hshift : E.read (%42) = .value 63#64)
    (hneg1 : E.read (%43) = .value (-3916664325105025 : BitVec 64))
    (hneg2 : E.read (%44) = .value (-1367801 : BitVec 64))
    (hneg4 : E.read (%45) = .value (-17592186044416 : BitVec 64)) :
    List.foldlM Instr.run E (((program.entry p g).body.drop 358).take 18) state =
      .value (wrapperBorrowEnv E x, state) := by
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  have hx (i : Fin 5) : ((x i).setWidth 64).toNat < 2 ^ 52 := by
    simpa only [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] using (x i).isLt
  have hc := (borrowSteps_certificate x).1
  have hs := differences_refine x
  have hf0 := (limb_minus_constant ((x 0).setWidth 64) 671914833335277
    (hx 0) (by decide)).1
  have hf1 := middle_borrow_flags ((x 1).setWidth 64) 3916664325105025
    (borrowSteps x 0).2 (hx 1) (by decide) (hc 0).2
  have hf2 := limb_minus_constant ((x 2).setWidth 64) 1367801
    (hx 2) (by decide)
  have hf3 := limb_plus_borrow ((x 3).setWidth 64) (borrowSteps x 2).2 (hx 3) (hc 2).2
  have ht := high_bit_trunc_flags (d 4)
  have htop := differences_top_certificate x
  have h327 := htop.1
  have h328 := htop.2.1
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
  have h195 := hf2.1
  have h196 : Operation.add { nsw := true }
      (.value ((x 2).setWidth 64 + (-1367801 : BitVec 64)))
      (.value ((d 1).sshiftRight 63)) = .value (d 2) := by
    have hm : ((d 1).sshiftRight 63).toInt = -((borrowSteps x 1).2 : Int) := by
      rw [(hs 1).2]
      exact borrow_mask_toInt _ (hc 1).2
    have hf2int : ((x 2).setWidth 64 + (-1367801 : BitVec 64)).toInt =
        (((x 2).setWidth 64).toNat : Int) - 1367801 := by
      simpa using hf2.2
    have hsafe := signed_add64 ((x 2).setWidth 64 + (-1367801 : BitVec 64))
      ((d 1).sshiftRight 63)
      (by rw [hf2int, hm]; have h := hx 2; have hb := (hc 1).2; norm_num at h ⊢; omega)
      (by rw [hf2int, hm]; have h := hx 2; have hb := (hc 1).2; norm_num at h ⊢; omega)
    simpa [d, differences,
      BitVec.add_assoc, BitVec.add_comm, add_left_comm] using hsafe.1
  have h199 : Operation.add { nsw := true }
      (.value ((d 2).sshiftRight 63)) (.value ((x 3).setWidth 64)) = .value (d 3) := by
    have hm : ((d 2).sshiftRight 63).toInt = -((borrowSteps x 2).2 : Int) := by
      rw [(hs 2).2]
      exact borrow_mask_toInt _ (hc 2).2
    have hxint : ((x 3).setWidth 64).toInt = (((x 3).setWidth 64).toNat : Int) :=
      BitVec.toInt_eq_toNat_of_lt (by have h := hx 3; norm_num at h ⊢; omega)
    have hsafe := signed_add64 ((d 2).sshiftRight 63) ((x 3).setWidth 64)
      (by rw [hm, hxint]; have h := hx 3; have hb := (hc 2).2; norm_num at h ⊢; omega)
      (by rw [hm, hxint]; have h := hx 3; have hb := (hc 2).2; norm_num at h ⊢; omega)
    simpa [d, differences,
      BitVec.add_comm] using hsafe.1
  have hadd (a b : BitVec 64) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [d, differences] at hf0 h191 h192 h195 h196 h199 h327 h328 ht
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    wrapperBorrowEnv, borrowByte, differences, d,
    hx0, hx1, hx2, hx3, hx4, hmask, hneg0, hneg1, hneg2, hneg4, hshift,
    hf0, h191, h192, h195, h196, h199, h327, h328, ht,
    hadd, Operation.and, Operation.ashr, Operation.lshr,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.Verifier.Execution.ScalarWide
