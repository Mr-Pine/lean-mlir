import SSA.Projects.Agave.Ed25519.Proof.Encoding.SplitExecution

namespace Agave.Ed25519.Encoding
open LeanMLIR.RIR

/-- The exact little-endian physical register corresponding to eight u32 lanes. -/
def physicalRegister (v : Field.Packed) (i : Fin 5) : V64 :=
  join64 (Vector.ofFn (v i))

/-! All twenty exact compiler observations implement `Field.split`, including
unrestricted physical lanes. These endpoints connect the RIR programs to the
integer-value preservation theorem `Field.split_value`. -/

theorem split_observe0_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_0.call
      (RIR.agave_avx2_field_split_observe_0.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 0 0)) .nil, s) := by
  rw [RIR.split_observe0_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 0 0]
  rfl

theorem split_observe1_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_1.call
      (RIR.agave_avx2_field_split_observe_1.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 0 1)) .nil, s) := by
  rw [RIR.split_observe1_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 0 1]
  rfl

theorem split_observe2_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_2.call
      (RIR.agave_avx2_field_split_observe_2.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 0 2)) .nil, s) := by
  rw [RIR.split_observe2_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 0 2]
  rfl

theorem split_observe3_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_3.call
      (RIR.agave_avx2_field_split_observe_3.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 0 3)) .nil, s) := by
  rw [RIR.split_observe3_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 0 3]
  rfl

theorem split_observe4_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_4.call
      (RIR.agave_avx2_field_split_observe_4.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 0 4)) .nil, s) := by
  rw [RIR.split_observe4_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 0 4]
  rfl

theorem split_observe5_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_5.call
      (RIR.agave_avx2_field_split_observe_5.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 1 0)) .nil, s) := by
  rw [RIR.split_observe5_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 1 0]
  rfl

theorem split_observe6_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_6.call
      (RIR.agave_avx2_field_split_observe_6.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 1 1)) .nil, s) := by
  rw [RIR.split_observe6_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 1 1]
  rfl

theorem split_observe7_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_7.call
      (RIR.agave_avx2_field_split_observe_7.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 1 2)) .nil, s) := by
  rw [RIR.split_observe7_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 1 2]
  rfl

theorem split_observe8_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_8.call
      (RIR.agave_avx2_field_split_observe_8.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 1 3)) .nil, s) := by
  rw [RIR.split_observe8_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 1 3]
  rfl

theorem split_observe9_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_9.call
      (RIR.agave_avx2_field_split_observe_9.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 1 4)) .nil, s) := by
  rw [RIR.split_observe9_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 1 4]
  rfl

theorem split_observe10_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_10.call
      (RIR.agave_avx2_field_split_observe_10.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 2 0)) .nil, s) := by
  rw [RIR.split_observe10_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 2 0]
  rfl

theorem split_observe11_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_11.call
      (RIR.agave_avx2_field_split_observe_11.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 2 1)) .nil, s) := by
  rw [RIR.split_observe11_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 2 1]
  rfl

theorem split_observe12_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_12.call
      (RIR.agave_avx2_field_split_observe_12.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 2 2)) .nil, s) := by
  rw [RIR.split_observe12_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 2 2]
  rfl

theorem split_observe13_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_13.call
      (RIR.agave_avx2_field_split_observe_13.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 2 3)) .nil, s) := by
  rw [RIR.split_observe13_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 2 3]
  rfl

theorem split_observe14_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_14.call
      (RIR.agave_avx2_field_split_observe_14.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 2 4)) .nil, s) := by
  rw [RIR.split_observe14_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 2 4]
  rfl

theorem split_observe15_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_15.call
      (RIR.agave_avx2_field_split_observe_15.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 3 0)) .nil, s) := by
  rw [RIR.split_observe15_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 3 0]
  rfl

theorem split_observe16_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_16.call
      (RIR.agave_avx2_field_split_observe_16.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 3 1)) .nil, s) := by
  rw [RIR.split_observe16_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 3 1]
  rfl

theorem split_observe17_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_17.call
      (RIR.agave_avx2_field_split_observe_17.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 3 2)) .nil, s) := by
  rw [RIR.split_observe17_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 3 2]
  rfl

theorem split_observe18_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_18.call
      (RIR.agave_avx2_field_split_observe_18.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 3 3)) .nil, s) := by
  rw [RIR.split_observe18_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 3 3]
  rfl

theorem split_observe19_refines (v : Field.Packed) (s : GlobalState) (hwf : s.WF) :
    RIR.agave_avx2_field_split_observe_19.call
      (RIR.agave_avx2_field_split_observe_19.args
        (Ty.wrap (physicalRegister v 0)) (Ty.wrap (physicalRegister v 1))
        (Ty.wrap (physicalRegister v 2)) (Ty.wrap (physicalRegister v 3))
        (Ty.wrap (physicalRegister v 4))) s =
      .value (.cons (.value (Field.split v 3 4)) .nil, s) := by
  rw [RIR.split_observe19_call _ _ _ _ _ s hwf]
  simp only [physicalRegister, split32_join64, Vector.getElem_ofFn]
  rw [← split_word_eq v 3 4]
  rfl

end Agave.Ed25519.Encoding
