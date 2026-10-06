import SSA.Projects.Agave.Ed25519.Proof.Encoding.Program
import SSA.Projects.Agave.Ed25519.Proof.Encoding.SplitWord
import SSA.Projects.Agave.Ed25519.Proof.Encoding.WordBounds
import SSA.Projects.Agave.Ed25519.Proof.ReduceBitcast

namespace Agave.Ed25519.Encoding.RIR
open LeanMLIR.RIR
section

private theorem wide32_bound (x : BitVec 32) :
    (x.setWidth 64).toNat ≤ 2^32-1 := by
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  have := x.isLt
  omega

private theorem wide32_shift_u (x : BitVec 32) :
    (x.setWidth 64 <<< 26) >>> 26 = x.setWidth 64 :=
  shift_unsigned_safe _ 26 (2^32-1) (wide32_bound x) (by decide)

private theorem wide32_shift_s (x : BitVec 32) :
    (x.setWidth 64 <<< 26).sshiftRight 26 = x.setWidth 64 :=
  shift_signed_safe _ 26 (2^32-1) (wide32_bound x) (by decide)

private theorem wide32_add_safe (x y : BitVec 32) :
    (y.setWidth 64 <<< 26).saddOverflow (x.setWidth 64) = false ∧
    (y.setWidth 64 <<< 26).uaddOverflow (x.setWidth 64) = false :=
  add_safe_of_bound _ _ ((2^32-1)*2^26) (2^32-1)
    (shiftLeft_bound _ 26 _ (wide32_bound y)) (wide32_bound x) (by decide)

private theorem pack_lane_0 (a : V64) :
    (BitVec.packLanes a).extractLsb' 0 32 = (split32 a)[0] := by
  simpa [split32] using extract_pack_part a 0 0 32 (by decide) (by decide)

private theorem pack_lane_1 (a : V64) :
    (BitVec.packLanes a).extractLsb' 32 32 = (split32 a)[1] := by
  simpa [split32] using extract_pack_part a 0 32 32 (by decide) (by decide)

private theorem pack_lane_2 (a : V64) :
    (BitVec.packLanes a).extractLsb' 64 32 = (split32 a)[2] := by
  simpa [split32] using extract_pack_part a 1 0 32 (by decide) (by decide)

private theorem pack_lane_3 (a : V64) :
    (BitVec.packLanes a).extractLsb' 96 32 = (split32 a)[3] := by
  simpa [split32] using extract_pack_part a 1 32 32 (by decide) (by decide)

private theorem pack_lane_4 (a : V64) :
    (BitVec.packLanes a).extractLsb' 128 32 = (split32 a)[4] := by
  simpa [split32] using extract_pack_part a 2 0 32 (by decide) (by decide)

private theorem pack_lane_5 (a : V64) :
    (BitVec.packLanes a).extractLsb' 160 32 = (split32 a)[5] := by
  simpa [split32] using extract_pack_part a 2 32 32 (by decide) (by decide)

private theorem pack_lane_6 (a : V64) :
    (BitVec.packLanes a).extractLsb' 192 32 = (split32 a)[6] := by
  simpa [split32] using extract_pack_part a 3 0 32 (by decide) (by decide)

private theorem pack_lane_7 (a : V64) :
    (BitVec.packLanes a).extractLsb' 224 32 = (split32 a)[7] := by
  simpa [split32] using extract_pack_part a 3 32 32 (by decide) (by decide)

/-! Each theorem executes an exact compiler-produced observation of `split`.
The sole execution premise is well-formed RIR state. Arbitrary physical lane
values are allowed; both LLVM overflow flags are discharged, not assumed. -/

theorem split_observe0_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_0.call
      (agave_avx2_field_split_observe_0.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 a)[2].setWidth 64 <<< 26) +
        (split32 a)[0].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_0, pack_lane_2]

theorem split_observe1_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_1.call
      (agave_avx2_field_split_observe_1.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 b)[2].setWidth 64 <<< 26) +
        (split32 b)[0].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_0, pack_lane_2]

theorem split_observe2_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_2.call
      (agave_avx2_field_split_observe_2.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 c)[2].setWidth 64 <<< 26) +
        (split32 c)[0].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_0, pack_lane_2]

theorem split_observe3_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_3.call
      (agave_avx2_field_split_observe_3.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 d)[2].setWidth 64 <<< 26) +
        (split32 d)[0].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_0, pack_lane_2]

theorem split_observe4_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_4.call
      (agave_avx2_field_split_observe_4.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 e)[2].setWidth 64 <<< 26) +
        (split32 e)[0].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_0, pack_lane_2]

theorem split_observe5_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_5.call
      (agave_avx2_field_split_observe_5.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 a)[3].setWidth 64 <<< 26) +
        (split32 a)[1].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_1, pack_lane_3]

theorem split_observe6_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_6.call
      (agave_avx2_field_split_observe_6.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 b)[3].setWidth 64 <<< 26) +
        (split32 b)[1].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_1, pack_lane_3]

theorem split_observe7_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_7.call
      (agave_avx2_field_split_observe_7.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 c)[3].setWidth 64 <<< 26) +
        (split32 c)[1].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_1, pack_lane_3]

theorem split_observe8_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_8.call
      (agave_avx2_field_split_observe_8.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 d)[3].setWidth 64 <<< 26) +
        (split32 d)[1].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_1, pack_lane_3]

theorem split_observe9_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_9.call
      (agave_avx2_field_split_observe_9.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 e)[3].setWidth 64 <<< 26) +
        (split32 e)[1].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_1, pack_lane_3]

theorem split_observe10_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_10.call
      (agave_avx2_field_split_observe_10.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 a)[6].setWidth 64 <<< 26) +
        (split32 a)[4].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_4, pack_lane_6]

theorem split_observe11_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_11.call
      (agave_avx2_field_split_observe_11.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 b)[6].setWidth 64 <<< 26) +
        (split32 b)[4].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_4, pack_lane_6]

theorem split_observe12_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_12.call
      (agave_avx2_field_split_observe_12.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 c)[6].setWidth 64 <<< 26) +
        (split32 c)[4].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_4, pack_lane_6]

theorem split_observe13_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_13.call
      (agave_avx2_field_split_observe_13.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 d)[6].setWidth 64 <<< 26) +
        (split32 d)[4].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_4, pack_lane_6]

theorem split_observe14_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_14.call
      (agave_avx2_field_split_observe_14.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 e)[6].setWidth 64 <<< 26) +
        (split32 e)[4].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_4, pack_lane_6]

theorem split_observe15_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_15.call
      (agave_avx2_field_split_observe_15.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 a)[7].setWidth 64 <<< 26) +
        (split32 a)[5].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_5, pack_lane_7]

theorem split_observe16_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_16.call
      (agave_avx2_field_split_observe_16.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 b)[7].setWidth 64 <<< 26) +
        (split32 b)[5].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_5, pack_lane_7]

theorem split_observe17_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_17.call
      (agave_avx2_field_split_observe_17.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 c)[7].setWidth 64 <<< 26) +
        (split32 c)[5].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_5, pack_lane_7]

theorem split_observe18_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_18.call
      (agave_avx2_field_split_observe_18.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 d)[7].setWidth 64 <<< 26) +
        (split32 d)[5].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_5, pack_lane_7]

theorem split_observe19_call (a b c d e : V64) (s : GlobalState) (hwf : s.WF) :
    agave_avx2_field_split_observe_19.call
      (agave_avx2_field_split_observe_19.args
        (Ty.wrap a) (Ty.wrap b) (Ty.wrap c) (Ty.wrap d) (Ty.wrap e)) s =
      .value (.cons (.value (((split32 e)[7].setWidth 64 <<< 26) +
        (split32 e)[5].setWidth 64)) .nil, s) := by
  func_init
  block_init
  iterate 3 step_pure
  step_pure [bitcast_split32]
  step_pure [split32]
  step_pure
  step_pure [split32]
  step_pure
  step_pure [split_shift_value]
  step_pure [split_add_value]
  finish_block
  rw [hS]
  simp [Ty.wrap_vec, Vector.map_map, Function.comp_def, wide32_shift_u,
    wide32_shift_s, (wide32_add_safe _ _).1, (wide32_add_safe _ _).2,
    pack_lane_5, pack_lane_7]

end
end Agave.Ed25519.Encoding.RIR
