import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesSafety

namespace Agave.Ed25519.Encoding.RIR
open LeanMLIR.RIR
section
set_option maxHeartbeats 2000000

attribute [-simp] BitVec.shiftLeft_add_distrib in
theorem to_bytes0_call (a0 a1 a2 a3 a4 : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    agave_serial_field_to_bytes_observe_0.call (agave_serial_field_to_bytes_observe_0.args
      (.value a0) (.value a1) (.value a2) (.value a3) (.value a4)) s =
      .value (.cons (.value (toBytesMachine0 a0 a1 a2 a3 a4)) .nil, s) := by
  have hs := toBytesSafe0 a0 a1 a2 a3 a4
  dsimp only at hs
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  func_init
  block_init
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure [h0, h1]
  step_pure [h2, h3]
  step_pure [h4, h5]
  step_pure [h6, h7]
  step_pure [h8, h9]
  step_pure [h10, h11]
  step_pure [h12, h13]
  step_pure
  step_pure [h14, h15]
  step_pure
  step_pure [h16, h17]
  step_pure
  step_pure [h18, h19]
  step_pure
  step_pure [h20, h21]
  step_pure
  step_pure [h22, h23]
  step_pure [h24, h25]
  step_pure
  step_pure
  finish_block
  rw [hS]
  rfl

attribute [-simp] BitVec.shiftLeft_add_distrib in
theorem to_bytes1_call (a0 a1 a2 a3 a4 : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    agave_serial_field_to_bytes_observe_1.call (agave_serial_field_to_bytes_observe_1.args
      (.value a0) (.value a1) (.value a2) (.value a3) (.value a4)) s =
      .value (.cons (.value (toBytesMachine1 a0 a1 a2 a3 a4)) .nil, s) := by
  have hs := toBytesSafe1 a0 a1 a2 a3 a4
  dsimp only at hs
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37⟩
  func_init
  block_init
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure [h0, h1]
  step_pure [h2, h3]
  step_pure [h4, h5]
  step_pure [h6, h7]
  step_pure [h8, h9]
  step_pure [h10, h11]
  step_pure [h12, h13]
  step_pure
  step_pure [h14, h15]
  step_pure
  step_pure [h16, h17]
  step_pure
  step_pure [h18, h19]
  step_pure
  step_pure [h20, h21]
  step_pure
  step_pure [h22, h23]
  step_pure [h24, h25]
  step_pure
  step_pure [h26, h27]
  step_pure
  step_pure [h28, h29]
  step_pure
  step_pure
  step_pure
  step_pure [h30, h31]
  step_pure
  step_pure
  step_pure [h32]
  step_pure [h33, h34]
  step_pure
  step_pure
  step_pure
  step_pure [h35]
  step_pure [h36]
  step_pure [h37]
  finish_block
  rw [hS]
  rfl

attribute [-simp] BitVec.shiftLeft_add_distrib in
theorem to_bytes2_call (a0 a1 a2 a3 a4 : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    agave_serial_field_to_bytes_observe_2.call (agave_serial_field_to_bytes_observe_2.args
      (.value a0) (.value a1) (.value a2) (.value a3) (.value a4)) s =
      .value (.cons (.value (toBytesMachine2 a0 a1 a2 a3 a4)) .nil, s) := by
  have hs := toBytesSafe2 a0 a1 a2 a3 a4
  dsimp only at hs
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39⟩
  func_init
  block_init
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure [h0, h1]
  step_pure [h2, h3]
  step_pure [h4, h5]
  step_pure [h6, h7]
  step_pure [h8, h9]
  step_pure [h10, h11]
  step_pure [h12, h13]
  step_pure
  step_pure [h14, h15]
  step_pure
  step_pure [h16, h17]
  step_pure
  step_pure [h18, h19]
  step_pure
  step_pure [h20, h21]
  step_pure
  step_pure [h22, h23]
  step_pure [h24, h25]
  step_pure
  step_pure [h26, h27]
  step_pure
  step_pure [h28, h29]
  step_pure
  step_pure [h30, h31]
  step_pure
  step_pure
  step_pure
  step_pure [h32, h33]
  step_pure
  step_pure
  step_pure [h34]
  step_pure [h35, h36]
  step_pure
  step_pure
  step_pure
  step_pure [h37]
  step_pure [h38]
  step_pure [h39]
  finish_block
  rw [hS]
  rfl

attribute [-simp] BitVec.shiftLeft_add_distrib in
theorem to_bytes3_call (a0 a1 a2 a3 a4 : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    agave_serial_field_to_bytes_observe_3.call (agave_serial_field_to_bytes_observe_3.args
      (.value a0) (.value a1) (.value a2) (.value a3) (.value a4)) s =
      .value (.cons (.value (toBytesMachine3 a0 a1 a2 a3 a4)) .nil, s) := by
  have hs := toBytesSafe3 a0 a1 a2 a3 a4
  dsimp only at hs
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41⟩
  func_init
  block_init
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure [h0, h1]
  step_pure [h2, h3]
  step_pure [h4, h5]
  step_pure [h6, h7]
  step_pure [h8, h9]
  step_pure [h10, h11]
  step_pure [h12, h13]
  step_pure
  step_pure [h14, h15]
  step_pure
  step_pure [h16, h17]
  step_pure
  step_pure [h18, h19]
  step_pure
  step_pure [h20, h21]
  step_pure
  step_pure [h22, h23]
  step_pure [h24, h25]
  step_pure
  step_pure [h26, h27]
  step_pure
  step_pure [h28, h29]
  step_pure
  step_pure [h30, h31]
  step_pure
  step_pure [h32, h33]
  step_pure
  step_pure
  step_pure
  step_pure [h34, h35]
  step_pure [h36]
  step_pure
  step_pure [h37]
  step_pure [h38, h39]
  step_pure
  step_pure
  step_pure [h40]
  step_pure [h41]
  finish_block
  rw [hS]
  rfl

end
end Agave.Ed25519.Encoding.RIR
