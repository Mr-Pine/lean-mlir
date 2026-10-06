module

public import SSA.Projects.Agave.Ed25519.Proof.Encoding.Program

namespace Agave.Ed25519.Encoding.RIR
open LeanMLIR.RIR
@[expose] public section

theorem from_bytes0_call (a b c d : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    agave_serial_field_from_bytes_observe_0.call
      (agave_serial_field_from_bytes_observe_0.args
        (.value a) (.value b) (.value c) (.value d)) s =
      .value (.cons (.value (a &&& 2251799813685247)) .nil, s) := by
  func_init
  block_init
  iterate 2 step_pure
  finish_block
  rw [hS]
  rfl

theorem from_bytes4_call (a b c d : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    agave_serial_field_from_bytes_observe_4.call
      (agave_serial_field_from_bytes_observe_4.args
        (.value a) (.value b) (.value c) (.value d)) s =
      .value (.cons (.value ((d >>> 12) &&& 2251799813685247)) .nil, s) := by
  func_init
  block_init
  iterate 4 step_pure
  finish_block
  rw [hS]
  rfl

end
end Agave.Ed25519.Encoding.RIR
