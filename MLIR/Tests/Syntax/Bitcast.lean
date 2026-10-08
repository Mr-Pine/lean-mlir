module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic

/-! # Vector lanes: literal reads and bitcasts -/

namespace MLIR.Tests.Syntax.Bitcast

@[expose] public section

-- a literal vector's lane read by a proof step: as a `dsimp` step, folded with `0#8 ++ 0#8`, the
-- kernel (in a module) rejects the proof
example (v : BitVec 8) : [#v[0#8, v][0] ++ 0#8, 1] = [0, 1] := by
  simp [mlir_operation]

end

end MLIR.Tests.Syntax.Bitcast
