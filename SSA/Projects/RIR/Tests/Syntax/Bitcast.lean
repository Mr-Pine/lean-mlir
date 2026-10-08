module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Run.Tactic

/-! # Vector lanes: literal reads and bitcasts -/

namespace LeanMLIR.RIR.Tests.Syntax.Bitcast

@[expose] public section

-- a literal vector's lane read by a proof step: as a `dsimp` step, folded with `0#8 ++ 0#8`, the
-- kernel (in a module) rejects the proof
example (v : BitVec 8) : [#v[0#8, v][0] ++ 0#8, 1] = [0, 1] := by
  simp [mlir_operation]

-- a lane at `⟨k, _⟩` or `↑⟨k, _⟩` is the lane at `k`, as specs write it
example (x : Vector (BitVec 64) 8) :
    (Vector.ofFn fun i : Fin 8 => x[i] + x[i.1])[3] = x[3] + x[3] := by
  simp only [Vector.getElem_ofFn, reduceGetElemLit]

end

end LeanMLIR.RIR.Tests.Syntax.Bitcast
