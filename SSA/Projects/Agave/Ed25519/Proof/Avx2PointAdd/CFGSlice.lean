import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Avx2Program
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseRepresentation
import SSA.Projects.RIR.Run.BasicBlock
import SSA.Projects.RIR.Run.Vector

/-! Local instruction intervals of the unchanged double-base CFG.
The interval runner does not replace a block: `runBodyFrom_slice` reconnects
its checked result to the original block's remaining instructions. -/
namespace Agave.Ed25519.Avx2PointAdd.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR Phases

def runSlice (block : BasicBlock Γ tRets bp) (E : ⟪Γ⟫) (start count : Nat) :
    EffectM ⟪Γ⟫ :=
  List.foldlM Instr.run E ((block.body.drop start).take count)

theorem runBodyFrom_slice (block : BasicBlock Γ tRets bp)
    (E E' : ⟪Γ⟫) (start count : Nat) (s s' : GlobalState)
    (h : runSlice block E start count s = .value (E', s')) :
    block.runBodyFrom E start s = block.runBodyFrom E' (start + count) s' := by
  unfold BasicBlock.runBodyFrom
  have hsplit := List.take_append_drop count (block.body.drop start)
  rw [← hsplit, List.foldlM_append]
  change (runSlice block E start count s >>= fun es =>
    List.foldlM Instr.run es.1 ((block.body.drop start).drop count) es.2) = _
  rw [h]
  simp only [PoisonOr.value_bind, List.drop_drop, Nat.add_comm]

def prepareConstants (k : Fin 5) : ⟦Ty.vec 8 32⟧ :=
  #v[.value (evenConstant k), .poison, .value (oddConstant k), .poison,
     .poison, .poison, .poison, .poison]

def differenceConstants (k : Fin 5) : ⟦Ty.vec 8 32⟧ :=
  #v[.value (evenConstant k), .poison, .value (oddConstant k), .poison,
     .value (evenConstant k), .poison, .value (oddConstant k), .poison]

def negateConstants (k : Fin 5) : ⟦Ty.vec 8 32⟧ :=
  #v[.poison, .poison, .poison, .poison, .poison,
     .value (evenConstant k), .poison, .value (oddConstant k)]

/-- The seven invariant constants read by all four point-add/subtract blocks.
These are ordinary register-read facts to be supplied by the bb0 proof. -/
structure Constants (E : ⟪avx2Kernel.Γ⟫) : Prop where
  poison : E.read (%26) = Ty.poisoned (.vec 8 32)
  prepare0 : E.read (%135) = prepareConstants 0
  prepareN : E.read (%152) = prepareConstants 1
  difference0 : E.read (%170) = differenceConstants 0
  differenceN : E.read (%187) = differenceConstants 1
  negate0 : E.read (%204) = negateConstants 0
  negateN : E.read (%221) = negateConstants 1

def abdcVec (x : PackedVec32) : PackedVec32 :=
  #v[x[0], x[1], x[2], x[3], x[5], x[4], x[7], x[6]]

theorem abdc_shuffle (x : PackedVec32) :
    Operation.shufflevector
      #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6]
      (Ty.wrap x) (Ty.poisoned (.vec 8 32)) = Ty.wrap (abdcVec x) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [abdcVec, Ty.wrap_vec]

end Agave.Ed25519.Avx2PointAdd.CFG
