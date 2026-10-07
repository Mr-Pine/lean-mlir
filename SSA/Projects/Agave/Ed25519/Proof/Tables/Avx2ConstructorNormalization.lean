import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorNormalizationWords
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheExecution

/-! The exact initial carry32 instruction interval, retaining poison semantics
and both LLVM overflow flags. The arithmetic value bridge is separate. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Normalization
open LeanMLIR.RIR Packing CachePhases
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def input (E : ⟪kernel.Γ⟫) (a : SerialPoint) : ⟪kernel.Γ⟫ :=
  E[%28 := Ty.wrap shifts, %29 := Ty.wrap masks,
    %30 := Ty.wrap (#v[0, 0, 127, 127, 0, 0, 127, 127] : Vector (BitVec 32) 8),
    %31 := Ty.poisoned (.vec 8 32),
    %32 := Vector.replicate 4 (.value 19#64),
    %415 := Ty.wrap (pack a 0), %431 := Ty.wrap (pack a 1),
    %447 := Ty.wrap (pack a 2), %463 := Ty.wrap (pack a 3), %479 := Ty.wrap (pack a 4)]

def reads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%504), E.read (%485), E.read (%489), E.read (%493), E.read (%497)]

def normalizedBlocks (a : SerialPoint) : Blocks :=
  ![first (pack a 4) (pack a 0),step (pack a 0) (pack a 1),
    step (pack a 1) (pack a 2),step (pack a 2) (pack a 3),step (pack a 3) (pack a 4)]

private theorem source_0 (E : ⟪kernel.Γ⟫) (a : SerialPoint) :
    reads (normalizeResult (input E a)) 0 = firstInstructions (Ty.wrap (pack a 4)) (Ty.wrap (pack a 0)) := by
  simp only [reads, normalizeResult, normalize0, normalize1, input,
    firstInstructions, foldInstructions, stepInstructions, mlir_env]
  rfl

private theorem source_1 (E : ⟪kernel.Γ⟫) (a : SerialPoint) :
    reads (normalizeResult (input E a)) 1 = stepInstructions (Ty.wrap (pack a 0)) (Ty.wrap (pack a 1)) := by
  simp only [reads, normalizeResult, normalize0, normalize1, input,
    firstInstructions, foldInstructions, stepInstructions, mlir_env]
  rfl

private theorem source_2 (E : ⟪kernel.Γ⟫) (a : SerialPoint) :
    reads (normalizeResult (input E a)) 2 = stepInstructions (Ty.wrap (pack a 1)) (Ty.wrap (pack a 2)) := by
  simp only [reads, normalizeResult, normalize0, normalize1, input,
    firstInstructions, foldInstructions, stepInstructions, mlir_env]
  rfl

private theorem source_3 (E : ⟪kernel.Γ⟫) (a : SerialPoint) :
    reads (normalizeResult (input E a)) 3 = stepInstructions (Ty.wrap (pack a 2)) (Ty.wrap (pack a 3)) := by
  simp only [reads, normalizeResult, normalize0, normalize1, input,
    firstInstructions, foldInstructions, stepInstructions, mlir_env]
  rfl

private theorem source_4 (E : ⟪kernel.Γ⟫) (a : SerialPoint) :
    reads (normalizeResult (input E a)) 4 = stepInstructions (Ty.wrap (pack a 3)) (Ty.wrap (pack a 4)) := by
  simp only [reads, normalizeResult, normalize0, normalize1, input,
    firstInstructions, foldInstructions, stepInstructions, mlir_env]
  rfl

/-- All five outputs are nonpoison, with no arithmetic premise on the words. -/
theorem network (E : ⟪kernel.Γ⟫) (a : SerialPoint) (k : Fin 5) :
    reads (normalizeResult (input E a)) k = Ty.wrap (normalizedBlocks a k) := by
  fin_cases k
  · exact (source_0 E a).trans (first_value (pack a 4) (pack a 0))
  · exact (source_1 E a).trans (step_value (pack a 0) (pack a 1))
  · exact (source_2 E a).trans (step_value (pack a 1) (pack a 2))
  · exact (source_3 E a).trans (step_value (pack a 2) (pack a 3))
  · exact (source_4 E a).trans (step_value (pack a 3) (pack a 4))

end Agave.Ed25519.Tables.Avx2Constructor.Normalization
