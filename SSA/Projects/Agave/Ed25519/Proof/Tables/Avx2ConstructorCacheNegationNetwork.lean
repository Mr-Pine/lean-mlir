import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheNegationRepresentation
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheEdges
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorTightPrefix
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorConstantValues

/-! Exact source intervals for the final D-coordinate negation. Both intervals
preserve the complete global state, including the ambient memory frame. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CacheNegation
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases CacheEdges
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

structure ConstantsReady (E : ⟪kernel.Γ⟫) : Prop where
  r28 : E.read (%28) = Ty.wrap (t := .vec 8 32) Normalization.shifts
  r31 : E.read (%31) = Ty.poisoned (.vec 8 32)
  r71 : E.read (%71) = .value 0#32
  r146 : E.read (%146) = Ty.wrap (t := .vec 8 32) (constants 0)
  r147 : E.read (%147) = Ty.wrap (t := .vec 8 32) (constants 1)
  r148 : E.read (%148) = .value 5#64
  r165 : E.read (%165) = maskD
  r183 : E.read (%183) = #v[.poison,.poison,.poison,.poison,.poison,.value 0#32,.poison,.value 15#32]
  r194 : E.read (%194) = #v[.poison,.poison,.poison,.value 19#64]

theorem constants_ready (E : ⟪kernel.Γ⟫) : ConstantsReady (Constants.result E) := by
  constructor
  · simpa [Ty.wrap_vec, Normalization.shifts, constants, evenIndex, oddIndex,
      CacheArithmetic.sixteenP, word, maskD, Ty.poisoned] using Constants.read_28 E
  · exact Constants.read_31 E
  · simpa [Ty.wrap_vec, Normalization.shifts, constants, evenIndex, oddIndex,
      CacheArithmetic.sixteenP, word, maskD, Ty.poisoned] using Constants.read_71 E
  · simpa [Ty.wrap_vec, Normalization.shifts, constants, evenIndex, oddIndex,
      CacheArithmetic.sixteenP, word, maskD, Ty.poisoned] using Constants.read_146 E
  · simpa [Ty.wrap_vec, Normalization.shifts, constants, evenIndex, oddIndex,
      CacheArithmetic.sixteenP, word, maskD, Ty.poisoned] using Constants.read_147 E
  · simpa [Ty.wrap_vec, Normalization.shifts, constants, evenIndex, oddIndex,
      CacheArithmetic.sixteenP, word, maskD, Ty.poisoned] using Constants.read_148 E
  · simpa [Ty.wrap_vec, Normalization.shifts, constants, evenIndex, oddIndex,
      CacheArithmetic.sixteenP, word, maskD, Ty.poisoned] using Constants.read_165 E
  · simpa [Ty.wrap_vec, Normalization.shifts, constants, evenIndex, oddIndex,
      CacheArithmetic.sixteenP, word, maskD, Ty.poisoned] using Constants.read_183 E
  · simpa [Ty.wrap_vec, Normalization.shifts, constants, evenIndex, oddIndex,
      CacheArithmetic.sixteenP, word, maskD, Ty.poisoned] using Constants.read_194 E

def initialResult (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  initialNegate2 (initialNegate1 (initialNegate0 E))

theorem initial_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb0 p) E 612 38 s = .value (initialResult E, s) := by
  exact TightPrefix.runSlice_add _ E (initialNegate0 E) (initialResult E)
    612 15 23 s s s (initialNegate0_slice p E s)
    (TightPrefix.runSlice_add _ (initialNegate0 E) (initialNegate1 (initialNegate0 E))
      (initialResult E) 627 15 8 s s s
      (initialNegate1_slice p _ s) (initialNegate2_slice p _ s))

theorem initial_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb0 p).runBodyFrom E 612 s =
      (kernel.bb0 p).runBodyFrom (initialResult E) 650 s :=
  runBodyFrom_slice _ E (initialResult E) 612 38 s s (initial_slice p E s)

def initialInputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%592), E.read (%597), E.read (%601), E.read (%606), E.read (%611)]

def initialOutputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%645), E.read (%646), E.read (%647), E.read (%648), E.read (%649)]

theorem initial_network (E : ⟪kernel.Γ⟫) (hc : ConstantsReady E) (k : Fin 5) :
    initialOutputReads (initialResult E) k = instructions (initialInputReads E) k := by
  rcases hc with ⟨h28,h31,h71,h146,h147,h148,h165,h183,h194⟩
  fin_cases k <;> dsimp only [initialOutputReads, initialInputReads, instructions]
  all_goals
    simp (disch := decide) only [initialResult,
      initialNegate0, initialNegate1, initialNegate2,
      subtract, blend, firstInstructions, stepInstructions, foldInstructions,
      h28,h31,h71,h146,h147,h148,h165,h183,h194, mlir_env]
  all_goals rfl

theorem initial_point (E : ⟪kernel.Γ⟫) (hc : ConstantsReady E)
    {Q : Point} (hQ : pointReduced Q)
    (hin : ∀ k, initialInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint Q k))
    (k : Fin 5) :
    initialOutputReads (initialResult E) k = Ty.wrap (packPoint (resultPoint Q) k) := by
  rw [initial_network E hc, funext hin, instructions_point hQ]

/-- Source execution and arithmetic outputs with the complete incoming state retained. -/
theorem initial_correct (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (hc : ConstantsReady E) {Q : Point} (hQ : pointReduced Q)
    (hin : ∀ k, initialInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint Q k)) :
    runSlice (kernel.bb0 p) E 612 38 s = .value (initialResult E, s) ∧
      ∀ k, initialOutputReads (initialResult E) k = Ty.wrap (packPoint (resultPoint Q) k) :=
  ⟨initial_slice p E s, initial_point E hc hQ hin⟩

def successorResult (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  successorNegate2 (successorNegate1 (successorNegate0 E))

theorem successor_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 212 38 s = .value (successorResult E, s) := by
  exact TightPrefix.runSlice_add _ E (successorNegate0 E) (successorResult E)
    212 15 23 s s s (successorNegate0_slice p E s)
    (TightPrefix.runSlice_add _ (successorNegate0 E) (successorNegate1 (successorNegate0 E))
      (successorResult E) 227 15 8 s s s
      (successorNegate1_slice p _ s) (successorNegate2_slice p _ s))

theorem successor_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 212 s =
      (kernel.bb2 p).runBodyFrom (successorResult E) 250 s :=
  runBodyFrom_slice _ E (successorResult E) 212 38 s s (successor_slice p E s)

def successorInputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%968), E.read (%973), E.read (%977), E.read (%982), E.read (%987)]

def successorOutputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%1021), E.read (%1022), E.read (%1023), E.read (%1024), E.read (%1025)]

theorem successor_network (E : ⟪kernel.Γ⟫) (hc : ConstantsReady E) (k : Fin 5) :
    successorOutputReads (successorResult E) k = instructions (successorInputReads E) k := by
  rcases hc with ⟨h28,h31,h71,h146,h147,h148,h165,h183,h194⟩
  fin_cases k <;> dsimp only [successorOutputReads, successorInputReads, instructions]
  all_goals
    simp (disch := decide) only [successorResult,
      successorNegate0, successorNegate1, successorNegate2,
      subtract, blend, firstInstructions, stepInstructions, foldInstructions,
      h28,h31,h71,h146,h147,h148,h165,h183,h194, mlir_env]
  all_goals rfl

theorem successor_point (E : ⟪kernel.Γ⟫) (hc : ConstantsReady E)
    {Q : Point} (hQ : pointReduced Q)
    (hin : ∀ k, successorInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint Q k))
    (k : Fin 5) :
    successorOutputReads (successorResult E) k = Ty.wrap (packPoint (resultPoint Q) k) := by
  rw [successor_network E hc, funext hin, instructions_point hQ]

/-- Source execution and arithmetic outputs with the complete incoming state retained. -/
theorem successor_correct (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (hc : ConstantsReady E) {Q : Point} (hQ : pointReduced Q)
    (hin : ∀ k, successorInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint Q k)) :
    runSlice (kernel.bb2 p) E 212 38 s = .value (successorResult E, s) ∧
      ∀ k, successorOutputReads (successorResult E) k = Ty.wrap (packPoint (resultPoint Q) k) :=
  ⟨successor_slice p E s, successor_point E hc hQ hin⟩

end Agave.Ed25519.Tables.Avx2Constructor.CacheNegation
