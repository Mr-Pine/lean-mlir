import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheEdges
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCachePreparation
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorTightPrefix
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorStack

/-! Exact 25-instruction preparation boundaries for composing the cache stages. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CachePrepare
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases CacheEdges
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2PointAdd.CFG (runSlice)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def initialResult (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  initialPrepare1 (initialPrepare0 E)

theorem initial_run (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb0 p) E 505 25 s = .value (initialResult E,s) :=
  TightPrefix.runSlice_add _ E (initialPrepare0 E) (initialResult E) 505 15 10 s s s
    (initialPrepare0_slice p E s) (initialPrepare1_slice p (initialPrepare0 E) s)

theorem initial_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 505 530 E (initialResult E) := by
  unfold initialResult initialPrepare1 initialPrepare0
  extract_lets
  iterate 25 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

def initialReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%525), E.read (%526), E.read (%527), E.read (%528), E.read (%529)]

private theorem initial_prefix (E : ⟪kernel.Γ⟫) :
    initialPrepare0 E = CachePhases.initialCache0 E := rfl

private theorem initial_read_525 (E : ⟪kernel.Γ⟫) :
    (initialPrepare1 E).read (%525) = (CachePhases.initialCache1 E).read (%525) := by
  unfold initialPrepare1 CachePhases.initialCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem initial_read_526 (E : ⟪kernel.Γ⟫) :
    (initialPrepare1 E).read (%526) = (CachePhases.initialCache1 E).read (%526) := by
  unfold initialPrepare1 CachePhases.initialCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem initial_read_527 (E : ⟪kernel.Γ⟫) :
    (initialPrepare1 E).read (%527) = (CachePhases.initialCache1 E).read (%527) := by
  unfold initialPrepare1 CachePhases.initialCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem initial_read_528 (E : ⟪kernel.Γ⟫) :
    (initialPrepare1 E).read (%528) = (CachePhases.initialCache1 E).read (%528) := by
  unfold initialPrepare1 CachePhases.initialCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem initial_read_529 (E : ⟪kernel.Γ⟫) :
    (initialPrepare1 E).read (%529) = (CachePhases.initialCache1 E).read (%529) := by
  unfold initialPrepare1 CachePhases.initialCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem initial_reads (E : ⟪kernel.Γ⟫) (k : Fin 5) :
    initialReads (initialPrepare1 E) k = CachePreparation.initialReads (CachePhases.initialCache1 E) k := by
  fin_cases k <;> simp [initialReads, CachePreparation.initialReads,
    initial_read_525, initial_read_526, initial_read_527, initial_read_528, initial_read_529]

theorem initial_point (E : ⟪kernel.Γ⟫) {P : Point} (hP : pointReduced P) (k : Fin 5) :
    initialReads (initialResult (CachePreparation.initialInput E P)) k =
      Ty.wrap (packPoint (prepare P) k) := by
  unfold initialResult
  rw [initial_reads, initial_prefix]
  exact CachePreparation.initial_point E hP k

def successorResult (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  successorPrepare1 (successorPrepare0 E)

theorem successor_run (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 105 25 s = .value (successorResult E,s) :=
  TightPrefix.runSlice_add _ E (successorPrepare0 E) (successorResult E) 105 15 10 s s s
    (successorPrepare0_slice p E s) (successorPrepare1_slice p (successorPrepare0 E) s)

theorem successor_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 881 906 E (successorResult E) := by
  unfold successorResult successorPrepare1 successorPrepare0
  extract_lets
  iterate 25 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

def successorReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%901), E.read (%902), E.read (%903), E.read (%904), E.read (%905)]

private theorem successor_prefix (E : ⟪kernel.Γ⟫) :
    successorPrepare0 E = CachePhases.successorCache0 E := rfl

private theorem successor_read_901 (E : ⟪kernel.Γ⟫) :
    (successorPrepare1 E).read (%901) = (CachePhases.successorCache1 E).read (%901) := by
  unfold successorPrepare1 CachePhases.successorCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem successor_read_902 (E : ⟪kernel.Γ⟫) :
    (successorPrepare1 E).read (%902) = (CachePhases.successorCache1 E).read (%902) := by
  unfold successorPrepare1 CachePhases.successorCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem successor_read_903 (E : ⟪kernel.Γ⟫) :
    (successorPrepare1 E).read (%903) = (CachePhases.successorCache1 E).read (%903) := by
  unfold successorPrepare1 CachePhases.successorCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem successor_read_904 (E : ⟪kernel.Γ⟫) :
    (successorPrepare1 E).read (%904) = (CachePhases.successorCache1 E).read (%904) := by
  unfold successorPrepare1 CachePhases.successorCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem successor_read_905 (E : ⟪kernel.Γ⟫) :
    (successorPrepare1 E).read (%905) = (CachePhases.successorCache1 E).read (%905) := by
  unfold successorPrepare1 CachePhases.successorCache1
  extract_lets
  simp (disch := decide) only [Env.read_write_ne, Env.read_write_self]
  rfl

private theorem successor_reads (E : ⟪kernel.Γ⟫) (k : Fin 5) :
    successorReads (successorPrepare1 E) k = CachePreparation.successorReads (CachePhases.successorCache1 E) k := by
  fin_cases k <;> simp [successorReads, CachePreparation.successorReads,
    successor_read_901, successor_read_902, successor_read_903, successor_read_904, successor_read_905]

theorem successor_point (E : ⟪kernel.Γ⟫) {P : Point} (hP : pointReduced P) (k : Fin 5) :
    successorReads (successorResult (CachePreparation.successorInput E P)) k =
      Ty.wrap (packPoint (prepare P) k) := by
  unfold successorResult
  rw [successor_reads, successor_prefix]
  exact CachePreparation.successor_point E hP k

end Agave.Ed25519.Tables.Avx2Constructor.CachePrepare
