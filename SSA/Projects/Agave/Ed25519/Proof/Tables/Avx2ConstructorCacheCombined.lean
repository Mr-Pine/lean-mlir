import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCachePrepare
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheScaleNetwork
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheNegationNetwork

/-! Composition of the exact 25 + 82 + 38 instruction cache conversions. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CacheCombined
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

structure Constants (E : ⟪kernel.Γ⟫) : Prop where
  r31 : E.read (%31) = Ty.poisoned (.vec 8 32)
  r52 : E.read (%52) = Avx2PointAdd.CFG.prepareConstants 0
  r70 : E.read (%70) = Avx2PointAdd.CFG.prepareConstants 1
  scale : CacheScale.ConstantsReady E
  negation : CacheNegation.ConstantsReady E

theorem constants_ready (E : ⟪kernel.Γ⟫) : Constants (Avx2Constructor.Constants.result E) :=
  ⟨Avx2Constructor.Constants.read_31 E, Avx2Constructor.Constants.read_52 E,
   Avx2Constructor.Constants.read_70 E, CacheScale.constants_ready E,
   CacheNegation.constants_ready E⟩

theorem Constants.frame {E F : ⟪kernel.Γ⟫} (h : Constants E)
    (hf : RegisterFrame 352 kernel.Γ.n E F) : Constants F := by
  refine ⟨(hf.read (%31) (by decide)).trans h.r31,
    (hf.read (%52) (by decide)).trans h.r52,
    (hf.read (%70) (by decide)).trans h.r70, ?_, ?_⟩
  · exact ⟨(hf.read (%27) (by decide)).trans h.scale.r27,
      (hf.read (%32) (by decide)).trans h.scale.r32,
      (hf.read (%88) (by decide)).trans h.scale.r88,
      (hf.read (%105) (by decide)).trans h.scale.r105,
      (hf.read (%106) (by decide)).trans h.scale.r106,
      (hf.read (%107) (by decide)).trans h.scale.r107,
      (hf.read (%108) (by decide)).trans h.scale.r108,
      (hf.read (%109) (by decide)).trans h.scale.r109,
      (hf.read (%127) (by decide)).trans h.scale.r127,
      (hf.read (%145) (by decide)).trans h.scale.r145⟩
  · exact ⟨(hf.read (%28) (by decide)).trans h.negation.r28,
      (hf.read (%31) (by decide)).trans h.negation.r31,
      (hf.read (%71) (by decide)).trans h.negation.r71,
      (hf.read (%146) (by decide)).trans h.negation.r146,
      (hf.read (%147) (by decide)).trans h.negation.r147,
      (hf.read (%148) (by decide)).trans h.negation.r148,
      (hf.read (%165) (by decide)).trans h.negation.r165,
      (hf.read (%183) (by decide)).trans h.negation.r183,
      (hf.read (%194) (by decide)).trans h.negation.r194⟩

def initialInputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%504), E.read (%485), E.read (%489), E.read (%493), E.read (%497)]

theorem initial_input_ready (E : ⟪kernel.Γ⟫) (P : Point) (hc : Constants E)
    (hin : ∀ k, initialInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint P k)) :
    CachePreparation.initialInput E P = E := by
  have h0 : E.read (%504) = Ty.wrap (packPoint P 0) := hin 0
  have h1 : E.read (%485) = Ty.wrap (packPoint P 1) := hin 1
  have h2 : E.read (%489) = Ty.wrap (packPoint P 2) := hin 2
  have h3 : E.read (%493) = Ty.wrap (packPoint P 3) := hin 3
  have h4 : E.read (%497) = Ty.wrap (packPoint P 4) := hin 4
  unfold CachePreparation.initialInput
  rw [Env.write_of_read E (%31) hc.r31,
    Env.write_of_read E (%52) hc.r52,
    Env.write_of_read E (%70) hc.r70,
    Env.write_of_read E (%504) h0,
    Env.write_of_read E (%485) h1,
    Env.write_of_read E (%489) h2,
    Env.write_of_read E (%493) h3,
    Env.write_of_read E (%497) h4]

private theorem initial_scale_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 530 612 E (CacheScale.initialScale E) := by
  unfold CacheScale.initialScale
  extract_lets
  iterate 82 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

private theorem initial_negation_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 612 650 E (CacheNegation.initialResult E) := by
  unfold CacheNegation.initialResult CacheEdges.initialNegate2
    CacheEdges.initialNegate1 CacheEdges.initialNegate0
  extract_lets
  iterate 38 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

def initialResult (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  CacheNegation.initialResult (CacheScale.initialScale (CachePrepare.initialResult E))

theorem initial_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 505 650 E (initialResult E) :=
  ((CachePrepare.initial_frame E).weaken (by decide) (by decide)).trans
    (((initial_scale_frame _).weaken (by decide) (by decide)).trans
      ((initial_negation_frame _).weaken (by decide) (by decide)))

theorem initial_point (E : ⟪kernel.Γ⟫) (hc : Constants E)
    {P : Point} (hP : pointReduced P)
    (hin : ∀ k, initialInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint P k))
    (k : Fin 5) :
    CacheNegation.initialOutputReads (initialResult E) k =
      Ty.wrap (packPoint (CacheArithmetic.cache P) k) := by
  have hp : ∀ k, CachePrepare.initialReads (CachePrepare.initialResult E) k =
      Ty.wrap (t := .vec 8 32) (packPoint (prepare P) k) := by
    intro k
    have h := CachePrepare.initial_point E hP k
    rw [initial_input_ready E P hc hin] at h
    exact h
  have hc1 := hc.frame ((CachePrepare.initial_frame E).weaken (by decide) (by decide))
  have hs := CacheScale.initial_point (CachePrepare.initialResult E) hc1.scale
    (prepare_wide hP) hp
  have hc2 := hc1.frame ((initial_scale_frame _).weaken (by decide) (by decide))
  exact CacheNegation.initial_point _ hc2.negation
    (CacheScale.scaledPoint_reduced (prepare_wide hP)) hs k

theorem initial_run (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb0 p) E 505 145 s = .value (initialResult E,s) := by
  apply TightPrefix.runSlice_add _ E (CachePrepare.initialResult E) _ 505 25 120 s s s
    (CachePrepare.initial_run p E s)
  exact TightPrefix.runSlice_add _ _ (CacheScale.initialScale (CachePrepare.initialResult E)) _
    530 82 38 s s s (CacheScale.initialScale_slice p _ s)
    (CacheNegation.initial_slice p _ s)

theorem initial_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb0 p).runBodyFrom E 505 s =
      (kernel.bb0 p).runBodyFrom (initialResult E) 650 s :=
  runBodyFrom_slice _ E (initialResult E) 505 145 s s (initial_run p E s)

def successorInputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%876), E.read (%877), E.read (%878), E.read (%879), E.read (%880)]

theorem successor_input_ready (E : ⟪kernel.Γ⟫) (P : Point) (hc : Constants E)
    (hin : ∀ k, successorInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint P k)) :
    CachePreparation.successorInput E P = E := by
  have h0 : E.read (%876) = Ty.wrap (packPoint P 0) := hin 0
  have h1 : E.read (%877) = Ty.wrap (packPoint P 1) := hin 1
  have h2 : E.read (%878) = Ty.wrap (packPoint P 2) := hin 2
  have h3 : E.read (%879) = Ty.wrap (packPoint P 3) := hin 3
  have h4 : E.read (%880) = Ty.wrap (packPoint P 4) := hin 4
  unfold CachePreparation.successorInput
  rw [Env.write_of_read E (%31) hc.r31,
    Env.write_of_read E (%52) hc.r52,
    Env.write_of_read E (%70) hc.r70,
    Env.write_of_read E (%876) h0,
    Env.write_of_read E (%877) h1,
    Env.write_of_read E (%878) h2,
    Env.write_of_read E (%879) h3,
    Env.write_of_read E (%880) h4]

private theorem successor_scale_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 906 988 E (CacheScale.successorScale E) := by
  unfold CacheScale.successorScale
  extract_lets
  iterate 82 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

private theorem successor_negation_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 988 1026 E (CacheNegation.successorResult E) := by
  unfold CacheNegation.successorResult CacheEdges.successorNegate2
    CacheEdges.successorNegate1 CacheEdges.successorNegate0
  extract_lets
  iterate 38 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

def successorResult (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  CacheNegation.successorResult (CacheScale.successorScale (CachePrepare.successorResult E))

theorem successor_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 881 1026 E (successorResult E) :=
  ((CachePrepare.successor_frame E).weaken (by decide) (by decide)).trans
    (((successor_scale_frame _).weaken (by decide) (by decide)).trans
      ((successor_negation_frame _).weaken (by decide) (by decide)))

theorem successor_point (E : ⟪kernel.Γ⟫) (hc : Constants E)
    {P : Point} (hP : pointReduced P)
    (hin : ∀ k, successorInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint P k))
    (k : Fin 5) :
    CacheNegation.successorOutputReads (successorResult E) k =
      Ty.wrap (packPoint (CacheArithmetic.cache P) k) := by
  have hp : ∀ k, CachePrepare.successorReads (CachePrepare.successorResult E) k =
      Ty.wrap (t := .vec 8 32) (packPoint (prepare P) k) := by
    intro k
    have h := CachePrepare.successor_point E hP k
    rw [successor_input_ready E P hc hin] at h
    exact h
  have hc1 := hc.frame ((CachePrepare.successor_frame E).weaken (by decide) (by decide))
  have hs := CacheScale.successor_point (CachePrepare.successorResult E) hc1.scale
    (prepare_wide hP) hp
  have hc2 := hc1.frame ((successor_scale_frame _).weaken (by decide) (by decide))
  exact CacheNegation.successor_point _ hc2.negation
    (CacheScale.scaledPoint_reduced (prepare_wide hP)) hs k

theorem successor_run (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 105 145 s = .value (successorResult E,s) := by
  apply TightPrefix.runSlice_add _ E (CachePrepare.successorResult E) _ 105 25 120 s s s
    (CachePrepare.successor_run p E s)
  exact TightPrefix.runSlice_add _ _ (CacheScale.successorScale (CachePrepare.successorResult E)) _
    130 82 38 s s s (CacheScale.successorScale_slice p _ s)
    (CacheNegation.successor_slice p _ s)

theorem successor_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 105 s =
      (kernel.bb2 p).runBodyFrom (successorResult E) 250 s :=
  runBodyFrom_slice _ E (successorResult E) 105 145 s s (successor_run p E s)

end Agave.Ed25519.Tables.Avx2Constructor.CacheCombined
