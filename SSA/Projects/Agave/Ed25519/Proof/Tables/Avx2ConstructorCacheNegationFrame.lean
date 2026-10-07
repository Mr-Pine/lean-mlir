import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheNegationNetwork
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame

/-! Exact register frames and transport of the low constructor constants. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CacheNegation
open LeanMLIR.RIR
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem initial_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 612 650 E (initialResult E) := by
  unfold initialResult CacheEdges.initialNegate2 CacheEdges.initialNegate1 CacheEdges.initialNegate0
  extract_lets
  iterate 38 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem successor_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 988 1026 E (successorResult E) := by
  unfold successorResult CacheEdges.successorNegate2 CacheEdges.successorNegate1 CacheEdges.successorNegate0
  extract_lets
  iterate 38 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem ConstantsReady.of_frame {E F : ⟪kernel.Γ⟫} (hc : ConstantsReady E)
    (hf : RegisterFrame lo hi E F) (hlo : 195 ≤ lo) : ConstantsReady F := by
  constructor
  · exact (hf.read (%28) (Or.inl (by change 28 < lo; omega))).trans hc.r28
  · exact (hf.read (%31) (Or.inl (by change 31 < lo; omega))).trans hc.r31
  · exact (hf.read (%71) (Or.inl (by change 71 < lo; omega))).trans hc.r71
  · exact (hf.read (%146) (Or.inl (by change 146 < lo; omega))).trans hc.r146
  · exact (hf.read (%147) (Or.inl (by change 147 < lo; omega))).trans hc.r147
  · exact (hf.read (%148) (Or.inl (by change 148 < lo; omega))).trans hc.r148
  · exact (hf.read (%165) (Or.inl (by change 165 < lo; omega))).trans hc.r165
  · exact (hf.read (%183) (Or.inl (by change 183 < lo; omega))).trans hc.r183
  · exact (hf.read (%194) (Or.inl (by change 194 < lo; omega))).trans hc.r194

end Agave.Ed25519.Tables.Avx2Constructor.CacheNegation
