import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheScaleNetwork
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame

/-! Exact register frames and transport of the low constructor constants. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CacheScale
open LeanMLIR.RIR
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem initial_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 530 612 E (initialScale E) := by
  unfold initialScale
  extract_lets
  iterate 82 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem successor_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 906 988 E (successorScale E) := by
  unfold successorScale
  extract_lets
  iterate 82 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem ConstantsReady.of_frame {E F : ⟪kernel.Γ⟫} (hc : ConstantsReady E)
    (hf : RegisterFrame lo hi E F) (hlo : 146 ≤ lo) : ConstantsReady F := by
  constructor
  · exact (hf.read (%27) (Or.inl (by change 27 < lo; omega))).trans hc.r27
  · exact (hf.read (%32) (Or.inl (by change 32 < lo; omega))).trans hc.r32
  · exact (hf.read (%88) (Or.inl (by change 88 < lo; omega))).trans hc.r88
  · exact (hf.read (%105) (Or.inl (by change 105 < lo; omega))).trans hc.r105
  · exact (hf.read (%106) (Or.inl (by change 106 < lo; omega))).trans hc.r106
  · exact (hf.read (%107) (Or.inl (by change 107 < lo; omega))).trans hc.r107
  · exact (hf.read (%108) (Or.inl (by change 108 < lo; omega))).trans hc.r108
  · exact (hf.read (%109) (Or.inl (by change 109 < lo; omega))).trans hc.r109
  · exact (hf.read (%127) (Or.inl (by change 127 < lo; omega))).trans hc.r127
  · exact (hf.read (%145) (Or.inl (by change 145 < lo; omega))).trans hc.r145

end Agave.Ed25519.Tables.Avx2Constructor.CacheScale
