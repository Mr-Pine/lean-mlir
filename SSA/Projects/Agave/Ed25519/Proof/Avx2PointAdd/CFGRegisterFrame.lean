import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGPrepare
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGNegate
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGDifference
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGFactors
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGLoads
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGTable
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame

namespace Agave.Ed25519.Avx2PointAdd.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR Phases
open DoubleBase.ExecutionAvx2 (RegisterFrame)

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

theorem row22_frame (E : ⟪avx2Kernel.Γ⟫) (table : Pointer) (index : Fin 64) :
    RegisterFrame 529 530 E (row22Env E table index) := by
  unfold row22Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem cached22_frame (E : ⟪avx2Kernel.Γ⟫) (r : Pointer) (v : PointBlocks) :
    RegisterFrame 530 539 E (cached22Env E r v) := by
  unfold cached22Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem abdc22_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 583 587 E (abdc22Env E) := by
  unfold abdc22Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load22_product4_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 579 583 E (load22_product4Env E v) := by
  unfold load22_product4Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load22_product1_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 587 588 E (load22_product1Env E v) := by
  unfold load22_product1Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load22_result_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 619 624 E (load22_resultEnv E v) := by
  unfold load22_resultEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem row25_frame (E : ⟪avx2Kernel.Γ⟫) (table : Pointer) (index : Fin 64) :
    RegisterFrame 627 628 E (row25Env E table index) := by
  unfold row25Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem abdc25_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 657 661 E (abdc25Env E) := by
  unfold abdc25Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load25_product4_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 653 657 E (load25_product4Env E v) := by
  unfold load25_product4Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load25_product1_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 661 662 E (load25_product1Env E v) := by
  unfold load25_product1Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load25_result_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 693 698 E (load25_resultEnv E v) := by
  unfold load25_resultEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem row29_frame (E : ⟪avx2Kernel.Γ⟫) (table : Pointer) (index : Fin 64) :
    RegisterFrame 710 711 E (row29Env E table index) := by
  unfold row29Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem cached29_frame (E : ⟪avx2Kernel.Γ⟫) (r : Pointer) (v : PointBlocks) :
    RegisterFrame 711 720 E (cached29Env E r v) := by
  unfold cached29Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem abdc29_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 764 768 E (abdc29Env E) := by
  unfold abdc29Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load29_product4_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 760 764 E (load29_product4Env E v) := by
  unfold load29_product4Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load29_product1_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 768 769 E (load29_product1Env E v) := by
  unfold load29_product1Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load29_result_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 800 805 E (load29_resultEnv E v) := by
  unfold load29_resultEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem row33_frame (E : ⟪avx2Kernel.Γ⟫) (table : Pointer) (index : Fin 64) :
    RegisterFrame 815 816 E (row33Env E table index) := by
  unfold row33Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem abdc33_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 845 849 E (abdc33Env E) := by
  unfold abdc33Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load33_product4_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 841 845 E (load33_product4Env E v) := by
  unfold load33_product4Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load33_product1_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 849 850 E (load33_product1Env E v) := by
  unfold load33_product1Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem load33_result_frame (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 881 886 E (load33_resultEnv E v) := by
  unfold load33_resultEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem prepare22_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 554 579 E (prepare22Env E) := by
  unfold prepare22Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem difference22_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 588 609 E (difference22Env E) := by
  unfold difference22Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem adda22_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 609 614 E (adda22Env E) := by
  unfold adda22Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem cbcb22_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 614 619 E (cbcb22Env E) := by
  unfold cbcb22Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem negate22_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 539 554 E (negate22Env E) := by
  unfold negate22Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem prepare25_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 628 653 E (prepare25Env E) := by
  unfold prepare25Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem difference25_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 662 683 E (difference25Env E) := by
  unfold difference25Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem adda25_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 683 688 E (adda25Env E) := by
  unfold adda25Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem cbcb25_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 688 693 E (cbcb25Env E) := by
  unfold cbcb25Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem prepare29_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 735 760 E (prepare29Env E) := by
  unfold prepare29Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem difference29_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 769 790 E (difference29Env E) := by
  unfold difference29Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem adda29_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 790 795 E (adda29Env E) := by
  unfold adda29Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem cbcb29_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 795 800 E (cbcb29Env E) := by
  unfold cbcb29Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem negate29_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 720 735 E (negate29Env E) := by
  unfold negate29Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem prepare33_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 816 841 E (prepare33Env E) := by
  unfold prepare33Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem difference33_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 850 871 E (difference33Env E) := by
  unfold difference33Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem adda33_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 871 876 E (adda33Env E) := by
  unfold adda33Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem cbcb33_frame (E : ⟪avx2Kernel.Γ⟫) :
    RegisterFrame 876 881 E (cbcb33Env E) := by
  unfold cbcb33Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _


end Agave.Ed25519.Avx2PointAdd.CFG
