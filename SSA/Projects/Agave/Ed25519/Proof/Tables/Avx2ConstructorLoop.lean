import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorStep

/-! All seven actual constructor iterations, preserving the completed records. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Loop
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2FieldMul.Execution (readBlocks)
open Avx2PointDouble (doublePoint)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open State (Slots)
open Arithmetic (entries)
open LoopStore (record)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem loop_run (slots : Slots) (table : Pointer) (P : Point) (hP : pointReduced P)
    (fuel k : Nat) (hcount : k+fuel = 7) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (hr : LoopRegisters.Ready slots table E)
    (hc : k < 7 → E.read (%803) = .value (BitVec.ofNat 64 k))
    (hs : State.Ready slots table s)
    (hd : readBlocks s.mem (slots 7) = packPoint (doublePoint P))
    (he : ∀ j : Fin 8, j.val ≤ k →
      readBlocks s.mem (record table j.val) = packPoint (entries P j.val)) :
    ∃ F t,
      (kernel Double.actual).runFrom E (if k = 7 then 1 else 2) s =
        (kernel Double.actual).runFrom F 1 t ∧
      RegisterFrame 803 kernel.Γ.n E F ∧ State.Frame slots table s t ∧
      LoopRegisters.Ready slots table F ∧ State.Ready slots table t ∧
      ∀ j : Fin 8, readBlocks t.mem (record table j.val) = packPoint (entries P j.val) := by
  induction fuel generalizing k E s with
  | zero =>
      have hk : k = 7 := by omega
      subst k
      exact ⟨E,s,by simp,RegisterFrame.refl _ _ _,State.Frame.refl hs.wf,hr,hs,
        fun j => he j (by have := j.isLt; omega)⟩
  | succ fuel ih =>
      have hk : k < 7 := by omega
      obtain ⟨M,u,hblock,hfr,hfm,hrm,hsm,hdm,hem,hcm⟩ :=
        Step.block_step slots table P hP ⟨k,hk⟩ E s hr (hc hk) hs hd he
      obtain ⟨F,t,hrest,hfr',hfm',hrf,hsf,hef⟩ := ih (k+1) (by omega) M u hrm
        (fun hn => hcm (show k < 6 by omega)) hsm hdm hem
      refine ⟨F,t,?_,hfr.trans hfr',hfm.trans hfm',hrf,hsf,hef⟩
      have heq : (if k = 6 then (1 : Fin 3) else 2) = if k+1 = 7 then 1 else 2 := by
        by_cases h : k = 6 <;> simp [h, show k+1 = 7 ↔ k=6 by omega]
      rw [show (if k = 7 then (1 : Fin 3) else 2) = 2 by simp [show k ≠ 7 by omega],
        Func.runFrom_eq,
        show (kernel Double.actual).blocks 2 = kernel.bb2 Double.actual from rfl,
        hblock]
      change (kernel Double.actual).runFrom M (if k = 6 then 1 else 2) u = _
      rw [heq]
      exact hrest

end Agave.Ed25519.Tables.Avx2Constructor.Loop
