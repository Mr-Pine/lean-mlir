import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorStep
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorLoopRegisters

namespace Agave.Ed25519.Tables.SerialConstructorLoop
open LeanMLIR.RIR
open DoubleBase.RIR (PrefixEq completedState completedState_writesOnly)
open DoubleBase.SerialContracts (readPoint readCached)
open SerialConstructorState (Slots Frame)
open SerialConstructorStep (record nextState)
open SerialConstructorArithmetic (entries)
open SerialConstructorLoopWrapper
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- One original loop block, including the actual conditional successor. -/
theorem block_step (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (hp : p.call2 = SerialPoint.cached_add.call)
    (slots : Slots) (table : Pointer) (k : Fin 7)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (A : SerialPoint.LimbPoint)
    (hA : SerialPoint.PointTight A)
    (hr : SerialConstructorLoopRegisters.Ready g slots table E)
    (hc : E.read (%140) = .value (BitVec.ofNat 64 k.val))
    (hs : SerialConstructorState.Ready g slots table s)
    (hd : readPoint s (slots 5) = SerialConstructorArithmetic.double A)
    (he : ∀ j : Fin 8, j.val ≤ k.val → readCached s (record table j.val) = entries A j.val) :
    ∃ F t,
      (SerialConstructor.kernel.bb2 (SerialCacheExecution.primitives p)).run
        SerialConstructor.kernel.blockParams E s =
        .value ((F, .inr (if k.val = 6 then 1 else 2)), t) ∧
      PrefixEq E F 140 ∧ Frame slots table s t ∧
      SerialConstructorLoopRegisters.Ready g slots table F ∧
      SerialConstructorState.Ready g slots table t ∧
      readPoint t (slots 5) = SerialConstructorArithmetic.double A ∧
      (∀ j : Fin 8, j.val ≤ k.val+1 → readCached t (record table j.val) = entries A j.val) ∧
      (k.val < 6 → F.read (%140) = .value (BitVec.ofNat 64 (k.val+1))) := by
  obtain ⟨u, hcall, hu, hru, hframe, hrt, hdt, het⟩ :=
    SerialConstructorStep.next_state g slots table k s A hA hs hd he
  have hcall' : p.call2 (.cons (.value (slots 2)) (.cons (.value (slots 5))
      (.cons (.value (record table k.val)) .nil))) s = .value (.nil,u) := by
    rw [hp]; exact hcall
  let E₁ := prefixResult E (slots 2) (slots 3) (slots 5) table k
  let v := completedState u (slots 3) (slots 2)
  have hprefix := prefix_run p E (slots 2) (slots 3) (slots 5) table k s u hs.tableBuffer
    hcall' hru.wf (hru.point 3 (by decide)) (hru.point 2 (by decide))
  rw [hr.prefix k hc] at hprefix
  have hf₁ : PrefixEq E E₁ 141 := by
    have h := prefix_preserves E (slots 2) (slots 3) (slots 5) table k
    rwa [hr.prefix k hc] at h
  have hr₁ := hr.preserve (hf₁.mono (by decide))
  have hv := completedState_writesOnly u (slots 3) (slots 2) hru.wf (hru.point 3 (by decide))
  have hrv := hru.preserve (Frame.slot 3 hv)
  obtain ⟨E₂, hcache, hf₂⟩ := SerialCacheExecution.successorBody_run p g E₁ v (slots 4) (slots 3)
    hrv.wf (hrv.point 4 (by decide)) (hrv.point 3 (by decide)) hrv.globalReady.buffer
    (hs.separate 4 3 (by decide)) (hrv.globalSeparate 4) hr₁.cache hr₁.constants
  let w := SerialCacheExecution.cacheState v (slots 4) (slots 3) g.address0
  have hw := SerialCacheExecution.cacheState_writesOnly v (slots 4) (slots 3)
    g.address0 hrv.wf (hrv.point 4 (by decide))
  have hrw := hrv.preserve (Frame.slot 4 hw)
  have hr₂ := hr₁.preserve (hf₂.mono (by decide))
  have hnext : E₂.read (%141) = .value (BitVec.ofNat 64 (k.val+1)) := by
    rw [hf₂.read _ (by intro i ht he; cases he; decide)]
    simp [E₁, prefixResult, mlir_env]
  have htail := tail_body (SerialCacheExecution.primitives p) E₂ table (slots 4) k w
    hrw.tableBuffer (hrw.point 4 (by decide)) (hs.separateTable 4).symm
  rw [hr₂.tail k hnext] at htail
  let E₃ := tailResult E₂ table (slots 4) k
  let F := if k.val = 6 then E₃ else E₃[%140 := .value (BitVec.ofNat 64 (k.val+1))]
  have hf₃ : PrefixEq E₂ E₃ 184 := by
    have h := tail_preserves E₂ table (slots 4) k
    rwa [hr₂.tail k hnext] at h
  have hfF : PrefixEq E F 140 := by
    have hf : PrefixEq E E₃ 140 :=
      (hf₁.mono (by decide)).trans ((hf₂.mono (by decide)).trans (hf₃.mono (by decide)))
    dsimp only [F]
    split
    · exact hf
    · exact hf.write _ _ (by decide)
  have hbody : List.foldlM Instr.run E
      (SerialConstructor.kernel.bb2 (SerialCacheExecution.primitives p)).body s =
      .value (E₃, nextState g slots table k u) := by
    have hb : (SerialConstructor.kernel.bb2 (SerialCacheExecution.primitives p)).body =
        ((SerialConstructor.kernel.bb2 (SerialCacheExecution.primitives p)).body.take 10) ++
        (SerialCacheExecution.successorBody p ++
          (SerialConstructor.kernel.bb2 (SerialCacheExecution.primitives p)).body.drop 67) := rfl
    rw [hb, List.foldlM_append, EffectM.bind_eq, hprefix, PoisonOr.value_bind]
    change List.foldlM Instr.run E₁ (SerialCacheExecution.successorBody p ++
      (SerialConstructor.kernel.bb2 (SerialCacheExecution.primitives p)).body.drop 67) v = _
    rw [List.foldlM_append, EffectM.bind_eq, hcache, PoisonOr.value_bind]
    change List.foldlM Instr.run E₂
      ((SerialConstructor.kernel.bb2 (SerialCacheExecution.primitives p)).body.drop 67) w = _
    exact htail
  refine ⟨F, nextState g slots table k u, ?_, hfF, hframe, hr.preserve hfF, hrt, hdt, het, ?_⟩
  · rw [BasicBlock.run, EffectM.bind_eq, hbody, PoisonOr.value_bind]
    exact tail_exit (SerialCacheExecution.primitives p) E₂ table (slots 4) k _
  · intro hk
    simp [F, show ¬k.val = 6 by omega, mlir_env]

/-- All seven source iterations, preserving a frame and every completed table record. -/
theorem loop_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (hp : p.call2 = SerialPoint.cached_add.call)
    (slots : Slots) (table : Pointer) (A : SerialPoint.LimbPoint) (hA : SerialPoint.PointTight A)
    (fuel k : Nat) (hcount : k+fuel = 7)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState)
    (hr : SerialConstructorLoopRegisters.Ready g slots table E)
    (hc : k < 7 → E.read (%140) = .value (BitVec.ofNat 64 k))
    (hs : SerialConstructorState.Ready g slots table s)
    (hd : readPoint s (slots 5) = SerialConstructorArithmetic.double A)
    (he : ∀ j : Fin 8, j.val ≤ k → readCached s (record table j.val) = entries A j.val) :
    ∃ F t,
      (SerialConstructor.kernel (SerialCacheExecution.primitives p) g).runFrom E
        (if k = 7 then 1 else 2) s =
      (SerialConstructor.kernel (SerialCacheExecution.primitives p) g).runFrom F 1 t ∧
      PrefixEq E F 140 ∧ Frame slots table s t ∧
      SerialConstructorLoopRegisters.Ready g slots table F ∧
      SerialConstructorState.Ready g slots table t ∧
      ∀ j : Fin 8, readCached t (record table j.val) = entries A j.val := by
  induction fuel generalizing k E s with
  | zero =>
      have hk : k = 7 := by omega
      subst k
      exact ⟨E,s,by simp,PrefixEq.refl _ _,Frame.refl hs.wf,hr,hs,
        fun j => he j (by have := j.isLt; omega)⟩
  | succ fuel ih =>
      have hk : k < 7 := by omega
      obtain ⟨M,u,hblock,hfr,hfm,hrm,hsm,hdm,hem,hcm⟩ :=
        block_step p g hp slots table ⟨k,hk⟩ E s A hA hr (hc hk) hs hd he
      obtain ⟨F,t,hrest,hfr',hfm',hrf,hsf,hef⟩ := ih (k+1) (by omega) M u hrm
        (fun hn => hcm (show k < 6 by omega)) hsm hdm hem
      refine ⟨F,t,?_,hfr.trans hfr',hfm.trans hfm',hrf,hsf,hef⟩
      have heq : (if k = 6 then (1 : Fin 3) else 2) = if k+1 = 7 then 1 else 2 := by
        by_cases h : k = 6 <;> simp [h, show k+1 = 7 ↔ k=6 by omega]
      rw [show (if k = 7 then (1 : Fin 3) else 2) = 2 by simp [show k ≠ 7 by omega],
        Func.runFrom_eq,
        show (SerialConstructor.kernel (SerialCacheExecution.primitives p) g).blocks 2 =
          SerialConstructor.kernel.bb2 (SerialCacheExecution.primitives p) from rfl,
        hblock]
      change (SerialConstructor.kernel (SerialCacheExecution.primitives p) g).runFrom M
        (if k = 6 then 1 else 2) u = _
      rw [heq]
      exact hrest

end Agave.Ed25519.Tables.SerialConstructorLoop
