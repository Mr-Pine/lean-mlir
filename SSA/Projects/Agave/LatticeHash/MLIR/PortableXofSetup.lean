/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofInput
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofCvData
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofInputEquiv
import SSA.Projects.Agave.LatticeHash.MLIR.PrefixIndices
namespace AgaveLatticeHash.MLIR.PortableXof
open LeanMLIR SLLVM Firedancer Blake3Compression
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem input_prefix_run (s : GlobalState) (out cvp msg : Pointer)
    (cv : CV Word) (m : State Word) (counter : BitVec 64) (len flags : BitVec 8)
    (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (m i)) :
    StateT.run (preInput.pre.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ)) s =
    .value (inputValuation out cvp msg cv m counter len flags, s) := by
  have h := input_run s out cvp msg cv m counter len flags hcvp hmsg rcv rmsg
  rw [inputBlock, BlockPrefix.denote_append, bind_pure] at h
  cases hr : StateT.run (preInput.pre.denote (Ctxt.Valuation.ofHVector
    [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ)) s with
  | poison =>
    simp only [EffectM.run_bind, hr, PoisonOr.poison_bind] at h
    exact False.elim (PoisonOr.poison_ne_value _ h)
  | value ws =>
    rcases ws with ⟨W, t⟩
    simp only [EffectM.run_bind, hr, PoisonOr.value_bind, BlockCom.denote_term,
      Terminator.denote_ret, EffectM.run_pure, HVector.map] at h
    have hv := PoisonOr.value_inj.mp h
    cases hv
    rfl

theorem tail_env_of_context (out cvp msg : Pointer) (cv : CV Word) (m : State Word)
    (counter : BitVec 64) (len flags : BitVec 8) (W : preRound.middle.Valuation)
    (hc : W.comap preRound.pre.contextHom = inputValuation out cvp msg cv m counter len flags) :
    TailEnv W out := by
  constructor
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := .ptr) ⟨79, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := .ptr) ⟨79, rfl⟩ = ⟨863, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := .ptr) ⟨79, rfl⟩) = .value out at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨73, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨73, rfl⟩ = ⟨857, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨73, rfl⟩) = .value (4 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨72, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨72, rfl⟩ = ⟨856, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨72, rfl⟩) = .value (8 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨71, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨71, rfl⟩ = ⟨855, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨71, rfl⟩) = .value (12 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨70, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨70, rfl⟩ = ⟨854, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨70, rfl⟩) = .value (16 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨69, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨69, rfl⟩ = ⟨853, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨69, rfl⟩) = .value (20 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨68, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨68, rfl⟩ = ⟨852, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨68, rfl⟩) = .value (24 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨67, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨67, rfl⟩ = ⟨851, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨67, rfl⟩) = .value (28 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨66, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨66, rfl⟩ = ⟨850, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨66, rfl⟩) = .value (32 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨65, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨65, rfl⟩ = ⟨849, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨65, rfl⟩) = .value (36 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨64, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨64, rfl⟩ = ⟨848, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨64, rfl⟩) = .value (40 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨63, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨63, rfl⟩ = ⟨847, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨63, rfl⟩) = .value (44 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨62, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨62, rfl⟩ = ⟨846, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨62, rfl⟩) = .value (48 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨61, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨61, rfl⟩ = ⟨845, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨61, rfl⟩) = .value (52 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨60, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨60, rfl⟩ = ⟨844, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨60, rfl⟩) = .value (56 : BitVec 64) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := (SLLVM.Ty.bitvec 64)) ⟨59, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨59, rfl⟩ = ⟨843, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 64) ⟨59, rfl⟩) = .value (60 : BitVec 64) at h
    rw [hv] at h
    exact h

theorem cv_of_context (out cvp msg : Pointer) (cv : CV Word) (m : State Word)
    (counter : BitVec 64) (len flags : BitVec 8) (W : preRound.middle.Valuation)
    (hc : W.comap preRound.pre.contextHom = inputValuation out cvp msg cv m counter len flags)
    (i : Fin 8) : W (cvVar i) = .value (cv i) := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := SLLVM.Ty.bitvec 32) ⟨19, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨19, rfl⟩ = ⟨803, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨19, rfl⟩) = .value (cv 0) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := SLLVM.Ty.bitvec 32) ⟨17, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨17, rfl⟩ = ⟨801, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨17, rfl⟩) = .value (cv 1) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := SLLVM.Ty.bitvec 32) ⟨15, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨15, rfl⟩ = ⟨799, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨15, rfl⟩) = .value (cv 2) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := SLLVM.Ty.bitvec 32) ⟨13, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨13, rfl⟩ = ⟨797, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨13, rfl⟩) = .value (cv 3) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := SLLVM.Ty.bitvec 32) ⟨11, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨11, rfl⟩ = ⟨795, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨11, rfl⟩) = .value (cv 4) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := SLLVM.Ty.bitvec 32) ⟨9, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨9, rfl⟩ = ⟨793, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨9, rfl⟩) = .value (cv 5) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := SLLVM.Ty.bitvec 32) ⟨7, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨7, rfl⟩ = ⟨791, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨7, rfl⟩) = .value (cv 6) at h
    rw [hv] at h
    exact h
  · have h := congrArg (fun U : preInput.middle.Valuation => U (t := SLLVM.Ty.bitvec 32) ⟨5, rfl⟩) hc
    have hv : preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨5, rfl⟩ = ⟨789, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (preRound.pre.contextHom (t := SLLVM.Ty.bitvec 32) ⟨5, rfl⟩) = .value (cv 7) at h
    rw [hv] at h
    exact h

theorem denote_no_blocks (b : BlockCom Γ Ω [] []) (V : Γ.Valuation) :
    Cfg.denote ⟨b, .nil⟩ V = b.denote V >>= fun _ => pure ([]ₕ : HVector toType ([] : List SLLVM.Ty)) := by
  simp only [Cfg.denote]
  congr 1
  funext z
  obtain ⟨W, r⟩ := z
  cases r with
  | inl r => cases r; rfl
  | inr r => exact r.elim

end AgaveLatticeHash.MLIR.PortableXof
