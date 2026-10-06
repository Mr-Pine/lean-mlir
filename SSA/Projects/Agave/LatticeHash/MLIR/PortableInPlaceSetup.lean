import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceInput
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceTransport
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlacePure
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlacePrefixRun
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceValuation
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceTail
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofProof
namespace AgaveLatticeHash.MLIR.PortableInPlace
open LeanMLIR SLLVM Firedancer Blake3Compression
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
theorem input_prefix_run (s : GlobalState) (cvp msg : Pointer)
    (cv : CV Word) (m : State Word) (counter : BitVec 64) (len flags : BitVec 8)
    (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (m i)) :
    StateT.run (input.pre.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value counter, .value len, .value msg, .value cvp]ₕ)) s =
    .value (inputValuation cvp msg cv m counter len flags, s) := by
  exact BlockPrefix.run_of_append_ret input.pre _ _ s
    (input_run s cvp msg cv m counter len flags hcvp hmsg rcv rmsg)


theorem input_comap (cvp msg : Pointer) (cv : CV Word) (m : State Word)
    (counter : BitVec 64) (len flags : BitVec 8) :
    (inputValuation cvp msg cv m counter len flags).comap rename =
    PortableXof.inputValuation msg cvp msg cv m counter len flags := by
  change (inputValuation cvp msg cv m counter len flags).comap (fun _ v => vars[v]) = _
  rw [valuation_comap_vars]
  rfl


theorem rounds_pure : rounds.pre.Pure := round_certificate.pure PortableXof.rounds_pure


theorem result_mapped (i : Fin 16) : finalMap (PortableXof.resultVar i) = resultVar i := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> rfl


theorem tail_env_of_context (cvp msg : Pointer) (cv : CV Word) (m : State Word)
    (counter : BitVec 64) (len flags : BitVec 8) (W : rounds.middle.Valuation)
    (hc : W.comap rounds.pre.contextHom = inputValuation cvp msg cv m counter len flags) :
    TailEnv W cvp := by
  constructor
  · have h := congrArg (fun U : input.middle.Valuation => U (t := SLLVM.Ty.ptr) ⟨78, rfl⟩) hc
    have hv : rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨78, rfl⟩ = ⟨862, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨78, rfl⟩) = _ at h
    rw [hv] at h
    change W ⟨862, rfl⟩ = PoisonOr.value cvp at h
    simpa only [show cvp.withOffset 0 = cvp by cases cvp; simp [Pointer.withOffset]] using h
  · have h := congrArg (fun U : input.middle.Valuation => U (t := SLLVM.Ty.ptr) ⟨18, rfl⟩) hc
    have hv : rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨18, rfl⟩ = ⟨802, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨18, rfl⟩) = _ at h
    rw [hv] at h
    change W ⟨802, rfl⟩ = PoisonOr.value (cvp.withOffset 4) at h
    exact h
  · have h := congrArg (fun U : input.middle.Valuation => U (t := SLLVM.Ty.ptr) ⟨16, rfl⟩) hc
    have hv : rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨16, rfl⟩ = ⟨800, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨16, rfl⟩) = _ at h
    rw [hv] at h
    change W ⟨800, rfl⟩ = PoisonOr.value (cvp.withOffset 8) at h
    exact h
  · have h := congrArg (fun U : input.middle.Valuation => U (t := SLLVM.Ty.ptr) ⟨14, rfl⟩) hc
    have hv : rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨14, rfl⟩ = ⟨798, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨14, rfl⟩) = _ at h
    rw [hv] at h
    change W ⟨798, rfl⟩ = PoisonOr.value (cvp.withOffset 12) at h
    exact h
  · have h := congrArg (fun U : input.middle.Valuation => U (t := SLLVM.Ty.ptr) ⟨12, rfl⟩) hc
    have hv : rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨12, rfl⟩ = ⟨796, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨12, rfl⟩) = _ at h
    rw [hv] at h
    change W ⟨796, rfl⟩ = PoisonOr.value (cvp.withOffset 16) at h
    exact h
  · have h := congrArg (fun U : input.middle.Valuation => U (t := SLLVM.Ty.ptr) ⟨10, rfl⟩) hc
    have hv : rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨10, rfl⟩ = ⟨794, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨10, rfl⟩) = _ at h
    rw [hv] at h
    change W ⟨794, rfl⟩ = PoisonOr.value (cvp.withOffset 20) at h
    exact h
  · have h := congrArg (fun U : input.middle.Valuation => U (t := SLLVM.Ty.ptr) ⟨8, rfl⟩) hc
    have hv : rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨8, rfl⟩ = ⟨792, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨8, rfl⟩) = _ at h
    rw [hv] at h
    change W ⟨792, rfl⟩ = PoisonOr.value (cvp.withOffset 24) at h
    exact h
  · have h := congrArg (fun U : input.middle.Valuation => U (t := SLLVM.Ty.ptr) ⟨6, rfl⟩) hc
    have hv : rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨6, rfl⟩ = ⟨790, rfl⟩ := by
      apply Subtype.ext
      rw [BlockPrefix.contextHom_val]
      rfl
    change W (rounds.pre.contextHom (t := SLLVM.Ty.ptr) ⟨6, rfl⟩) = _ at h
    rw [hv] at h
    change W ⟨790, rfl⟩ = PoisonOr.value (cvp.withOffset 28) at h
    exact h

end AgaveLatticeHash.MLIR.PortableInPlace
