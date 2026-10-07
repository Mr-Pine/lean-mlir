import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialProjectiveRefinement
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialValidPoint

/-! The complete serial ladder suffix: real completed-to-projective calls,
the 120-byte copy, the zero-index branch, and the actual final return block. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (readPoint)
open Verifier.Execution

theorem projectiveRoundState_readFrame (s : GlobalState)
    (temporary completed projective q : Pointer) (bits : Nat)
    (ht : temporary.id ≠ q.id) (hp : projective.id ≠ q.id) :
    (projectiveRoundState s temporary completed projective).mem.readAt q bits =
      s.mem.readAt q bits := by
  unfold projectiveRoundState
  rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hp)]
  simp only [projectiveState, fieldState]
  rw [SerialPoint.Execution.readAt_storeLimbs_ne _ _ _ _ _ (by simpa using ht),
    SerialPoint.Execution.readAt_storeLimbs_ne _ _ _ _ _ (by simpa using ht),
    SerialPoint.Execution.readAt_storeLimbs_ne _ _ _ _ _ ht]

/-- The result bytes are exactly the verifier ValidPoint encoding of the
completed accumulator's group value. All other caller blocks are preserved,
apart from the designated output; scratch blocks are explicitly identified. -/
theorem serial_suffix_run_validPoint (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (hsquare : p.call8 = Encoding.Decompress.Execution.Pow2k.program.call)
    (E : ⟪serialKernel.Γ⟫) (out temporary completed projective : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : Buffer s.mem out 160)
    (ht : Buffer s.mem temporary 120) (hc : Buffer s.mem completed 160)
    (hp : Buffer s.mem projective 120) (hpt : projective.id ≠ temporary.id)
    (htc : temporary.id ≠ completed.id) (hop : out.id ≠ projective.id)
    (harg : E.read (%arg0) = .value out)
    (hbound : SerialPoint.PointBounded (readPoint s completed)) (V : GroupPoint)
    (hpoint : Tables.Represents (SerialPoint.pointValue
      (SerialPoint.asExtended (readPoint s completed))) V) :
    ∃ (P : ValidPoint) (final : GlobalState),
      (serialKernel p g).runFrom
        (projectiveInput (serialReturnInput E projective) temporary completed projective 0) 28 s =
          .value (.nil, final) ∧ final.WF ∧ P.curve = V ∧
      Dalek.ReadBytes final out 160 P.bytes ∧
      (∀ q bits, temporary.id ≠ q.id → projective.id ≠ q.id →
        (Range.of q bits).Disjoint (Range.of out 1280) →
        final.mem.readAt q bits = s.mem.readAt q bits) := by
  let R := projectiveResult (serialReturnInput E projective) temporary completed projective 0
  let next := projectiveRoundState s temporary completed projective
  obtain ⟨hprefix, hwf', htight, hrep⟩ := serial_projective_run_represents p g hfield
    (serialReturnInput E projective) temporary completed projective 0 s hwf ht hc hp hpt htc hbound V hpoint
  have hout' : Buffer next.mem out 160 := projectiveRoundState_buffer hout _ _ _
  have hp' : Buffer next.mem projective 120 := projectiveRoundState_buffer hp _ _ _
  have harg' : R.read (%arg0) = .value out := by
    simpa [R, projectiveResult, projectiveInput, serialReturnInput, mlir_env] using harg
  have h0 : R.read (%0) = .value 1#32 := by
    simp [R, projectiveResult, projectiveInput, serialReturnInput, mlir_env]
  have h20 : R.read (%20) = .value 40#64 := by
    simp [R, projectiveResult, projectiveInput, serialReturnInput, mlir_env]
  have h22 : R.read (%22) = .value 80#64 := by
    simp [R, projectiveResult, projectiveInput, serialReturnInput, mlir_env]
  have h23 : R.read (%23) = .value 120#64 := by
    simp [R, projectiveResult, projectiveInput, serialReturnInput, mlir_env]
  have h38 : R.read (%38) = .value projective := by
    simp [R, projectiveResult, projectiveInput, serialReturnInput, mlir_env]
  have h107 : R.read (%107) = .value (projective.add 40) := by
    simp [R, projectiveResult, projectiveInput, serialReturnInput, mlir_env]
  have h108 : R.read (%108) = .value (projective.add 80) := by
    simp [R, projectiveResult, projectiveInput, serialReturnInput, mlir_env]
  have hR : serialReturnInput R projective = R := by
    unfold serialReturnInput
    rw [Env.write_of_read R (%0) h0, Env.write_of_read R (%20) h20,
      Env.write_of_read R (%22) h22, Env.write_of_read R (%23) h23,
      Env.write_of_read R (%38) h38, Env.write_of_read R (%107) h107,
      Env.write_of_read R (%108) h108]
  obtain ⟨P, hrun, hframe, hcurve, hbytes⟩ := serial_return_run_validPoint p g hfield hsquare
    R out projective next hwf' hout' hp' hop harg'
    (SerialPoint.pointTight_bounded _ htight) V hrep
  rw [hR] at hrun
  refine ⟨P, _, ?_, hframe.wellFormed, hcurve, hbytes, ?_⟩
  · exact hprefix.trans hrun
  · intro q bits htq hpq hd
    exact (hframe.readFrame q bits hd).trans
      (projectiveRoundState_readFrame s temporary completed projective q bits htq hpq)

end Agave.Ed25519.DoubleBase.RIR
