import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLadderSteps

/-! One complete iteration of the actual serial CFG. Both signed switches,
zero cases, finite table guards, arithmetic calls and projective copy execute
from the source NAF bytes; the resulting group invariant is preserved. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (readPoint readProjective)
set_option maxRecDepth 10000

variable {p : SerialCFG.Primitives} {g : SerialCFG.Globals} {slots : Fin 7 → Pointer}
  {tableA tableB da db : Pointer} {a b : Nat} {A B V : GroupPoint}
  {E : ⟪serialKernel.Γ⟫} {s : GlobalState} {i : Fin 256}

theorem serial_ladder_double_A (hh : SerialLadderHelpers p)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialProjectiveAt slots s V) :
    ∃ E' s', (serialKernel p g).runFrom E 18 s = (serialKernel p g).runFrom E' 26 s' ∧
      SerialLadderRegisters slots tableA tableB da db E' ∧
      E'.read (%131) = .value (BitVec.ofNat 64 i.val) ∧
      SerialLadderMemory slots tableA tableB da db a b A B s' ∧
      SerialScratchFrame slots s s' ∧
      SerialCompletedAt slots s' ((V + V) + nafDigits 5 a i.val • A) ∧ E'.args = E.args := by
  have hc : Buffer s.mem (slots 5) 160 := by simpa [serialScratchBytes] using hm.scratch 5
  have hp : Buffer s.mem (slots 6) 120 := by simpa [serialScratchBytes] using hm.scratch 6
  obtain ⟨sd, hd, hframe, hread, hbound⟩ := serial_dispatchA_naf p g hh.double E da (slots 5)
    (slots 6) a i s hm.wellFormed hm.digitsA hc hp
    (Range.disjoint_of_id_ne (hm.separate 5 6 (by decide)))
    (hm.separateDigitsA 5).symm hP.tight (hm.readA i)
  rw [serialDispatchAInput_of_registers hr i hi] at hd
  let R := serialDispatchAResult E da (slots 5) (slots 6) i (Execution.nafByte 5 a i.val)
  have hf := SerialScratchFrame.of_writesOnly 5 hframe
  have he := serialDispatchAResult_frame hr i hi (Execution.nafByte 5 a i.val)
  have hr' : SerialLadderRegisters slots tableA tableB da db R := hr.of_frame (he.weaken_serial (by decide))
  have hi' : R.read (%131) = .value (BitVec.ofNat 64 i.val) :=
    (he.read (%131) (by intro j ht heq; cases heq; decide)).trans hi
  have hm' := hm.preserve hf
  have hp' : SerialCompletedAt slots sd (V + V) := by
    refine ⟨hbound, ?_⟩
    rw [hread]
    exact doubleCompleted_projective_represents _ V hP.tight hP.represents
  have hbyte : R.read (%133) = .value (Execution.nafByte 5 a i.val) := by
    simp [R, serialDispatchAResult, mlir_env]
  by_cases hn : nafDigits 5 a i.val < 0
  · obtain ⟨E', s', hrun, hr'', hi'', hm'', hf', hp'', hargs⟩ :=
      serial_ladder_cached_sub hh hr' hi' hm' hp' hbyte hn
    refine ⟨E', s', ?_, hr'', hi'', hm'', hf.trans hf', hp'', hargs.trans he.1⟩
    simp only [hn, ite_true] at hd
    exact hd.trans hrun
  · by_cases hz : nafDigits 5 a i.val = 0
    · refine ⟨R, sd, ?_, hr', hi', hm', hf, ?_, he.1⟩
      · simpa [hn, hz] using hd
      · simpa only [hz, zero_zsmul, add_zero] using hp'
    · obtain ⟨E', s', hrun, hr'', hi'', hm'', hf', hp'', hargs⟩ :=
        serial_ladder_cached_add hh hr' hi' hm' hp' hbyte (by omega)
      refine ⟨E', s', ?_, hr'', hi'', hm'', hf.trans hf', hp'', hargs.trans he.1⟩
      simp only [hn, hz, ite_false] at hd
      exact hd.trans hrun

theorem serial_ladder_B (hh : SerialLadderHelpers p)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialCompletedAt slots s V) :
    ∃ E' s', (serialKernel p g).runFrom E 26 s = (serialKernel p g).runFrom E' 28 s' ∧
      SerialLadderRegisters slots tableA tableB da db E' ∧
      E'.read (%131) = .value (BitVec.ofNat 64 i.val) ∧
      SerialLadderMemory slots tableA tableB da db a b A B s' ∧
      SerialScratchFrame slots s s' ∧
      SerialCompletedAt slots s' (V + nafDigits 8 b i.val • B) ∧ E'.args = E.args := by
  have hd := serial_dispatchB_naf p g E db b i s hm.digitsB (hm.readB i)
  rw [serialDispatchBInput_of_registers hr i hi] at hd
  let R := serialDispatchBResult E db i (Execution.nafByte 8 b i.val)
  have he := serialDispatchBResult_frame hr i hi (Execution.nafByte 8 b i.val)
  have hr' : SerialLadderRegisters slots tableA tableB da db R := hr.of_frame (he.weaken_serial (by decide))
  have hi' : R.read (%131) = .value (BitVec.ofNat 64 i.val) :=
    (he.read (%131) (by intro j ht heq; cases heq; decide)).trans hi
  have hbyte : R.read (%145) = .value (Execution.nafByte 8 b i.val) := by
    simp [R, serialDispatchBResult, mlir_env]
  by_cases hn : nafDigits 8 b i.val < 0
  · obtain ⟨E', s', hrun, hr'', hi'', hm'', hf, hp'', hargs⟩ :=
      serial_ladder_affine_sub hh hr' hi' hm hP hbyte hn
    refine ⟨E', s', ?_, hr'', hi'', hm'', hf, hp'', hargs.trans he.1⟩
    simp only [hn, ite_true] at hd
    exact hd.trans hrun
  · by_cases hz : nafDigits 8 b i.val = 0
    · refine ⟨R, s, ?_, hr', hi', hm, SerialScratchFrame.refl hm.wellFormed, ?_, he.1⟩
      · simpa [hn, hz] using hd
      · simpa only [hz, zero_zsmul, add_zero] using hP
    · obtain ⟨E', s', hrun, hr'', hi'', hm'', hf, hp'', hargs⟩ :=
        serial_ladder_affine_add hh hr' hi' hm hP hbyte (by omega)
      refine ⟨E', s', ?_, hr'', hi'', hm'', hf, hp'', hargs.trans he.1⟩
      simp only [hn, hz, ite_false] at hd
      exact hd.trans hrun

theorem serial_ladder_round (hh : SerialLadderHelpers p)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialProjectiveAt slots s V) :
    ∃ E' s', (serialKernel p g).runFrom E 18 s =
        (serialKernel p g).runFrom E' (if i.val = 0 then 34 else 35) s' ∧
      SerialLadderRegisters slots tableA tableB da db E' ∧
      E'.read (%131) = .value (BitVec.ofNat 64 i.val) ∧
      SerialLadderMemory slots tableA tableB da db a b A B s' ∧
      SerialScratchFrame slots s s' ∧
      SerialProjectiveAt slots s' (groupRound A B V (nafDigits 5 a) (nafDigits 8 b) i.val) ∧ E'.args = E.args := by
  obtain ⟨EA, sa, hA, hrA, hiA, hmA, hfA, hpA, hargsA⟩ := serial_ladder_double_A hh hr hi hm hP
  obtain ⟨EB, sb, hB, hrB, hiB, hmB, hfB, hpB, hargsB⟩ := serial_ladder_B hh hrA hiA hmA hpA
  have ht : Buffer sb.mem (slots 0) 120 := by simpa [serialScratchBytes] using hmB.scratch 0
  have hc : Buffer sb.mem (slots 5) 160 := by simpa [serialScratchBytes] using hmB.scratch 5
  have hp : Buffer sb.mem (slots 6) 120 := by simpa [serialScratchBytes] using hmB.scratch 6
  obtain ⟨hC, _, htight, hrep⟩ := serial_projective_run_represents p g hh.multiply EB
    (slots 0) (slots 5) (slots 6) i sb hmB.wellFormed ht hc hp
    (hmB.separate 6 0 (by decide)) (hmB.separate 0 5 (by decide)) hpB.bounded _ hpB.represents
  rw [projectiveInput_of_registers hrB i hiB] at hC
  have hfC := projectiveRoundState_scratchFrame sb slots hmB.wellFormed
  have he := projectiveResult_frame hrB i hiB
  refine ⟨_, _, hA.trans (hB.trans hC), hrB.of_frame (he.weaken_serial (by decide)),
    (he.read (%131) (by intro j ht heq; cases heq; decide)).trans hiB,
    hmB.preserve hfC, hfA.trans (hfB.trans hfC), ⟨htight, ?_⟩, he.1.trans (hargsB.trans hargsA)⟩
  simpa only [groupRound, two_nsmul] using hrep

end Agave.Ed25519.DoubleBase.RIR
