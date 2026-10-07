import SSA.Projects.Agave.Ed25519.Proof.Verifier.Bridge.ColdInputMemory
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.OutputMemory

namespace Agave.Ed25519.Verifier.Execution.ColdInput
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- The single public-key decoder invocation, its ordinary exact caller frame,
and the Rust Option result. No key-constructor or verifier execution is assumed. -/
structure DecoderResult (kp : Key.Primitives) (decode : Bytes32 → Option ValidPoint)
    (initial decoded : GlobalState) (i : Invocation) (a : Bytes32) : Prop where
  call : kp.decompress
    (Key.args (Key.optionSlot (Wrapper.allocated initial)) i.publicKey)
    ((Wrapper.allocated initial).alloca 168) = .value (.nil, decoded)
  wellFormed : decoded.WF
  callerBlocks : CallerBlocks (Wrapper.allocated initial) decoded
  optionRange : SmallRange decoded.mem (Key.optionSlot (Wrapper.allocated initial)) 168
  result : match decode a with
    | none => decoded.mem.readAt (Key.optionSlot (Wrapper.allocated initial)) 64 = 0
    | some A => decoded.mem.readAt (Key.optionSlot (Wrapper.allocated initial)) 64 = 1 ∧
        Dalek.ReadBytes decoded ((Key.optionSlot (Wrapper.allocated initial)).add 8#64)
          160 A.bytes

private theorem pack_pair (a b : BitVec 64) : BitVec.packLanes #v[a, b] = b ++ a := by
  change (0#0 ++ b) ++ a = b ++ a
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero]
  grind only

private theorem payload_slices (P : Key.PointWords) :
    P.bytes.extractLsb' 0 128 = BitVec.packLanes #v[P.X 0, P.X 1] ∧
    P.bytes.extractLsb' 64 128 = BitVec.packLanes #v[P.X 1, P.X 2] ∧
    P.bytes.extractLsb' 192 128 = BitVec.packLanes #v[P.X 3, P.X 4] ∧
    P.bytes.extractLsb' 960 128 = BitVec.packLanes #v[P.T 0, P.T 1] ∧
    P.bytes.extractLsb' 1024 128 = BitVec.packLanes #v[P.T 1, P.T 2] ∧
    P.bytes.extractLsb' 1152 128 = BitVec.packLanes #v[P.T 3, P.T 4] ∧
    P.bytes.extractLsb' 320 320 = Key.coordinatePayload P.Y ∧
    P.bytes.extractLsb' 640 320 = Key.coordinatePayload P.Z := by
  repeat' constructor
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [Key.PointWords.bytes, Key.pointPayload, Key.coordinatePayload,
      BitVec.getLsbD_extractLsb', Memory.getLsbD_spliceBits,
      pack_pair, BitVec.getLsbD_append, BitVec.getLsbD_zero]
    grind only

theorem decoded_coordinates (s : GlobalState) (out : Pointer) (A : ValidPoint)
    (hp : Dalek.ReadBytes s (out.add 8#64) 160 A.bytes) :
    Key.NegationReads s out A.words.X A.words.T ∧
    s.mem.readAt (out.add 48#64) 320 = Key.coordinatePayload A.words.Y ∧
    s.mem.readAt (out.add 88#64) 320 = Key.coordinatePayload A.words.Z := by
  obtain ⟨hx0, hx8, hx24, ht0, ht8, ht24, hy, hz⟩ := payload_slices A.words
  have hc := Encoding.Decompress.Execution.Decode.keyChunks_of_payload s out A.bytes hp
  have hY := Encoding.Decompress.Execution.Decode.payload_part s out A.bytes hp
    40 320 (by decide) (by decide)
  have hZ := Encoding.Decompress.Execution.Decode.payload_part s out A.bytes hp
    80 320 (by decide) (by decide)
  exact ⟨⟨hc.x0.trans hx0, hc.x8.trans hx8, hc.x24.trans hx24,
    hc.t0.trans ht0, hc.t8.trans ht8, hc.t24.trans ht24⟩, hY.trans hy, hZ.trans hz⟩

theorem decoderCall (hwf : initial.WF)
    (hkey : SmallRange initial.mem i.publicKey 32)
    (hd : DecoderResult kp decode initial decoded i a) :
    ∃ x t,
      Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
        i.publicKey x t (decode a).isSome ∧
      ∀ A, decode a = some A → x = A.words.X ∧ t = A.words.T ∧
        decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 48#64) 320 =
          Key.coordinatePayload A.words.Y ∧
        decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 88#64) 320 =
          Key.coordinatePayload A.words.Z := by
  have hresult := hd.callerBlocks.range (allocated_wf hwf) (allocated_result hwf)
  cases ha : decode a with
  | none =>
    refine ⟨fun _ => 0, fun _ => 0, ⟨hd.call, hd.optionRange, ?_, hresult, ?_⟩, ?_⟩
    · simpa [ha] using hd.result
    · simp
    · intro A hA; simp at hA
  | some A =>
    have hr := hd.result
    rw [ha] at hr
    obtain ⟨hn, hy, hz⟩ := decoded_coordinates _ _ A hr.2
    refine ⟨A.words.X, A.words.T, ⟨hd.call, hd.optionRange, ?_, hresult, ?_⟩, ?_⟩
    · simpa [ha] using hr.1
    · intro _
      refine ⟨hd.callerBlocks.range (allocated_wf hwf)
        ((allocated_blocks initial).range hwf hkey), ?_,
        fresh_ne hwf hkey (result_fresh initial), hn⟩
      simp [Wrapper.keyResultSlot, Key.optionSlot, Wrapper.allocated,
        GlobalState.alloca, GlobalState.allocaPtr]
    · intro B hB
      have hBA : B = A := Option.some.inj hB.symm
      subst B
      exact ⟨rfl, rfl, hy, hz⟩

/-- A contextual decoder contract supplies the entire observation package
except exact allocation preservation. That stronger frame remains explicit. -/
theorem decoderResult_of_contract
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (hdecode : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
      (ValidPoint.layout timesEight) (ValidPoint.shared decode))
    (initial : GlobalState) (i : Invocation) (a : Bytes32)
    (hwf : initial.WF) (hkey : Dalek.ReadBytes initial i.publicKey 32 a)
    (hready : Encoding.Decompress.Execution.Ready ddg dsg initial)
    (hframe : ∀ decoded,
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
        (Key.args (Key.optionSlot (Wrapper.allocated initial)) i.publicKey)
        ((Wrapper.allocated initial).alloca 168) = .value (.nil, decoded) →
      CallerBlocks (Wrapper.allocated initial) decoded) :
    ∃ decoded, DecoderResult (LinkedColdLeaves.keyPrimitives ddg dsg)
      decode initial decoded i a := by
  have hw := allocated_wf hwf
  have hk := (allocated_blocks initial).readBytes hwf hkey
  have hr := ((hready.alloca hwf 64).alloca hwf.alloca 200).alloca hwf.alloca.alloca 192
  have hout := fresh_range (Wrapper.allocated initial) 168 (by decide)
  have hin : Dalek.ReadBytes ((Wrapper.allocated initial).alloca 168) i.publicKey 32 a :=
    ⟨Dalek.smallRange_alloca _ hw hk.1 _, (MemoryState.readAt_alloca hw hk.1.fits).trans hk.2⟩
  obtain ⟨decoded, hc, hf, ho⟩ := hdecode _ _ _ a hw.alloca (hr.alloca hw 168) hout hin
    (Range.disjoint_of_id_ne (GlobalState.ne_allocaPtr_of_fits hw hk.1.fits).symm)
  exact ⟨decoded, hc, hf.wellFormed, hframe decoded hc, hf.live _ _ hout, by
    cases ha : decode a <;> simpa [ValidPoint.shared, ValidPoint.layout, Key.optionSlot, ha] using ho⟩

end Agave.Ed25519.Verifier.Execution.ColdInput
