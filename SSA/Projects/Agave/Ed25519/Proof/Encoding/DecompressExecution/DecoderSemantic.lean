import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderOuterFrame
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressValidPointExecution

/-!
Semantic completion of the checked outer decoder suffixes. The imported RIR
call, including its actual stack erasure, has the mathematical decoder result
once its two finite prefixes satisfy `PrefixBoundary` below. That boundary does
not contain a whole-call equation, a final output observation, a curve-point
representation premise, or a square-root algebra assumption.

The residual work is deliberately visible: total execution of bb0:0--136,
its flag, and (only on success) bb1:0--49 and three exact field reads. Their
private-memory frame and allocator growth are also required. Initialized
globals alone have not yet been proved to imply these prefix facts.

All algebra is already proved by `wordStep1_value`, `pointWords_value`, and
`Valid.decoderCorrect`: square-root correction/parity, encoded sign selection,
zero X and noncanonical Y need no additional premise here.
-/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.Semantic
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open Verifier
open Verifier.Execution

attribute [local irreducible] step1 wordStep1 pointWords Valid.decode wordDecode

/-- Only the public-memory identity and the allocator order of a prefix.
The suffix stores and their output frame are proved, not included here. -/
structure PrefixPublic (entry reached : GlobalState) : Prop where
  memory : reached.mem.eraseFrom entry.alloc.nextFreeBlock = entry.mem
  allocator : entry.alloc.nextFreeBlock ≤ reached.alloc.nextFreeBlock

/-- The only arithmetic observations required at the success cutpoint.
Y is the original parsed limb array; it is not replaced by a canonical value. -/
structure SuccessWords (bytes : Bytes32) (s : GlobalState)
    (d : OuterSuccessData) : Prop where
  x : s.mem.readAt d.point 320 =
    fieldPayload (pointWords bytes (wordStep1 bytes).2).X.limbs
  y : s.mem.readAt d.y 320 =
    fieldPayload (pointWords bytes (wordStep1 bytes).2).Y.limbs
  t : s.mem.readAt (d.point.add 120#64) 320 =
    fieldPayload (pointWords bytes (wordStep1 bytes).2).T.limbs

/-- Exact finite-source obligations. Failure has no success-prefix, coordinate,
or point-payload premise. The zero test is the only required fact about the
possibly noncanonical flag byte. -/
def PrefixBoundary (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry : GlobalState) (bytes : Bytes32) : Prop :=
  ∃ (E : ⟪program.Γ⟫) (s : GlobalState) (flag : BitVec 8),
    outerEntryPrefix (decodePrimitives sg) dg
      (Env.init (program.args (.value out) (.value input)).get) entry = .value (E, s) ∧
    OuterDecisionReady E s out flag ∧
    (flag = 0#8 ↔ (wordStep1 bytes).1 = false) ∧
    (if flag = 0#8 then PrefixPublic entry s else
      ∃ (F : ⟪program.Γ⟫) (t : GlobalState) (d : OuterSuccessData),
        outerSuccessPrefix (decodePrimitives sg) dg (outerSuccessEnv E flag) s =
          .value (F, t) ∧
        OuterSuccessReady F t out d ∧ PrefixPublic entry t ∧
        entry.alloc.nextFreeBlock ≤ d.point.id.id ∧ SuccessWords bytes t d)

private theorem frame_with_allocator (before after later : GlobalState)
    (out : Pointer) (frame : Dalek.OutputFrame before after out 168)
    (halloc : after.alloc.nextFreeBlock ≤ later.alloc.nextFreeBlock) :
    Dalek.OutputFrame before {later with mem := after.mem} out 168 := by
  refine ⟨?_, frame.live, frame.read⟩
  intro k hk
  exact lt_of_lt_of_le (frame.wellFormed k hk) halloc

private theorem call_of_run (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry result : GlobalState)
    (hrun : (program (decodePrimitives sg) dg).runFrom
      (Env.init (program.args (.value out) (.value input)).get) 0 entry =
      .value (.nil, result)) :
    (program (decodePrimitives sg) dg).call (Dalek.args2 out input) entry =
      .value (.nil, {result with mem := result.mem.eraseFrom entry.alloc.nextFreeBlock}) := by
  rw [Func.call_eq_run_bind, Func.run_runFrom_eq]
  change ((program (decodePrimitives sg) dg).runFrom
    (Env.init (program.args (.value out) (.value input)).get) 0 entry >>= _) = _
  rw [hrun]
  rfl

/-- Actual rejection execution, including the public call's stack erasure.
No bytes or coordinate facts are needed on this branch. -/
theorem linked_call_rejection (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry s : GlobalState) (E : ⟪program.Γ⟫)
    (hentry : outerEntryPrefix (decodePrimitives sg) dg
      (Env.init (program.args (.value out) (.value input)).get) entry = .value (E, s))
    (hready : OuterDecisionReady E s out 0#8)
    (hpublic : PrefixPublic entry s) :
    (program (decodePrimitives sg) dg).call (Dalek.args2 out input) entry =
      .value (.nil, {s with mem := (rejectionState entry out).mem}) := by
  have hprefix := Cutpoint.after_segment (program (decodePrimitives sg) dg) 0 0 137
    (Env.init (program.args (.value out) (.value input)).get) E entry s hentry
  rw [Cutpoint.zero] at hprefix
  have hrun : (program (decodePrimitives sg) dg).runFrom
      (Env.init (program.args (.value out) (.value input)).get) 0 entry =
      .value (.nil, rejectionState s out) := by
    rw [hprefix]
    exact rejection_run (decodePrimitives sg) dg E s out hready.outputRegister
      hready.flagRegister hready.zeroRegister hready.tagRegister hready.outputLive
  rw [call_of_run dg sg out input entry _ hrun,
    outerRejectionState_public entry s out hpublic.memory]

/-- Actual success execution into the representation-preserving `ValidPoint`.
The required words are only X/Y/T at bb1:50; Z, payload, tag and all final
memory operations are supplied by the checked original suffix. -/
theorem linked_call_success (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry s t : GlobalState)
    (E F : ⟪program.Γ⟫) (flag : BitVec 8) (d : OuterSuccessData)
    (bytes : Bytes32) (hvalid : (step1 bytes).1 = true)
    (hentry : outerEntryPrefix (decodePrimitives sg) dg
      (Env.init (program.args (.value out) (.value input)).get) entry = .value (E, s))
    (hdecision : OuterDecisionReady E s out flag) (hnonzero : flag ≠ 0#8)
    (hsuccess : outerSuccessPrefix (decodePrimitives sg) dg
      (outerSuccessEnv E flag) s = .value (F, t))
    (hready : OuterSuccessReady F t out d) (hwords : SuccessWords bytes t d)
    (hpublic : PrefixPublic entry t)
    (hprivate : entry.alloc.nextFreeBlock ≤ d.point.id.id) :
    (program (decodePrimitives sg) dg).call (Dalek.args2 out input) entry =
      .value (.nil, {t with mem :=
        (successState entry out (Valid.point bytes hvalid).bytes).mem}) := by
  have hprefix := Cutpoint.after_segment (program (decodePrimitives sg) dg) 0 0 137
    (Env.init (program.args (.value out) (.value input)).get) E entry s hentry
  rw [Cutpoint.zero] at hprefix
  have hsuffix := Cutpoint.after_segment (program (decodePrimitives sg) dg) 1 0 50
    (outerSuccessEnv E flag) F s t hsuccess
  rw [Cutpoint.zero] at hsuffix
  have hrun : (program (decodePrimitives sg) dg).runFrom
      (Env.init (program.args (.value out) (.value input)).get) 0 entry =
      .value (.nil, successState (finishPointState t d.point d.y) out
        (Valid.point bytes hvalid).bytes) := by
    rw [hprefix]
    change resume (decodePrimitives sg) dg 0 137 E s = _
    rw [decide_path (decodePrimitives sg) dg E s flag hdecision.flagRegister
      hdecision.zeroRegister hdecision.tagRegister, ite_eq_right hnonzero]
    change (program (decodePrimitives sg) dg).runFrom (outerSuccessEnv E flag) 1 s = _
    rw [hsuffix]
    exact Valid.finishPoint_run (decodePrimitives sg) dg F t out d.point d.y bytes hvalid
      hready.outputRegister hready.pointRegister hready.yRegister hready.fortyRegister
      hready.eightyRegister hready.eightyEightRegister hready.oneRegister
      hready.zeroRegister hready.thirtyTwoRegister hready.eightRegister
      hready.oneSixtyRegister hready.pointLive hready.yLive hready.outputLive
      hready.yDisjoint hready.outputDisjoint hwords.x hwords.y hwords.t
  rw [call_of_run dg sg out input entry _ hrun]
  congr 2
  apply GlobalState.ext
  · rfl
  · simp only [successState, MemoryState.eraseFrom_storeAt]
    rw [finishPointState_erase t d.point d.y entry.alloc.nextFreeBlock hprivate,
      hpublic.memory]

/-- Both reachable outcomes refine the fixed mathematical decoder. This is
not an assumption about the complete decoder call: `PrefixBoundary` lists the
precise source-prefix execution, flag, three reads and private-frame facts. -/
theorem linked_call_valid (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry : GlobalState) (bytes : Bytes32)
    (hwf : entry.WF) (hout : SmallRange entry.mem out 168)
    (hprefix : PrefixBoundary dg sg out input entry bytes) :
    ∃ after,
      (program (decodePrimitives sg) dg).call (Dalek.args2 out input) entry = .value (.nil, after) ∧
      Dalek.OutputFrame entry after out 168 ∧
      (Valid.decode bytes).elim (after.mem.readAt out 64 = 0)
        (fun P => after.mem.readAt out 64 = 1 ∧
          Dalek.ReadBytes after (out.add 8) 160 P.bytes) := by
  obtain ⟨E, s, flag, hentry, hdecision, hflag, hbranch⟩ := hprefix
  have hvalue := congrArg Prod.fst (wordStep1_value bytes)
  change (wordStep1 bytes).1 = (step1 bytes).1 at hvalue
  by_cases hz : flag = 0#8
  · have hpublic : PrefixPublic entry s := by simpa only [ite_eq_left hz] using hbranch
    have hinvalid : ¬(step1 bytes).1 = true := by
      rw [← hvalue, hflag.mp hz]
      decide
    refine ⟨{s with mem := (rejectionState entry out).mem}, ?_, ?_, ?_⟩
    · subst flag
      exact linked_call_rejection dg sg out input entry s E hentry hdecision hpublic
    · exact frame_with_allocator entry (rejectionState entry out) s out
        (rejectionState_frame hwf hout) hpublic.allocator
    · simp only [Valid.decode, dite_eq_right hinvalid, Option.elim_none]
      exact rejectionState_tag hout
  · have hvalid : (step1 bytes).1 = true := by
      rw [← hvalue]
      have hnot : ¬(wordStep1 bytes).1 = false := fun h => hz (hflag.mpr h)
      cases hb : (wordStep1 bytes).1 <;> simp_all
    simp only [ite_eq_right hz] at hbranch
    obtain ⟨F, t, d, hsuccess, hready, hpublic, hprivate, hwords⟩ := hbranch
    refine ⟨{t with mem := (successState entry out (Valid.point bytes hvalid).bytes).mem},
      linked_call_success dg sg out input entry s t E F flag d bytes hvalid hentry
        hdecision hz hsuccess hready hwords hpublic hprivate, ?_, ?_⟩
    · exact frame_with_allocator entry (successState entry out (Valid.point bytes hvalid).bytes)
        t out (successState_frame hwf hout _) hpublic.allocator
    · simp only [Valid.decode, dite_eq_left hvalid, Option.elim_some]
      exact ⟨successState_tag hout _, successState_payload hout _⟩

/-- Caller-visible tag classification against the permissive mathematical
encoding relation, for every 256-bit input. -/
theorem linked_call_classification (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry : GlobalState) (bytes : Bytes32)
    (hwf : entry.WF) (hout : SmallRange entry.mem out 168)
    (hprefix : PrefixBoundary dg sg out input entry bytes) :
    ∃ after,
      (program (decodePrimitives sg) dg).call (Dalek.args2 out input) entry =
        .value (.nil, after) ∧
      Dalek.OutputFrame entry after out 168 ∧
      (after.mem.readAt out 64 = 0 ↔ ¬∃ A, Bridge.Encodes bytes A) ∧
      (after.mem.readAt out 64 = 1 ↔ ∃ A, Bridge.Encodes bytes A) := by
  obtain ⟨after, hcall, hframe, hresult⟩ :=
    linked_call_valid dg sg out input entry bytes hwf hout hprefix
  refine ⟨after, hcall, hframe, ?_⟩
  cases hd : Valid.decode bytes with
  | none =>
    have henc := (Valid.decode_eq_none_iff bytes).mp hd
    simp only [hd, Option.elim_none] at hresult
    simp [hresult, henc]
  | some P =>
    have henc : ∃ A, Bridge.Encodes bytes A :=
      ⟨P.curve, Valid.decoderCorrect.sound bytes P hd⟩
    simp only [hd, Option.elim_some] at hresult
    simp [hresult.1, henc]

/-- A precise replacement for the old whole-call execution premise. The only
remaining hypothesis concerns the two stated original finite prefixes. -/
theorem contractUnder_of_prefixes (dg : Globals) (sg : SqrtRatio.Globals)
    (ready : GlobalState → Prop) (cofactor : ValidPoint → ValidPoint)
    (hprefix : ∀ (out input : Pointer) (entry : GlobalState) (bytes : Bytes32),
      entry.WF → ready entry → SmallRange entry.mem out 168 →
      Dalek.ReadBytes entry input 32 bytes →
      (Range.of out 1344).Disjoint (Range.of input 256) →
      PrefixBoundary dg sg out input entry bytes) :
    Dalek.DecompressContractUnder ready (linkedProgram dg sg).call
      (ValidPoint.layout cofactor) (ValidPoint.shared Valid.decode) := by
  change Dalek.DecompressContractUnder ready (program (decodePrimitives sg) dg).call
    (ValidPoint.layout cofactor) (ValidPoint.shared Valid.decode)
  intro out input entry bytes hwf hready hout hin hd
  obtain ⟨after, hcall, hframe, hresult⟩ := linked_call_valid dg sg out input entry bytes
    hwf hout (hprefix out input entry bytes hwf hready hout hin hd)
  refine ⟨after, hcall, hframe, ?_⟩
  simp only [ValidPoint.shared, ValidPoint.layout]
  generalize heq : Valid.decode bytes = decoded at hresult ⊢
  cases decoded <;> exact hresult

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.Semantic
