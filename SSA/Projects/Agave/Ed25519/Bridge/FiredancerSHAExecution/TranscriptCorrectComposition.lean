import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptCorrectState

/-! Composition of the actual five RIR calls. This layer separates the pure
append-memory invariant from already proved call execution; the concrete
endpoint instantiates that single invariant in TranscriptCorrect. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge Agave.Ed25519.SHA512
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A property only of the explicit append memory transition, not an assumed
execution equation or a whole-hash result. The concrete proof is supplied by
Append.Semantic.result_represents. -/
def AppendPreserves : Prop :=
  ∀ (s : GlobalState) (context data : Pointer) (size : BitVec 64)
    (completed pending : Bytes),
    ContextRepresents s.mem context completed pending →
    SmallRange s.mem data size.toNat → context.id ≠ data.id →
    ∃ completed' pending',
      ContextRepresents (Append.resultState s context data size).mem context completed' pending' ∧
      completed' ++ pending' =
        (completed ++ pending) ++ readBytes s.mem data size.toNat

theorem append_step_of_semantics (happend : AppendPreserves)
    (id : BlockId) (s : GlobalState) (context data : Pointer) (size : BitVec 64)
    (completed pending : Bytes) (hr : Append.Resources id s context data size)
    (hp : ContextRepresents s.mem context completed pending) :
    ∃ completed' pending',
      ContextRepresents (Append.resultState s context data size).mem context completed' pending' ∧
      completed' ++ pending' = (completed ++ pending) ++ readBytes s.mem data size.toNat ∧
      (appendProgram (constantsGlobal.address id)).call
        (Append.program.args (.value context) (.value data) (.value size)) s =
        .value (.cons (.value context) .nil, Append.resultState s context data size) := by
  obtain ⟨completed', pending', hp', hinput⟩ :=
    happend s context data size completed pending hp hr.inputLive hr.distinct
  exact ⟨completed', pending', hp', hinput,
    Append.linked_call id s context data size hr (context_count_bound hp)⟩

/-- Zero-length append does not inspect the message pointer, its allocation,
or any bytes. The nonempty path uses the ordinary checked resources. -/
theorem append_optional_of_semantics (happend : AppendPreserves)
    (id : BlockId) (s : GlobalState) (context data : Pointer) (size : BitVec 64)
    (completed pending : Bytes) (hwf : s.WF)
    (hp : ContextRepresents s.mem context completed pending)
    (hk : constantsGlobal.Present id s.mem) (hck : context.id ≠ id)
    (hi : size ≠ 0#64 → SmallRange s.mem data size.toNat)
    (hne : size ≠ 0#64 → context.id ≠ data.id) :
    ∃ completed' pending',
      ContextRepresents (Append.resultState s context data size).mem context completed' pending' ∧
      completed' ++ pending' = (completed ++ pending) ++ readBytes s.mem data size.toNat ∧
      (appendProgram (constantsGlobal.address id)).call
        (Append.program.args (.value context) (.value data) (.value size)) s =
        .value (.cons (.value context) .nil, Append.resultState s context data size) := by
  by_cases hz : size = 0#64
  · subst size
    refine ⟨completed, pending, ?_, ?_, ?_⟩
    · simpa only [Append.resultState, ↓reduceIte] using hp
    · simp [readBytes]
    · simpa only [Append.resultState, ↓reduceIte] using
        append_empty_call (constantsGlobal.address id) (.value context) (.value data) s hwf
  · exact append_step_of_semantics happend id s context data size completed pending
      ⟨hwf, hp.live, hi hz, hk, hne hz, hck⟩ hp

/-- Exact imported init, append(R), append(A), append(M), and finish execution.
All input reads occur before the final output stores, so output/input aliasing
needs no exclusion. No additional total-transcript size bound is introduced. -/
theorem execution_of_append_semantics (happend : AppendPreserves)
    (v : TranscriptInvocation) (id : BlockId) (r a : BitVec 256) (message : HashBytes)
    (h : Ready v id)
    (hr : readBytes v.initial.mem v.signature 32 = bytesOf (n := 32) r)
    (ha : readBytes v.initial.mem v.publicKey 32 = bytesOf (n := 32) a)
    (hm : readBytes v.initial.mem v.message v.size.toNat = message) :
    ∃ after, ExecutionResult v after r a message := by
  have hp0 := Init.memory_represents v.initial.mem v.context h.contextLive
  change ContextRepresents v.afterInit.mem v.context [] [] at hp0
  have hinit := Init.call v.initial v.context h.wf h.contextLive
  change Init.program.call (Init.program.args (.value v.context)) v.initial =
    .value (.cons (.value v.context) .nil, v.afterInit) at hinit
  have hresourcesR : Append.Resources id v.afterInit v.context v.signature 32#64 :=
    ⟨h.afterInit.wf, h.afterInit.contextLive, h.afterInit.signatureLive,
     h.afterInit.constants, h.context_signature, h.context_constants⟩
  obtain ⟨completedR, pendingR, hpR, hinputR, hcallR⟩ :=
    append_step_of_semantics happend id v.afterInit v.context v.signature 32#64 [] [] hresourcesR hp0
  change ContextRepresents v.afterR.mem v.context completedR pendingR at hpR
  have hreadR : readBytes v.afterInit.mem v.signature 32 = bytesOf (n := 32) r :=
    (writes_readBytes v.afterInit_writes _ _ (Ne.symm h.context_signature)).trans hr
  change completedR ++ pendingR = ([] ++ []) ++ readBytes v.afterInit.mem v.signature 32 at hinputR
  rw [hreadR] at hinputR
  simp only [List.nil_append] at hinputR
  have hresourcesA : Append.Resources id v.afterR v.context v.publicKey 32#64 :=
    ⟨h.afterR.wf, h.afterR.contextLive, h.afterR.publicKeyLive,
     h.afterR.constants, h.context_publicKey, h.context_constants⟩
  obtain ⟨completedA, pendingA, hpA, hinputA, hcallA⟩ :=
    append_step_of_semantics happend id v.afterR v.context v.publicKey 32#64
      completedR pendingR hresourcesA hpR
  change ContextRepresents v.afterA.mem v.context completedA pendingA at hpA
  have hreadA : readBytes v.afterR.mem v.publicKey 32 = bytesOf (n := 32) a :=
    (writes_readBytes v.afterR_writes _ _ (Ne.symm h.context_publicKey)).trans ha
  change completedA ++ pendingA = (completedR ++ pendingR) ++ readBytes v.afterR.mem v.publicKey 32 at hinputA
  rw [hinputR, hreadA] at hinputA
  obtain ⟨completedM, pendingM, hpM, hinputM, hcallM⟩ :=
    append_optional_of_semantics happend id v.afterA v.context v.message v.size
      completedA pendingA h.afterA.wf hpA h.afterA.constants h.context_constants
      h.afterA.messageLive h.context_message
  change ContextRepresents v.afterMessage.mem v.context completedM pendingM at hpM
  have hreadM : readBytes v.afterA.mem v.message v.size.toNat = message :=
    by
      by_cases hz : v.size = 0#64
      · simpa [hz, readBytes] using hm
      · exact (writes_readBytes v.afterA_writes _ _ (Ne.symm (h.context_message hz))).trans hm
  rw [hinputA, hreadM] at hinputM
  change completedM ++ pendingM = hashTranscript r a message at hinputM
  obtain ⟨after, hfinish, hresult, houtput⟩ := finish_source_live id v.context v.output
    v.afterMessage completedM pendingM h.afterMessage.wf hpM h.afterMessage.outputLive
    h.afterMessage.constants h.context_constants h.output_context
  have hrun : v.run = .value (.cons (.value v.output) .nil, after) := by
    unfold run
    rw [h.constantsAddress]
    simp only [EffectM.bind_eq, hinit, LeanMLIR.RIR.PoisonOr.value_bind]
    rw [hcallR]
    simp only [LeanMLIR.RIR.PoisonOr.value_bind]
    change (do
      let _ ← (appendProgram (constantsGlobal.address id)).call
        (Append.program.args (.value v.context) (.value v.publicKey) (.value 32#64))
      let _ ← (appendProgram (constantsGlobal.address id)).call
        (Append.program.args (.value v.context) (.value v.message) (.value v.size))
      (finishProgram (constantsGlobal.address id)).call
        (Finish.program.args (.value v.context) (.value v.output))) v.afterR = _
    simp only [EffectM.bind_eq, hcallA, LeanMLIR.RIR.PoisonOr.value_bind]
    change (do
      let _ ← (appendProgram (constantsGlobal.address id)).call
        (Append.program.args (.value v.context) (.value v.message) (.value v.size))
      (finishProgram (constantsGlobal.address id)).call
        (Finish.program.args (.value v.context) (.value v.output))) v.afterA = _
    simp only [EffectM.bind_eq, hcallM, LeanMLIR.RIR.PoisonOr.value_bind]
    exact hfinish
  have hdigest : readBytes after.mem v.output 64 =
      bytesOf (n := 64) (digest Spec.compression (hashTranscript r a message)) := by
    rw [hresult.digest, hinputM]
  refine ⟨after, hrun, houtput, readAt_of_readBytes _ _ _ _ houtput hdigest,
    hdigest, hresult.wf, ?_, ?_, ?_⟩
  · rw [hresult.alloc]
    exact v.afterMessage_allocator.trans (Nat.le_add_right _ _)
  · intro q bits hq hdis
    rw [hresult.frame q bits (Or.inl (Ne.symm hq)) hdis]
    exact writes_readAt v.afterMessage_writes q bits hq
  · intro j hc ho
    exact (hresult.otherBlocks j hc ho).trans (v.afterMessage_writes.other j hc)

theorem correct_of_append_semantics (happend : AppendPreserves)
    (v : TranscriptInvocation) (id : BlockId) (r a : BitVec 256) (message : HashBytes)
    (h : Ready v id)
    (hr : readBytes v.initial.mem v.signature 32 = bytesOf (n := 32) r)
    (ha : readBytes v.initial.mem v.publicKey 32 = bytesOf (n := 32) a)
    (hm : readBytes v.initial.mem v.message v.size.toNat = message) :
    v.Correct r a message := by
  obtain ⟨after, hafter⟩ := execution_of_append_semantics happend v id r a message h hr ha hm
  exact hafter.correct

end Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
