import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptCorrectMemory

/-! Concrete invocation resources and intermediate states. Input allocations
may alias each other, the constants, and the output; only the private context
must be separate. The final digest is written after all input has been read. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge Agave.Ed25519.SHA512
open Agave.Ed25519.Verifier.Execution.Challenge

structure At (v : TranscriptInvocation) (id : BlockId) (s : GlobalState) : Prop where
  wf : s.WF
  constants : constantsGlobal.Present id s.mem
  contextLive : SmallRange s.mem v.context 224
  signatureLive : SmallRange s.mem v.signature 32
  publicKeyLive : SmallRange s.mem v.publicKey 32
  messageLive : v.size ≠ 0#64 → SmallRange s.mem v.message v.size.toNat
  outputLive : SmallRange s.mem v.output 64

structure Ready (v : TranscriptInvocation) (id : BlockId) : Prop extends At v id v.initial where
  constantsAddress : v.constants = constantsGlobal.address id
  context_constants : v.context.id ≠ id
  context_signature : v.context.id ≠ v.signature.id
  context_publicKey : v.context.id ≠ v.publicKey.id
  context_message : v.size ≠ 0#64 → v.context.id ≠ v.message.id
  output_context : v.output.id ≠ v.context.id

theorem At.transport {v : TranscriptInvocation} {id : BlockId} {s t : GlobalState}
    (h : At v id s) (hw : Append.BlockWrites v.context.id s.mem t.mem)
    (hwf : t.WF) (hne : v.context.id ≠ id) : At v id t :=
  ⟨hwf, hw.present constantsGlobal id (Ne.symm hne) h.constants,
   hw.live h.contextLive, hw.live h.signatureLive, hw.live h.publicKeyLive,
   (fun hn => hw.live (h.messageLive hn)), hw.live h.outputLive⟩

def afterInit (v : TranscriptInvocation) : GlobalState :=
  {v.initial with mem := Init.memory v.initial.mem v.context}
def afterR (v : TranscriptInvocation) : GlobalState :=
  Append.resultState v.afterInit v.context v.signature 32#64
def afterA (v : TranscriptInvocation) : GlobalState :=
  Append.resultState v.afterR v.context v.publicKey 32#64
def afterMessage (v : TranscriptInvocation) : GlobalState :=
  Append.resultState v.afterA v.context v.message v.size

theorem afterInit_writes (v : TranscriptInvocation) :
    Append.BlockWrites v.context.id v.initial.mem v.afterInit.mem :=
  init_writes _ _
theorem afterR_writes (v : TranscriptInvocation) :
    Append.BlockWrites v.context.id v.initial.mem v.afterR.mem :=
  v.afterInit_writes.trans (Append.result_writes _ _ _ _)
theorem afterA_writes (v : TranscriptInvocation) :
    Append.BlockWrites v.context.id v.initial.mem v.afterA.mem :=
  v.afterR_writes.trans (Append.result_writes _ _ _ _)
theorem afterMessage_writes (v : TranscriptInvocation) :
    Append.BlockWrites v.context.id v.initial.mem v.afterMessage.mem :=
  v.afterA_writes.trans (Append.result_writes _ _ _ _)

theorem Ready.afterInit {v : TranscriptInvocation} {id : BlockId} (h : Ready v id) :
    At v id v.afterInit :=
  h.toAt.transport v.afterInit_writes (Init.memory_wf _ _ h.wf) h.context_constants

theorem Ready.afterR {v : TranscriptInvocation} {id : BlockId} (h : Ready v id) :
    At v id v.afterR :=
  h.afterInit.transport (Append.result_writes _ _ _ _)
    (Append.result_wf _ _ _ _ h.afterInit.wf) h.context_constants

theorem Ready.afterA {v : TranscriptInvocation} {id : BlockId} (h : Ready v id) :
    At v id v.afterA :=
  h.afterR.transport (Append.result_writes _ _ _ _)
    (Append.result_wf _ _ _ _ h.afterR.wf) h.context_constants

theorem Ready.afterMessage {v : TranscriptInvocation} {id : BlockId} (h : Ready v id) :
    At v id v.afterMessage :=
  h.afterA.transport (Append.result_writes _ _ _ _)
    (Append.result_wf _ _ _ _ h.afterA.wf) h.context_constants

theorem afterMessage_allocator (v : TranscriptInvocation) :
    v.initial.alloc.nextFreeBlock ≤ v.afterMessage.alloc.nextFreeBlock :=
  (Append.result_allocator v.afterInit v.context v.signature 32#64).trans
    ((Append.result_allocator v.afterR v.context v.publicKey 32#64).trans
      (Append.result_allocator v.afterA v.context v.message v.size))

theorem context_count_bound {m : MemoryState} {p : Pointer} {completed pending : Bytes}
    (h : ContextRepresents m p completed pending) :
    (m.readAt (p.add 200#64) 64).toNat < 128 := by
  rw [h.pendingCount, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := h.pendingBound; omega)]
  exact h.pendingBound

/-- Public success includes precisely the output pointer checked by observe,
both byte and word views of its 64-byte digest, and the remaining caller frame. -/
structure ExecutionResult (v : TranscriptInvocation) (after : GlobalState)
    (r a : BitVec 256) (message : HashBytes) : Prop where
  run : v.run = .value (.cons (.value v.output) .nil, after)
  outputLive : SmallRange after.mem v.output 64
  digest : after.mem.readAt v.output 512 =
    SHA512.digest Spec.compression (hashTranscript r a message)
  digestBytes : readBytes after.mem v.output 64 =
    bytesOf (n := 64) (SHA512.digest Spec.compression (hashTranscript r a message))
  wf : after.WF
  allocator : v.initial.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock
  frame : ∀ q bits, q.id ≠ v.context.id →
    (Range.of v.output 512).Disjoint (Range.of q bits) →
    after.mem.readAt q bits = v.initial.mem.readAt q bits
  otherBlocks : ∀ id, id ≠ v.context.id → id ≠ v.output.id →
    after.mem[id]? = v.initial.mem[id]?

theorem ExecutionResult.correct {v : TranscriptInvocation} {after : GlobalState}
    {r a : BitVec 256} {message : HashBytes} (h : ExecutionResult v after r a message) :
    v.Correct r a message := by
  have hf : Fits after.mem v.output 512 := h.outputLive.fits
  unfold Correct observe
  rw [h.run]
  change (if v.output = v.output ∧ Fits after.mem v.output 512
    then some (after.mem.readAt v.output 512) else none) = _
  rw [ite_eq_left ⟨rfl, hf⟩, h.digest]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
