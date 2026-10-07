import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionControl

/-!
# The invocation-local external `bcmp` boundary

The pinned module declares `bcmp`; it does not define it. These propositions
are explicit linkage obligations, not implementations of that missing symbol.
Only length 32 and the zero/nonzero distinction are observed by this caller.
The final cleanup contains no memory reads, so acceptance needs no post-call
memory premise. A separate framed form records the read-only ABI guarantee
when a client needs to reason about the final memory as well.
-/

namespace Agave.Ed25519.Verifier.Execution.Dalek.Bcmp
open LeanMLIR.RIR

abbrev Call := Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32])

def args (left right : Pointer) : Vals [.ptr, .ptr, .bv 64] :=
  .cons (.value left) (.cons (.value right) (.cons (.value 32#64) .nil))

/-- Successful termination and the one observed bit of the result, for this
particular call. The bytes are the actual pre-call memory, rather than an
independently supplied specification value. Aliasing is permitted. -/
def Invocation (call : Call) (left right : Pointer) (state : GlobalState) : Prop :=
  ∃ (after : GlobalState) (result : BitVec 32),
    call (args left right) state = .value (.cons (.value result) .nil, after) ∧
    (result = 0 ↔ state.mem.readAt left 256 = state.mem.readAt right 256)

/-- Optional memory guarantee for the same invocation. This does not require
literal global-state identity: a linked routine may allocate private objects.
It imposes no ordering, sign, or fixed magnitude on a nonzero result. -/
def FramedInvocation (call : Call) (left right : Pointer) (state : GlobalState) : Prop :=
  ∃ (after : GlobalState) (result : BitVec 32),
    call (args left right) state = .value (.cons (.value result) .nil, after) ∧
    ReadOnlyFrame state after ∧
    (result = 0 ↔ state.mem.readAt left 256 = state.mem.readAt right 256)

theorem FramedInvocation.toInvocation {call : Call} {left right : Pointer}
    {state : GlobalState} (h : FramedInvocation call left right state) :
    Invocation call left right state := by
  obtain ⟨after, result, hcall, _, heq⟩ := h
  exact ⟨after, result, hcall, heq⟩

/-- The earlier all-state ABI contract specializes to this local boundary. -/
theorem of_compare_contract (call : Call) (h : CompareContract call)
    (left right : Pointer) (state : GlobalState) (a b : Bytes32)
    (hwf : state.WF) (ha : ReadBytes state left 32 a)
    (hb : ReadBytes state right 32 b) :
    FramedInvocation call left right state := by
  obtain ⟨after, result, hcall, hframe, heq⟩ := h left right state a b hwf ha hb
  refine ⟨after, result, hcall, hframe, ?_⟩
  simpa only [ha.2, hb.2] using heq

/-- Exact imported blocks 10, 12, and 13 need only the local extensional fact.
The theorem exposes the resulting state, without asserting any property of
that state which acceptance does not use. -/
theorem compression_tail_of_invocation (p : Primitives) (g : Globals)
    (E : Env program.Γ) (state compared : GlobalState)
    (out point signature : Pointer) (a r : Bytes32)
    (hout : E.read (%26) = .value out) (hpoint : E.read (%25) = .value point)
    (hsig : E.read (%arg1) = .value signature)
    (hlen : E.read (%1) = .value 32#64)
    (hzero : E.read (%19) = .value 0#32)
    (hok : E.read (%13) = .value 255#8)
    (herr : E.read (%8) = .value 2#8)
    (hc : p.compressPoint (args2 out point) state = .value (.nil, compared))
    (ha : compared.mem.readAt out 256 = a)
    (hr : compared.mem.readAt signature 256 = r)
    (hb : Invocation p.compareBytes out signature compared) :
    ∃ after, (program p g).runFrom E 10 state =
      .value (.cons (.value (code (decide (a = r)))) .nil, after) := by
  obtain ⟨after, result, hcall, heq⟩ := hb
  change result = 0#32 ↔ compared.mem.readAt out 256 = compared.mem.readAt signature 256 at heq
  have heq' : result = 0#32 ↔ a = r := by
    simpa only [ha, hr] using heq
  refine ⟨after, ?_⟩
  rw [compression_tail p g E state compared after out point signature result
    hout hpoint hsig hlen hzero hok herr hc hcall]
  simp only [heq']

/-- The optional frame is preserved through the real cleanup, whose operations
leave memory unchanged in the RIR semantics. This is a guarantee relative to
the state immediately before `bcmp`, after compression has already occurred. -/
theorem compression_tail_of_framed_invocation (p : Primitives) (g : Globals)
    (E : Env program.Γ) (state compared : GlobalState)
    (out point signature : Pointer) (a r : Bytes32)
    (hout : E.read (%26) = .value out) (hpoint : E.read (%25) = .value point)
    (hsig : E.read (%arg1) = .value signature)
    (hlen : E.read (%1) = .value 32#64)
    (hzero : E.read (%19) = .value 0#32)
    (hok : E.read (%13) = .value 255#8)
    (herr : E.read (%8) = .value 2#8)
    (hc : p.compressPoint (args2 out point) state = .value (.nil, compared))
    (ha : compared.mem.readAt out 256 = a)
    (hr : compared.mem.readAt signature 256 = r)
    (hb : FramedInvocation p.compareBytes out signature compared) :
    ∃ after, (program p g).runFrom E 10 state =
      .value (.cons (.value (code (decide (a = r)))) .nil, after) ∧
      ReadOnlyFrame compared after := by
  obtain ⟨after, result, hcall, hframe, heq⟩ := hb
  change result = 0#32 ↔ compared.mem.readAt out 256 = compared.mem.readAt signature 256 at heq
  have heq' : result = 0#32 ↔ a = r := by
    simpa only [ha, hr] using heq
  refine ⟨after, ?_, hframe⟩
  rw [compression_tail p g E state compared after out point signature result
    hout hpoint hsig hlen hzero hok herr hc hcall]
  simp only [heq']

end Agave.Ed25519.Verifier.Execution.Dalek.Bcmp
