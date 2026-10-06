import SSA.Projects.Agave.Ed25519.Proof.Verifier.Execution
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

/-!
# The extracted byte-input wrapper

This module proves the four-block wrapper itself. Its contracts concern the
three individual external calls and the memory those calls return. None of the
contracts mentions execution of `Wrapper.program` or `RefinesControlFlow`.
-/

namespace Agave.Ed25519.Verifier.Execution.Wrapper

open LeanMLIR.RIR

def signatureSlot (s : GlobalState) : Pointer := s.allocaPtr
def keyResultSlot (s : GlobalState) : Pointer := (s.alloca 64).allocaPtr
def keySlot (s : GlobalState) : Pointer := ((s.alloca 64).alloca 200).allocaPtr
def allocated (s : GlobalState) : GlobalState := ((s.alloca 64).alloca 200).alloca 192

def ptrArgs (a b : Pointer) : Vals [.ptr, .ptr] :=
  .cons (.value a) (.cons (.value b) .nil)

def dalekArgs (key signature message : Pointer) (length : BitVec 64) :
    Vals [.ptr, .ptr, .ptr, .bv 64] :=
  .cons (.value key) (.cons (.value signature)
    (.cons (.value message) (.cons (.value length) .nil)))

def boolResult (b : Bool) : Vals [.bv 1] := .cons (.value (BitVec.ofBool b)) .nil

/-- Exactly the wrapper's 192-byte payload move, after the successful key tag. -/
def copiedKey (initial afterKey : GlobalState) : GlobalState :=
  { afterKey with mem := afterKey.mem.storeAt (keySlot initial) (afterKey.mem.readAt ((keyResultSlot initial).add 8) 1536) }

open Agave.Ed25519.Reduce64.Execution (SmallRange)

/-- Postconditions needed from the key constructor on its success path. These
are allocation and bounds requirements, independent of signature acceptance. -/
structure KeyMemory (initial afterKey : GlobalState) : Prop where
  resultRange : SmallRange afterKey.mem (keyResultSlot initial) 200
  destinationFits : Fits afterKey.mem (keySlot initial) 1536

/-- The signature and Dalek primitive calls on the successful key path. Their
states remain explicit: either primitive may allocate its own temporary frame. -/
structure SuccessCalls (p : Primitives) (i : Invocation)
    (initial afterKey afterSignature afterDalek : GlobalState) (accepted : Bool) : Prop where
  memory : KeyMemory initial afterKey
  signature : p.signatureFromBytes (ptrArgs (signatureSlot initial) i.signature)
    (copiedKey initial afterKey) = .value (.nil, afterSignature)
  dalek : p.verifyDalek
    (dalekArgs (keySlot initial) (signatureSlot initial) i.message i.length)
    afterSignature = .value (.cons (.value (resultCode accepted)) .nil, afterDalek)

theorem payload_disjoint (s : GlobalState) :
    (Range.of (keySlot s) 1536).Disjoint
      (Range.of ((keyResultSlot s).add 8) 1536) := by
  apply Range.disjoint_of_id_ne
  simp [keySlot, keyResultSlot, GlobalState.allocaPtr, GlobalState.alloca, Pointer.add]

/-- The public-key primitive's local ABI contract. In particular, truncation
of the tag is defined because its value is exactly zero or one. -/
structure KeyCall {Point Scalar : Type} (p : Primitives) (shared : Shared Point Scalar)
    (i : Invocation) (initial afterKey : GlobalState) (a : Bytes32) : Prop where
  call : p.keyFromBytes (ptrArgs (keyResultSlot initial) i.publicKey)
    (allocated initial) = .value (.nil, afterKey)
  tagFits : Fits afterKey.mem (keyResultSlot initial) 8
  tag : afterKey.mem.readAt (keyResultSlot initial) 8 =
    if (shared.decompress a).isNone then 1 else 0

/-- Primitive obligations for one concrete byte-input invocation. The key
constructor must produce the correct option tag. On success, the signature
constructor and Dalek primitive must meet their named call contracts. This
predicate contains no wrapper execution or wrapper-result assumption. -/
def PrimitiveCalls {Point Scalar Result : Type}
    (p : Primitives) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8)) : Prop :=
  ∃ afterKey afterSignature afterDalek,
    KeyCall p shared i initial afterKey a ∧
    ∀ A, shared.decompress a = some A →
      SuccessCalls p i initial afterKey afterSignature afterDalek
        (prehashed shared doubleBase compress (shared.negate A) r s (challenge r a message))

def entryEnv (i : Invocation) (s : GlobalState) (failed : Bool) : Env program.Γ :=
  (Env.init (Γ := program.Γ) i.args.get)[%0 := .value 1, %1 := .value 8, %2 := .value 192,
    %3 := .value 255, %4 := .value 0, %5 := .value (signatureSlot s),
    %6 := .value (keyResultSlot s), %7 := .value (keySlot s),
    %8 := .value (if failed then 1 else 0), %9 := .value (BitVec.ofBool failed)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem entry_run (p : Primitives) (i : Invocation) (initial afterKey : GlobalState)
    (failed : Bool)
    (hkey : p.keyFromBytes (ptrArgs (keyResultSlot initial) i.publicKey)
      (allocated initial) = .value (.nil, afterKey))
    (htagFits : Fits afterKey.mem (keyResultSlot initial) 8)
    (htag : afterKey.mem.readAt (keyResultSlot initial) 8 = if failed then 1 else 0) :
    (program.bb0 p).run program.blockParams (Env.init i.args.get) initial =
      .value ((entryEnv i initial failed, .inr (if failed then 1 else 2)), afterKey) := by
  generalize hS : initial = S
  symm at hS
  rw [BasicBlock.run_eq]
  simp only [EffectM.bind_eq]
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_impure => exact run_alloca
  clear hfits
  step_impure => exact run_alloca
  clear hfits
  step_impure => exact run_alloca
  clear hfits
  step_pure
  step_impure =>
    apply run_call
    simpa [hS, ptrArgs, keyResultSlot, allocated, Env.init, Invocation.args, Vals.get] using hkey
  have hfit : Fits S.mem (initial.alloca 64).allocaPtr 8 := by
    simpa [hS, keyResultSlot] using htagFits
  have hread : S.mem.readAt (initial.alloca 64).allocaPtr 8 = if failed then 1 else 0 := by
    simpa [hS, keyResultSlot] using htag
  step_load [hread] inline
  cases failed <;> step_pure
  all_goals
    rw [BasicBlock.runBodyFrom_done (Nat.le_of_ble_eq_true rfl)]
    simp only [EffectM.pure_eq, PoisonOr.value_bind]
    simp [program.bb0, Exit.run, Jump.run, program.blockParams, hE, entryEnv,
      Env.read, Env.write, Env.set, signatureSlot, keyResultSlot, keySlot]
    rfl

def successEnv (i : Invocation) (s : GlobalState) (accepted : Bool) : Env program.Γ :=
  (entryEnv i s false)[%10 := .value ((keyResultSlot s).add 8),
    %11 := .value (resultCode accepted), %12 := .value (BitVec.ofBool accepted),
    %13 := .value (BitVec.ofBool accepted)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem success_run (p : Primitives) (i : Invocation)
    (initial afterKey afterSignature afterDalek : GlobalState) (accepted : Bool)
    (hcalls : SuccessCalls p i initial afterKey afterSignature afterDalek accepted) :
    (program.bb2 p).run program.blockParams (entryEnv i initial false) afterKey =
      .value ((successEnv i initial accepted, .inr 3), afterDalek) := by
  obtain ⟨hmemory, hsignature, hdalek⟩ := hcalls
  have hgep := hmemory.resultRange.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  change Operation.gepInboundsLive afterKey.mem (.value (keyResultSlot initial))
    [.value 8] = .value ((keyResultSlot initial).add 8) at hgep
  have hsource := hmemory.resultRange.fits_add (k := 8) (count := 192) (by decide)
  change Fits afterKey.mem ((keyResultSlot initial).add 8) 1536 at hsource
  have hdest := hmemory.destinationFits
  have hdisjoint := payload_disjoint initial
  generalize hS : afterKey = S
  symm at hS
  generalize hE : entryEnv i initial false = E
  symm at hE
  dsimp only [entryEnv] at hE
  rw [BasicBlock.run_eq]
  simp only [EffectM.bind_eq]
  step_pure [entryEnv]
  have hgepS : Operation.gepInboundsLive S.mem (.value (keyResultSlot initial))
      [.value 8] = .value ((keyResultSlot initial).add 8) := by simpa [hS] using hgep
  step_reduce_gep [hgepS, entryEnv, GepIndex.inboundsOffset]
  clear hgepS
  have hfs : Fits S.mem ((keyResultSlot initial).add 8) 1536 := by simpa [hS] using hsource
  have hfd : Fits S.mem (keySlot initial) 1536 := by simpa [hS] using hdest
  step_memcpy
  clear hfs hfd hread
  step_pure
  step_pure
  step_impure =>
    apply run_call
    simpa [hS, ptrArgs, copiedKey, Env.init, Invocation.args, Vals.get] using hsignature
  step_impure =>
    apply run_call
    simpa [hS, dalekArgs, Env.init, Invocation.args, Vals.get] using hdalek
  cases accepted
  all_goals
    step_pure [resultCode]
    step_pure
    step_pure
    rw [BasicBlock.runBodyFrom_done (Nat.le_of_ble_eq_true rfl)]
    simp only [EffectM.pure_eq, PoisonOr.value_bind]
    simp [program.bb2, Exit.run, Jump.run, program.blockParams, hE, successEnv, entryEnv,
      Env.read, Env.write, Env.set, resultCode]
    rfl

theorem rejected_tail (p : Primitives) (i : Invocation) (initial afterKey : GlobalState) :
    (program p).evalFrom 2 (entryEnv i initial true) 1 afterKey =
      .value (some (boolResult false), afterKey) := by
  rfl

theorem return_tail (p : Primitives) (i : Invocation) (initial finalState : GlobalState)
    (accepted : Bool) :
    (program p).evalFrom 1 (successEnv i initial accepted) 3 finalState =
      .value (some (boolResult accepted), finalState) := by
  rfl

/-- The actual extracted wrapper terminates within three visited basic blocks.
The result follows solely from its three primitive call contracts and memory
bounds, including on the public-key rejection path. -/
theorem eval_of_calls (p : Primitives) (i : Invocation)
    (initial afterKey afterSignature afterDalek : GlobalState)
    (failed accepted : Bool)
    (hkey : p.keyFromBytes (ptrArgs (keyResultSlot initial) i.publicKey)
      (allocated initial) = .value (.nil, afterKey))
    (htagFits : Fits afterKey.mem (keyResultSlot initial) 8)
    (htag : afterKey.mem.readAt (keyResultSlot initial) 8 = if failed then 1 else 0)
    (hcalls : failed = false → SuccessCalls p i initial afterKey afterSignature afterDalek accepted) :
    (program p).eval 3 i.args initial =
      .value (some (boolResult (if failed then false else accepted)),
        if failed then afterKey else afterDalek) := by
  change (program p).evalFrom 3 (Env.init i.args.get) 0 initial = _
  rw [Func.evalFrom]
  simp only [EffectM.bind_eq]
  change ((program.bb0 p).run program.blockParams (Env.init i.args.get) initial >>= _) = _
  rw [entry_run p i initial afterKey failed hkey htagFits htag]
  simp only [PoisonOr.value_bind]
  cases failed with
  | true => exact rejected_tail p i initial afterKey
  | false =>
    rw [Func.evalFrom]
    simp only [EffectM.bind_eq]
    change ((program.bb2 p).run program.blockParams (entryEnv i initial false) afterKey >>= _) = _
    rw [success_run p i initial afterKey afterSignature afterDalek accepted (hcalls rfl)]
    simp only [PoisonOr.value_bind]
    exact return_tail p i initial afterDalek accepted

theorem rejected_run_tail (p : Primitives) (i : Invocation) (initial afterKey : GlobalState) :
    (program p).runFrom (entryEnv i initial true) 1 afterKey =
      .value (boolResult false, afterKey) := by
  rw [Func.runFrom_eq]
  change Func.continue (func := program p)
    ((entryEnv i initial true)[%13 := .value 0]) (.inr 3) afterKey = _
  rw [Func.continue_next, Func.runFrom_eq]
  change Func.continue (func := program p)
    ((entryEnv i initial true)[%13 := .value 0]) (.inl (boolResult false)) afterKey = _
  rfl

theorem return_run_tail (p : Primitives) (i : Invocation) (initial finalState : GlobalState)
    (accepted : Bool) :
    (program p).runFrom (successEnv i initial accepted) 3 finalState =
      .value (boolResult accepted, finalState) := by
  rw [Func.runFrom_eq]
  change Func.continue (func := program p) (successEnv i initial accepted)
    (.inl (boolResult accepted)) finalState = _
  rfl

/-- The same instruction proof establishes the actual fuel-independent RIR
semantics, without treating a finite simulator as an assumed execution oracle. -/
theorem run_of_calls (p : Primitives) (i : Invocation)
    (initial afterKey afterSignature afterDalek : GlobalState)
    (failed accepted : Bool)
    (hkey : p.keyFromBytes (ptrArgs (keyResultSlot initial) i.publicKey)
      (allocated initial) = .value (.nil, afterKey))
    (htagFits : Fits afterKey.mem (keyResultSlot initial) 8)
    (htag : afterKey.mem.readAt (keyResultSlot initial) 8 = if failed then 1 else 0)
    (hcalls : failed = false → SuccessCalls p i initial afterKey afterSignature afterDalek accepted) :
    (program p).run i.args initial =
      .value (boolResult (if failed then false else accepted),
        if failed then afterKey else afterDalek) := by
  rw [Func.run_runFrom_eq, Func.runFrom_eq]
  change ((program.bb0 p).run program.blockParams (Env.init i.args.get) initial >>= _) = _
  rw [entry_run p i initial afterKey failed hkey htagFits htag]
  simp only [PoisonOr.value_bind]
  cases failed with
  | true => exact rejected_run_tail p i initial afterKey
  | false =>
    change (program p).runFrom (entryEnv i initial false) 2 afterKey = _
    rw [Func.runFrom_eq]
    change ((program.bb2 p).run program.blockParams (entryEnv i initial false) afterKey >>= _) = _
    rw [success_run p i initial afterKey afterSignature afterDalek accepted (hcalls rfl)]
    simp only [PoisonOr.value_bind]
    exact return_run_tail p i initial afterDalek accepted

/-- All byte strings are covered, including failed public-key decompression.
The only execution premises name individual external primitive calls. -/
theorem eval_of_primitive_calls {Point Scalar Result : Type}
    (p : Primitives) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (h : PrimitiveCalls p shared doubleBase compress challenge i initial a r s message) :
    ∃ finalState, (program p).eval 3 i.args initial =
      .value (some (boolResult (verify shared doubleBase compress a r s (challenge r a message))), finalState) := by
  obtain ⟨afterKey, afterSignature, afterDalek, hkey, hsuccess⟩ := h
  cases ha : shared.decompress a with
  | none =>
    refine ⟨afterKey, ?_⟩
    have hexec := eval_of_calls p i initial afterKey afterSignature afterDalek true false
      hkey.call hkey.tagFits (by simpa [ha] using hkey.tag) (by simp)
    simpa [verify, ha] using hexec
  | some A =>
    refine ⟨afterDalek, ?_⟩
    have hexec := eval_of_calls p i initial afterKey afterSignature afterDalek false
      (prehashed shared doubleBase compress (shared.negate A) r s (challenge r a message))
      hkey.call hkey.tagFits (by simpa [ha] using hkey.tag) (fun _ => hsuccess A ha)
    simpa [verify, ha] using hexec

theorem run_of_primitive_calls {Point Scalar Result : Type}
    (p : Primitives) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (h : PrimitiveCalls p shared doubleBase compress challenge i initial a r s message) :
    ∃ finalState, (program p).run i.args initial =
      .value (boolResult (verify shared doubleBase compress a r s (challenge r a message)), finalState) := by
  obtain ⟨afterKey, afterSignature, afterDalek, hkey, hsuccess⟩ := h
  cases ha : shared.decompress a with
  | none =>
    refine ⟨afterKey, ?_⟩
    have hexec := run_of_calls p i initial afterKey afterSignature afterDalek true false
      hkey.call hkey.tagFits (by simpa [ha] using hkey.tag) (by simp)
    simpa [verify, ha] using hexec
  | some A =>
    refine ⟨afterDalek, ?_⟩
    have hexec := run_of_calls p i initial afterKey afterSignature afterDalek false
      (prehashed shared doubleBase compress (shared.negate A) r s (challenge r a message))
      hkey.call hkey.tagFits (by simpa [ha] using hkey.tag) (fun _ => hsuccess A ha)
    simpa [verify, ha] using hexec

/-- Lift the actual RIR run to its call semantics, including its
frame erasure. The returned value is a defined, canonical one-bit Boolean. -/
theorem call_of_primitive_calls {Point Scalar Result : Type}
    (p : Primitives) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (h : PrimitiveCalls p shared doubleBase compress challenge i initial a r s message) :
    ∃ finalState, (program p).call i.args initial =
      .value (boolResult (verify shared doubleBase compress a r s (challenge r a message)), finalState) := by
  obtain ⟨finalState, hrun⟩ := run_of_primitive_calls p shared doubleBase compress challenge
    i initial a r s message h
  exact ⟨_, Func.call_of_run hrun⟩

theorem observe_of_primitive_calls {Point Scalar Result : Type}
    (p : Primitives) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (h : PrimitiveCalls p shared doubleBase compress challenge i initial a r s message) :
    observe p i initial = some (verify shared doubleBase compress a r s (challenge r a message)) := by
  obtain ⟨finalState, hcall⟩ := call_of_primitive_calls p shared doubleBase compress challenge
    i initial a r s message h
  simp only [observe, hcall, boolResult]
  cases verify shared doubleBase compress a r s (challenge r a message) <;> rfl

/-- Construct the former whole-wrapper refinement obligation from the explicit
primitive and memory obligations. This theorem proves wrapper execution; it
does not assume an equality involving wrapper execution in any premise. -/
theorem refines_of_primitive_calls {Point Scalar Result : Type}
    (p : Primitives) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (environment : Invocation → GlobalState → Prop)
    (hcalls : ∀ i state a r s message,
      Represents i state a r s message → environment i state →
      PrimitiveCalls p shared doubleBase compress challenge i state a r s message) :
    RefinesControlFlow p shared doubleBase compress challenge environment := by
  intro i state a r s message hinput henv
  exact observe_of_primitive_calls p shared doubleBase compress challenge i state a r s message
    (hcalls i state a r s message hinput henv)

end Agave.Ed25519.Verifier.Execution.Wrapper
