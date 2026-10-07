import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionSuccess
import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionMemory

/-! Composition of all four actual key-constructor blocks. The only call premise
is the decoder invocation; no key-constructor execution equality is assumed. -/
namespace Agave.Ed25519.Verifier.Execution.Key
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

def successState (s : GlobalState) (out opt bytes : Pointer) (x t : Words) : GlobalState :=
  let s' := payloadState s out opt bytes x t
  { s' with mem := s'.mem.storeAt out (0#8) }

theorem payload_range (h : SmallRange s.mem out 200) :
    SmallRange (payloadState s out opt bytes x t).mem out 200 := by
  exact ((((((((h.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

theorem run_success (p : Primitives) (E : Env program.Γ) (initial s : GlobalState)
    (out bytes : Pointer) (x t : Words)
    (hout : E.read (%arg0) = .value out) (hbytes : E.read (%arg1) = .value bytes)
    (hor : SmallRange s.mem out 200)
    (hpr : SmallRange s.mem (optionSlot initial) 168)
    (hbr : SmallRange s.mem bytes 32)
    (hop : out.id ≠ (optionSlot initial).id) (hob : out.id ≠ bytes.id)
    (hreads : NegationReads s (optionSlot initial) x t) :
    (program p).runFrom (entryEnv E initial true) 1 s =
      .value (.nil, successState s out (optionSlot initial) bytes x t) := by
  rw [Func.runFrom_eq, block_1, success_block E initial s out bytes x t hout hbytes
    hor hpr hbr hop hob hreads]
  change (program p).runFrom _ 3 _ = _
  apply return_block
  · simpa [successEnv, entryEnv, mlir_env] using hout
  · simp [successEnv, mlir_env]
  · exact Fits.mono (by decide) (payload_range hor).fits

def outputState (s : GlobalState) (out opt bytes : Pointer) (x t : Words) (valid : Bool) :
    GlobalState :=
  if valid then successState s out opt bytes x t else rejectedState s out

/-- Every constructor path terminates: the successful path has no small-order
branch. Small-order rejection belongs to the subsequent Dalek verifier. -/
theorem run_of_decoder (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer) (x t : Words) (valid : Bool)
    (hcall : p.decompress (args (optionSlot initial) bytes) (initial.alloca 168) =
      .value (.nil, decoded))
    (hpr : SmallRange decoded.mem (optionSlot initial) 168)
    (htag : decoded.mem.readAt (optionSlot initial) 64 = if valid then 1 else 0)
    (hor : SmallRange decoded.mem out 200)
    (hsuccess : valid = true → SmallRange decoded.mem bytes 32 ∧
      out.id ≠ (optionSlot initial).id ∧ out.id ≠ bytes.id ∧
      NegationReads decoded (optionSlot initial) x t) :
    (program p).run (args out bytes) initial =
      .value (.nil, outputState decoded out (optionSlot initial) bytes x t valid) := by
  rw [Func.run_runFrom_eq, Func.runFrom_eq]
  change ((program.bb0 p).run program.blockParams (Env.init (args out bytes).get) initial >>= _) = _
  rw [entry_block p _ initial decoded bytes valid (by simp [args, Env.init, mlir_env, Vals.get])
    hcall (Fits.mono (by decide) hpr.fits) htag]
  cases valid with
  | false =>
    change (program p).runFrom _ 2 decoded = _
    apply reject_block
    · simp [entryEnv, args, Env.init, mlir_env, Vals.get]
    · simp [entryEnv, mlir_env]
    · simp [entryEnv, mlir_env]
    · exact hor
  | true =>
    rcases hsuccess rfl with ⟨hbr,hop,hob,hreads⟩
    apply run_success p _ initial decoded out bytes x t
    · simp [args, Env.init, mlir_env, Vals.get]
    · simp [args, Env.init, mlir_env, Vals.get]
    · exact hor
    · exact hpr
    · exact hbr
    · exact hop
    · exact hob
    · exact hreads

theorem output_range (h : SmallRange s.mem out 200) :
    SmallRange (outputState s out opt bytes x t valid).mem out 200 := by
  cases valid
  · exact rejected_range h
  · exact (payload_range h).storeAt _ _

theorem output_tag (h : SmallRange s.mem out 200) :
    (outputState s out opt bytes x t valid).mem.readAt out 8 =
      if valid then 0 else 1 := by
  cases valid
  · exact rejected_tag h
  · exact MemoryState.readAt_storeAt_self
      (Fits.mono (by decide) (payload_range h).fits) _

/-- The observable Result tag follows the decoder Option tag for every input. -/
theorem observe_of_decoder (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer) (x t : Words) (valid : Bool)
    (hcall : p.decompress (args (optionSlot initial) bytes) (initial.alloca 168) =
      .value (.nil, decoded))
    (hpr : SmallRange decoded.mem (optionSlot initial) 168)
    (htag : decoded.mem.readAt (optionSlot initial) 64 = if valid then 1 else 0)
    (hor : SmallRange decoded.mem out 200)
    (hsuccess : valid = true → SmallRange decoded.mem bytes 32 ∧
      out.id ≠ (optionSlot initial).id ∧ out.id ≠ bytes.id ∧
      NegationReads decoded (optionSlot initial) x t)
    (hcaller : out.id.id < initial.alloc.nextFreeBlock) :
    observe p initial out bytes = some valid := by
  have hc := Func.call_of_run (run_of_decoder p initial decoded out bytes x t valid
    hcall hpr htag hor hsuccess)
  rw [observe, hc]
  simp only [erase_read _ _ _ _ hcaller, output_tag hor]
  cases valid <;> rfl

end Agave.Ed25519.Verifier.Execution.Key
