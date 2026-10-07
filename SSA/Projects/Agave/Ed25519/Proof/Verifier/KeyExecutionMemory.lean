import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionControl

namespace Agave.Ed25519.Verifier.Execution.Key
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- Caller allocations survive the constructor's actual call-frame erasure. -/
theorem erase_get (m : MemoryState) (id : BlockId) (n : Nat) (h : id.id < n) :
    (m.eraseFrom n)[id]? = m[id]? := by
  simp [MemoryState.eraseFrom, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_filter', h]
  cases m.mem[id]? <;> rfl

theorem erase_read (m : MemoryState) (p : Pointer) (n w : Nat) (h : p.id.id < n) :
    (m.eraseFrom n).readAt p w = m.readAt p w := by
  simp only [MemoryState.readAt, erase_get m p.id n h]

theorem erase_range (h : SmallRange m p bytes) (hp : p.id.id < n) :
    SmallRange (m.eraseFrom n) p bytes := by
  rcases h with ⟨b, hb, hs, hr⟩
  exact ⟨b, (erase_get m p.id n hp).trans hb, hs, hr⟩

theorem rejected_range (h : SmallRange s.mem out 200) :
    SmallRange (rejectedState s out).mem out 200 :=
  (h.storeAt _ _).storeAt _ _

theorem rejected_tag (h : SmallRange s.mem out 200) :
    (rejectedState s out).mem.readAt out 8 = 1#8 := by
  exact MemoryState.readAt_storeAt_self
    (Fits.mono (by decide) (h.storeAt _ _).fits) _

/-- Full malformed-input call semantics, including frame erasure. -/
theorem call_rejected (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer)
    (hcall : p.decompress (args (optionSlot initial) bytes) (initial.alloca 168) =
      .value (.nil, decoded))
    (hfit : Fits decoded.mem (optionSlot initial) 64)
    (htag : decoded.mem.readAt (optionSlot initial) 64 = 0)
    (hrange : SmallRange decoded.mem out 200) :
    (program p).call (args out bytes) initial =
      .value (.nil, { rejectedState decoded out with
        mem := (rejectedState decoded out).mem.eraseFrom initial.alloc.nextFreeBlock }) :=
  Func.call_of_run (run_rejected p initial decoded out bytes hcall hfit htag hrange)

noncomputable def observe (p : Primitives) (initial : GlobalState) (out bytes : Pointer) :
    Option Bool :=
  match (program p).call (args out bytes) initial with
  | .poison => none
  | .value (_, s) => some (decide (s.mem.readAt out 8 = 0))

/-- Failure is an observed, defined `Err` result, rather than RIR poison. -/
theorem observe_rejected (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer)
    (hcall : p.decompress (args (optionSlot initial) bytes) (initial.alloca 168) =
      .value (.nil, decoded))
    (hfit : Fits decoded.mem (optionSlot initial) 64)
    (htag : decoded.mem.readAt (optionSlot initial) 64 = 0)
    (hrange : SmallRange decoded.mem out 200)
    (hcaller : out.id.id < initial.alloc.nextFreeBlock) :
    observe p initial out bytes = some false := by
  rw [observe, call_rejected p initial decoded out bytes hcall hfit htag hrange]
  simp only [erase_read _ _ _ _ hcaller, rejected_tag hrange]
  rfl

end Agave.Ed25519.Verifier.Execution.Key
