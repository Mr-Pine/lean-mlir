import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionTail
import SSA.Projects.Agave.Ed25519.Proof.Conformance.ScalarAvx2

/-!
# Cache selection is observationally irrelevant

The pure result is independent of every 8-bit cache value. The extracted suffix
requires execution/refinement only of the backend that is actually selected.
This separates semantic acceptance from the hardware legality and termination
of that selected execution. An initializer that returns without changing the
255 sentinel is also covered: the caller reloads it and selects serial.

A trapping or nonterminating initializer is not a successful verification and
cannot be equated to a Boolean result by these theorems. Likewise, they make no
claim that an AVX2 instruction is legal on a processor without AVX2 support.
-/

namespace Agave.Ed25519.Conformance
open PointArithmetic Tables Verifier DoubleBase

/-- Cache corruption or an inaccurate feature decision cannot change the pure
Boolean, even on malformed inputs. Byte 1 selects AVX2; all others select serial. -/
theorem pure_cache_all_messages {Point : Type}
    (shared : Shared Point Nat) (coordinates : Point → Extended F)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Nat)
    (a r s : Bytes32) (message : List (BitVec 8)) (cache : BitVec 8) :
    verify shared
        (if cache = 1 then (fun h A s => avx2Math h (coordinates A) s)
          else (fun h A s => serialMath h (coordinates A) s))
        compressMath a r s (challenge r a message) =
      verify shared (fun h A s => serialMath h (coordinates A) s)
        compressMath a r s (challenge r a message) := by
  by_cases hc : cache = 1
  · simp only [hc, ↓reduceIte]
    exact (pure_scalar_avx2_all_messages shared coordinates challenge a r s message).symm
  · simp only [hc, ↓reduceIte]

end Agave.Ed25519.Conformance

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR

/-- The unselected backend needs no execution premise. In particular, taking
the serial branch does not require AVX2 instruction legality on that CPU. -/
theorem backend_tail_of_selected_contract {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (vector : Bool)
    (hselected : DoubleBaseContract
      (if vector then p.avx2DoubleBase else p.serialDoubleBase) layout doubleBase)
    (q : TailPointers) (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hregs : TailRegisters q E) (hmem : TailMemory q state layout h scalar a r) :
    ∃ after, (program p g).runFrom E (if vector then 9 else 8) state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil,
        after) := by
  obtain ⟨middle, encoded, hcall, hframe, hresult, hencoded⟩ :=
    hselected q.output q.challenge q.point q.scalar state h scalar a
      hmem.wellFormed hmem.output hmem.challenge hmem.point hmem.scalar
      hmem.outputChallenge hmem.outputPoint hmem.outputScalar
  have hr : ReadBytes middle q.signature 32 r :=
    ⟨hframe.live q.signature 32 hmem.signature.1,
      (hframe.read q.signature 256 hmem.signatureOutput).trans hmem.signature.2⟩
  obtain ⟨after, hsuffix⟩ := compression_tail_of_contracts p g layout compress
    hcompress hcompare E middle q.compressed q.output q.signature
    (doubleBase h a scalar) r encoded hregs.compressed hregs.output hregs.signature
    hregs.length hregs.zero hregs.ok hregs.error hframe.wellFormed
    (hframe.live q.compressed 32 hmem.compressed) hresult hencoded hr
    hmem.compressedOutput hmem.signatureCompressed
  refine ⟨after, ?_⟩
  cases vector with
  | false =>
    change (program p g).runFrom E 8 state = _
    rw [serial_block p g E state middle q.output q.challenge q.point q.scalar
      hregs.output hregs.challenge hregs.point hregs.scalar hcall]
    exact hsuffix
  | true =>
    change (program p g).runFrom E 9 state = _
    rw [avx2_block p g E state middle q.output q.challenge q.point q.scalar
      hregs.output hregs.challenge hregs.point hregs.scalar hcall]
    exact hsuffix

/-- Every cache byte is covered by the exact dispatch CFG. The cache value is
read from memory, and refinement is required only of that selected backend. -/
theorem dispatch_tail_of_selected_contract {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (q : TailPointers) (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hregs : TailRegisters q E) (hmem : TailMemory q state layout h scalar a r)
    (hcache : Fits state.mem q.cache 8)
    (hselected : DoubleBaseContract
      (if state.mem.readAt q.cache 8 = 1 then p.avx2DoubleBase else p.serialDoubleBase)
      layout doubleBase) :
    ∃ after, (program p g).runFrom E 7 state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil,
        after) := by
  rw [dispatch_block p g E state q.cache (state.mem.readAt q.cache 8)
    hregs.cache hregs.one hcache rfl]
  have hchoice : DoubleBaseContract
      (if decide (state.mem.readAt q.cache 8 = 1) then p.avx2DoubleBase
        else p.serialDoubleBase) layout doubleBase := by
    simpa using hselected
  simpa using backend_tail_of_selected_contract p g layout doubleBase compress
    hcompress hcompare (decide (state.mem.readAt q.cache 8 = 1)) hchoice q _ state
    h scalar a r (TailRegisters.dispatch q E hregs (state.mem.readAt q.cache 8)) hmem

/-- A local initializer call needs only to return with the actual backend
inputs still valid. Its return bit and resulting cache byte are unrestricted.
No universal initializer contract or feature-detection correctness is assumed. -/
theorem initialized_tail_of_local_execution {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (q : TailPointers) (E : Env program.Γ) (state initialized : GlobalState)
    (returned : BitVec 1) (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hcall : p.initializeAvx2Cache .nil state =
      .value (.cons (.value returned) .nil, initialized))
    (hregs : TailRegisters q E)
    (hmem : TailMemory q initialized layout h scalar a r)
    (hcache : Fits initialized.mem q.cache 8)
    (hselected : DoubleBaseContract
      (if initialized.mem.readAt q.cache 8 = 1 then p.avx2DoubleBase
        else p.serialDoubleBase) layout doubleBase) :
    ∃ after, (program p g).runFrom E 6 state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil,
        after) := by
  rw [initialize_cache_block p g E state initialized returned hcall]
  exact dispatch_tail_of_selected_contract p g layout doubleBase compress hcompress
    hcompare q _ initialized h scalar a r (TailRegisters.initialize q E hregs returned)
    hmem hcache hselected

end Agave.Ed25519.Verifier.Execution.Dalek
