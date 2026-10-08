import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageResult
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendZero

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace MessageExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] append core

/-- All paths of the actual third append, with only the independently proved
real-core execution theorem supplied as a parameter. -/
theorem body
    (hCore : ∀ (s : GlobalState) (kp chain data : Pointer) (count : BitVec 64),
      Core.Ready s kp chain data count → Core.Executes s chain data count)
    (s : GlobalState) (p data kp : Pointer) (n : BitVec 64)
    (h : Ready s p data kp n)
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    ∃ after : GlobalState,
      StateT.run (append.denote
        (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ)) s =
        .value ([.value p]ₕ, after) ∧ after ≈ resultState s p data n := by
  by_cases hz : n = 0#64
  · subst n
    refine ⟨s, append_zero_body p (.value data) s, ?_⟩
    simpa only [resultState, ↓reduceIte] using GlobalState.Equiv.refl s
  by_cases hshort : n.toNat < 64
  · have hn : 0 < n.toNat := by
      have hnn : n.toNat ≠ 0 := by intro hh; apply hz; exact BitVec.eq_of_toNat_eq hh
      omega
    refine ⟨{s with mem := appendMessageShortMemory s.mem p data n},
      append_message_short_body p data s n hn hshort h.contextRange.fits h.messageRange.fits hcount, ?_⟩
    simp only [resultState, hz, hshort, ↓reduceIte]
    exact GlobalState.Equiv.refl _
  have hn64 : 64 ≤ n.toNat := by omega
  let filled := {s with mem := appendMessageFilledMemory s.mem p data n}
  obtain ⟨first, hfirst, hfirstwf, hfirstalloc, hfirstglobals, hfirstmem⟩ :=
    hCore filled kp (p.withOffset 128#64) p 1#64 h.filled.buffered_core
  have hfirstReady : Ready first p data kp n :=
    h.filled.after_core hfirstwf hfirstglobals hfirstmem
  have hfirstEq : first ≈ coreState filled p p 1#64 :=
    ⟨hfirstalloc, hfirstglobals, hfirstmem⟩
  by_cases he : n = 64#64
  · subst n
    refine ⟨{first with mem := first.mem.splice (p.withOffset 200#64) (0#64)},
      append_message_fill_body p data s first h.contextRange.fits h.messageRange.fits
        hcount hfirstReady.contextRange.fits hfirst, ?_⟩
    simpa only [resultState, hz, hshort, ↓reduceIte] using
      (splice_equiv (p := p.withOffset 200#64) (x := 0#64) hfirstEq)
  have hn64lt : 64 < n.toNat := by
    have hnne : n.toNat ≠ 64 := by intro hh; apply he; exact BitVec.eq_of_toNat_eq hh
    omega
  by_cases htail : n.toNat < 192
  · refine ⟨{first with mem := appendMessageTailMemory first.mem p (data.withOffset 64#64) (n - 64#64)},
      append_message_fill_tail_body p data s first n hn64lt htail h.contextRange.fits
        h.messageRange.fits hcount hfirstReady.contextRange.fits
        (hfirstReady.rest_range hn64).fits hfirst, ?_⟩
    simpa only [resultState, hz, hshort, he, htail, ↓reduceIte] using
      tailMemory_congr hfirstEq p (data.withOffset 64#64) (n - 64#64)
  have hlong : 192 ≤ n.toNat := by omega
  let reset := {first with mem := first.mem.splice (p.withOffset 200#64) (0#64)}
  have hreset : Ready reset p data kp n := hfirstReady.store _ _
  obtain ⟨bulk, hbulk, hbulkwf, hbulkalloc, hbulkglobals, hbulkmem⟩ :=
    hCore reset kp (p.withOffset 128#64) (data.withOffset 64#64) ((n - 64#64) >>> (7 : Nat))
      (hreset.direct_core hlong)
  have hbulkReady : Ready bulk p data kp n :=
    hreset.after_core hbulkwf hbulkglobals hbulkmem
  have hbulkEq : bulk ≈ coreState reset p (data.withOffset 64#64) ((n - 64#64) >>> (7 : Nat)) :=
    ⟨hbulkalloc, hbulkglobals, hbulkmem⟩
  have hresetEq := splice_equiv (p := p.withOffset 200#64) (x := 0#64) hfirstEq
  refine ⟨{bulk with mem := appendMessageDirectTailMemory bulk.mem p (data.withOffset 64#64) (n - 64#64)},
    append_message_direct_body p data s first bulk n hlong h.contextRange.fits h.messageRange.fits
      hcount hfirstReady.contextRange.fits hbulkReady.contextRange.fits (hbulkReady.tail_fits hn64)
      hfirst hbulk, ?_⟩
  have hfinal := directTailMemory_congr
    (hbulkEq.trans (coreState_congr hresetEq p (data.withOffset 64#64) ((n - 64#64) >>> (7 : Nat))))
    p (data.withOffset 64#64) (n - 64#64)
  simpa only [resultState, hz, hshort, he, htail, ↓reduceIte] using hfinal

/-- Actual function execution with exact canonical live memory, allocator and
symbol-table restoration, well-formedness, and the complete off-context frame. -/
theorem call
    (hCore : ∀ (s : GlobalState) (kp chain data : Pointer) (count : BitVec 64),
      Core.Ready s kp chain data count → Core.Executes s chain data count)
    (s : GlobalState) (p data kp : Pointer) (n : BitVec 64)
    (h : Ready s p data kp n)
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      after.WF ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ q, after.mem.live? q = (resultState s p data n).mem.live? q) ∧
      (∀ q, q ≠ p.id → after.mem.live? q = s.mem.live? q) := by
  obtain ⟨out, hout, heq⟩ := body hCore s p data kp n h hcount
  have hwf := resultState_wf s p data n h.wf h.contextRange.fits
  have hf : ∀ q, (s.popFrame out.mem).mem.live? q = (resultState s p data n).mem.live? q := by
    intro q
    change (out.mem.killFrom s.alloc.nextFreeBlock).live? q = _
    by_cases hlt : q.id < s.alloc.nextFreeBlock
    · rw [live?_killFrom_of_lt hlt]
      exact heq.live q
    · rw [live?_killFrom_of_le (by omega), hwf q (by rw [resultState_alloc]; omega)]
  refine ⟨s.popFrame out.mem, run_runFunction hout, ?_, rfl, rfl, hf, ?_⟩
  · intro q hq
    exact live?_killFrom_of_le hq
  · intro q hq
    exact (hf q).trans (resultState_other s p data n q hq)

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
