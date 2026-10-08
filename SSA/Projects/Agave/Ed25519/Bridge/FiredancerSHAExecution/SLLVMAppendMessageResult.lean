import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageDirect
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageReady

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace MessageExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] core append Core.result sourceRead

/-- Canonical caller-visible effect of the actual core at the context's chain. -/
def coreState (s : GlobalState) (p data : Pointer) (count : BitVec 64) : GlobalState :=
  {s with mem := s.mem.splice (p.withOffset 128#64) (Core.result s (p.withOffset 128#64) data count)}

/-- A source-memory specification of the third append's concrete branch effects.
This is only a pure state transformer; actual execution is proved separately. -/
def resultState (s : GlobalState) (p data : Pointer) (n : BitVec 64) : GlobalState :=
  if n = 0#64 then s else if n.toNat < 64 then
    {s with mem := appendMessageShortMemory s.mem p data n}
  else
    let first := coreState {s with mem := appendMessageFilledMemory s.mem p data n} p p 1#64
    if n = 64#64 then {first with mem := first.mem.splice (p.withOffset 200#64) (0#64)}
    else if n.toNat < 192 then
      {first with mem := appendMessageTailMemory first.mem p (data.withOffset 64#64) (n - 64#64)}
    else
      let reset := {first with mem := first.mem.splice (p.withOffset 200#64) (0#64)}
      let bulk := coreState reset p (data.withOffset 64#64) ((n - 64#64) >>> (7 : Nat))
      {bulk with mem := appendMessageDirectTailMemory bulk.mem p (data.withOffset 64#64) (n - 64#64)}

theorem coreState_congr {s t : GlobalState} (h : s ≈ t) (p data : Pointer) (count : BitVec 64) :
    coreState s p data count ≈ coreState t p data count := by
  have hc : Core.result s (p.withOffset 128#64) data count = Core.result t (p.withOffset 128#64) data count := by
    simp only [Core.result, Core.readBytes, Core.readBits_of_live_eq (h.live _)]
  unfold coreState
  rw [hc]
  exact splice_equiv h

theorem tailMemory_congr {s t : GlobalState} (h : s ≈ t) (p data : Pointer) (tail : BitVec 64) :
    ({s with mem := appendMessageTailMemory s.mem p data tail} : GlobalState) ≈
    {t with mem := appendMessageTailMemory t.mem p data tail} := by
  have h0 := splice_equiv (p := p.withOffset 200#64) (x := 0#64) h
  have hr := sourceRead_of_live_eq (w := 8 * tail.toNat) (p := data) (h0.live data.id)
  dsimp only [appendMessageTailMemory] at *
  rw [hr]
  exact splice_equiv (splice_equiv h0)

theorem directTailMemory_congr {s t : GlobalState} (h : s ≈ t) (p data : Pointer) (size : BitVec 64) :
    ({s with mem := appendMessageDirectTailMemory s.mem p data size} : GlobalState) ≈
    {t with mem := appendMessageDirectTailMemory t.mem p data size} := by
  dsimp only [appendMessageDirectTailMemory]
  split
  · exact h
  · have hr := sourceRead_of_live_eq (w := 8 * (size &&& 127#64).toNat)
      (p := data.withOffset (size &&& 18446744073709551488#64)) (h.live data.id)
    rw [hr]
    exact splice_equiv (splice_equiv h)

theorem filledMemory_other (m : MemoryState) (p data : Pointer) (n : BitVec 64)
    (q : BlockId) (hne : q ≠ p.id) :
    (appendMessageFilledMemory m p data n).live? q = m.live? q := by
  simp only [appendMessageFilledMemory,
    live?_splice_ne (show (p.withOffset _).id ≠ q from Ne.symm hne)]

theorem tailMemory_other (m : MemoryState) (p data : Pointer) (n : BitVec 64)
    (q : BlockId) (hne : q ≠ p.id) :
    (appendMessageTailMemory m p data n).live? q = m.live? q := by
  simp only [appendMessageTailMemory, live?_splice_ne (Ne.symm hne),
    live?_splice_ne (show (p.withOffset _).id ≠ q from Ne.symm hne)]

theorem directTailMemory_other (m : MemoryState) (p data : Pointer) (n : BitVec 64)
    (q : BlockId) (hne : q ≠ p.id) :
    (appendMessageDirectTailMemory m p data n).live? q = m.live? q := by
  dsimp only [appendMessageDirectTailMemory]
  split
  · rfl
  · simp only [live?_splice_ne (Ne.symm hne),
      live?_splice_ne (show (p.withOffset _).id ≠ q from Ne.symm hne)]

theorem resultState_other (s : GlobalState) (p data : Pointer) (n : BitVec 64)
    (q : BlockId) (hne : q ≠ p.id) :
    (resultState s p data n).mem.live? q = s.mem.live? q := by
  dsimp only [resultState]
  split_ifs <;> simp only [appendMessageShortMemory_other _ _ _ _ _ hne,
    coreState, directTailMemory_other _ _ _ _ _ hne, tailMemory_other _ _ _ _ _ hne,
    filledMemory_other _ _ _ _ _ hne,
    live?_splice_ne (show (p.withOffset _).id ≠ q from Ne.symm hne)]

theorem resultState_alloc (s : GlobalState) (p data : Pointer) (n : BitVec 64) :
    (resultState s p data n).alloc = s.alloc := by simp only [resultState, coreState]; split_ifs <;> rfl

theorem resultState_globals (s : GlobalState) (p data : Pointer) (n : BitVec 64) :
    (resultState s p data n).globals = s.globals := by simp only [resultState, coreState]; split_ifs <;> rfl

theorem resultState_wf (s : GlobalState) (p data : Pointer) (n : BitVec 64)
    (hwf : s.WF) (hr : Fits s.mem p (224 * 8)) : (resultState s p data n).WF := by
  intro q hq
  have hp := lt_nextFreeBlock_of_fits hwf hr
  have halloc := resultState_alloc s p data n
  have hne : q ≠ p.id := by intro hh; subst q; rw [halloc] at hq; omega
  rw [resultState_other s p data n q hne]
  exact hwf q (by rw [halloc] at hq; exact hq)

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
