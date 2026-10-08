import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishObservation
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishOutputMemory

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Reduce64.Execution
namespace FinishObservation
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def outputWords (m : MemoryState) (o : Pointer) (s : State) : MemoryState :=
  let m := m.splice o (bswapBV s.a)
  let m := m.splice (o.withOffset 8#64) (bswapBV s.b)
  let m := m.splice (o.withOffset 16#64) (bswapBV s.c)
  let m := m.splice (o.withOffset 24#64) (bswapBV s.d)
  let m := m.splice (o.withOffset 32#64) (bswapBV s.e)
  let m := m.splice (o.withOffset 40#64) (bswapBV s.f)
  let m := m.splice (o.withOffset 48#64) (bswapBV s.g)
  m.splice (o.withOffset 56#64) (bswapBV s.h)

theorem sourceRead_splice_ne (m : MemoryState) (p q : Pointer) (v : BitVec w) (n : Nat)
    (hne : q.id ≠ p.id) : sourceRead (m.splice q v) p n = sourceRead m p n := by
  simp only [sourceRead, live?_splice_ne hne]

theorem outputMemory_static (m : MemoryState) (p o : Pointer) (hne : o.id ≠ p.id) :
    FinishExecution.outputMemory m p o = outputWords m o (sourceReadState m p) := by
  simp only [FinishExecution.outputMemory, FinishExecution.outputStep, word_sourceRead,
    sourceRead_splice_ne _ _ _ _ _ (show (o.withOffset _).id ≠ (p.withOffset _).id from hne)]
  simp [outputWords, sourceReadState, Pointer.withOffset]

theorem Observed.outputWords {m : MemoryState} {o : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m o r q) (s : State) :
    Observed (outputWords m o s) o (Finish.outputMemory r q s) q := by
  have hx := (((((((h.splice 0#64 (bswapBV s.a)).splice 8#64 (bswapBV s.b)).splice 16#64
    (bswapBV s.c)).splice 24#64 (bswapBV s.d)).splice 32#64 (bswapBV s.e)).splice 40#64
    (bswapBV s.f)).splice 48#64 (bswapBV s.g)).splice 56#64 (bswapBV s.h)
  have hswap (x : Word) : bswapBV x = Agave.Ed25519.Verifier.Execution.SHA512Finalization.swapBytes x := rfl
  simpa [FinishObservation.outputWords, Finish.outputMemory, Pointer.withOffset, hswap] using hx

theorem output_word (m : MemoryState) (p o : Pointer) (r : RIR.MemoryState) (q : RIR.Pointer)
    (h : Observed m o r q) (hr : SmallRange r q 64) (hne : o.id ≠ p.id) :
    sourceRead (FinishExecution.outputMemory m p o) o 512 =
      serialize (pack (sourceReadState m p)) := by
  rw [outputMemory_static m p o hne, (h.outputWords _).read 512,
    Finish.outputMemory_eq r q hr]
  exact RIR.MemoryState.readAt_storeAt_self hr.fits _

end FinishObservation
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
