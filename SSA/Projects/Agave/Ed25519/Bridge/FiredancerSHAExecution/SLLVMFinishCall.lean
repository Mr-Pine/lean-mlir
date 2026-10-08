import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishExecution

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace FinishExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] core finish markerMemory longMemory lastMemory outputMemory word

theorem short_call (p o : Pointer) (s after : GlobalState) (used : Nat)
    (lo hi : BitVec 64) (hn : used < 112) (hr : Fits s.mem p (224*8))
    (hu : word s.mem (p.withOffset 200#64) = BitVec.ofNat 64 used)
    (hlo : word s.mem (p.withOffset 208#64) = lo)
    (hhi : word s.mem (p.withOffset 216#64) = hi)
    (hc : Fits after.mem p (224*8)) (ho : Fits after.mem o (64*8))
    (hcore : StateT.run (runFunction (core.denote
        (.cons (.value 1#64) (.cons (.value p)
          (Ctxt.Valuation.singleton (.value (p.withOffset 128#64)))))))
      {s with mem := lastMemory (markerMemory s.mem p used) p (used+1) lo hi} =
        .value (.nil, after)) :
    StateT.run (runFunction (finish.denote (.cons (.value o) (Ctxt.Valuation.singleton (.value p))))) s =
      .value ([.value o]ₕ, s.popFrame (outputMemory after.mem p o)) :=
  run_runFunction (short_body p o s after used lo hi hn hr hu hlo hhi hc ho hcore)

theorem long_call (p o : Pointer) (s middle after : GlobalState) (used : Nat)
    (lo hi : BitVec 64) (hn : used < 128) (hl : 112 ≤ used) (hr : Fits s.mem p (224*8))
    (hu : word s.mem (p.withOffset 200#64) = BitVec.ofNat 64 used)
    (hlo : word s.mem (p.withOffset 208#64) = lo)
    (hhi : word s.mem (p.withOffset 216#64) = hi)
    (hc : Fits after.mem p (224*8)) (ho : Fits after.mem o (64*8))
    (hmiddle : Fits middle.mem p (224*8))
    (hcoreFirst : StateT.run (runFunction (core.denote
        (.cons (.value 1#64) (.cons (.value p)
          (Ctxt.Valuation.singleton (.value (p.withOffset 128#64)))))))
      {s with mem := longMemory (markerMemory s.mem p used) p used} =
        .value (.nil, middle))
    (hcore : StateT.run (runFunction (core.denote
        (.cons (.value 1#64) (.cons (.value p)
          (Ctxt.Valuation.singleton (.value (p.withOffset 128#64)))))))
      {middle with mem := lastMemory middle.mem p 0 lo hi} =
        .value (.nil, after)) :
    StateT.run (runFunction (finish.denote (.cons (.value o) (Ctxt.Valuation.singleton (.value p))))) s =
      .value ([.value o]ₕ, s.popFrame (outputMemory after.mem p o)) :=
  run_runFunction (long_body p o s middle after used lo hi hn hl hr hu hlo hhi hc ho hmiddle hcoreFirst hcore)

theorem outputMemory_fits {m : MemoryState} {p o q : Pointer} {n : Nat}
    (h : Fits m q n) : Fits (outputMemory m p o) q n := by
  unfold outputMemory outputStep
  repeat apply fits_splice
  exact h

theorem outputMemory_frame (m : MemoryState) (p o : Pointer) (q : BlockId)
    (hne : q ≠ o.id) : (outputMemory m p o).live? q = m.live? q := by
  simp only [outputMemory, outputStep, live?_splice_ne (show (o.withOffset _).id ≠ q from Ne.symm hne)]

theorem markerMemory_frame (m : MemoryState) (p : Pointer) (used : Nat) (q : BlockId)
    (hne : q ≠ p.id) : (markerMemory m p used).live? q = m.live? q := by
  simp only [markerMemory, live?_splice_ne (show (p.withOffset _).id ≠ q from Ne.symm hne)]

theorem longMemory_frame (m : MemoryState) (p : Pointer) (used : Nat) (q : BlockId)
    (hne : q ≠ p.id) : (longMemory m p used).live? q = m.live? q := by
  simp only [longMemory, live?_splice_ne (show (p.withOffset _).id ≠ q from Ne.symm hne)]

theorem lastMemory_frame (m : MemoryState) (p : Pointer) (n : Nat) (lo hi : BitVec 64) (q : BlockId)
    (hne : q ≠ p.id) : (lastMemory m p n lo hi).live? q = m.live? q := by
  simp only [lastMemory, live?_splice_ne (show (p.withOffset _).id ≠ q from Ne.symm hne)]

end FinishExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
