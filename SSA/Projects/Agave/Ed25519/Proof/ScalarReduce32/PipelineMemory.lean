import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Subtract
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductPhase

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

theorem unpackPhase_live (E : Env program.Γ) (s : GlobalState) (a q : Pointer)
    (scratch : Fin 4 → Pointer) (count : Nat) (h : SmallRange s.mem q count) :
    SmallRange (unpackPhaseResult E s a scratch).2.mem q count := by
  dsimp only [unpackPhaseResult, unpackScratch0Result, unpackScratch1Result,
    unpackScratch2Result, unpackScratch3Result]
  repeat' apply SmallRange.storeAt
  exact h

theorem unpackPhase_wf (E : Env program.Γ) (s : GlobalState) (a : Pointer)
    (scratch : Fin 4 → Pointer) (h : s.WF) :
    (unpackPhaseResult E s a scratch).2.WF := by
  simpa only [unpackPhaseResult, unpackScratch0Result, unpackScratch1Result,
    unpackScratch2Result, unpackScratch3Result, GlobalState.WF_storeAt] using h

theorem productPhase_live (s : GlobalState) (x : Fin 5 → BitVec 64)
    (scratch : Fin 9 → Pointer) (q : Pointer) (count : Nat) (h : SmallRange s.mem q count) :
    SmallRange (productPhaseState s x scratch).mem q count := by
  dsimp only [productPhaseState]
  repeat' apply SmallRange.storeAt
  exact h

theorem productPhase_wf (s : GlobalState) (x : Fin 5 → BitVec 64)
    (scratch : Fin 9 → Pointer) (h : s.WF) :
    (productPhaseState s x scratch).WF := by
  simpa only [productPhaseState, GlobalState.WF_storeAt] using h

theorem subtractState_live (s : GlobalState) (x : Fin 5 → BitVec 52)
    (scratch : Fin 5 → Pointer) (q : Pointer) (count : Nat) (h : SmallRange s.mem q count) :
    SmallRange (subtractState s x scratch).mem q count := by
  dsimp only [subtractState]
  repeat' apply SmallRange.storeAt
  exact h

end Agave.Ed25519.ScalarReduce32.Execution
