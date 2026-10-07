import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Program
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Exact scratch-memory instruction slices. Loaded values are retained from
the actual intermediate memory; no disjointness or zero-load shortcut is assumed. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def subtractStores0Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 400).take 5}

def subtractStores0Result (E : Env program.Γ) (s : GlobalState) (p76 p77 p78 p79 p80 : Pointer) (v332 : BitVec 64) (v337 : BitVec 64) (v342 : BitVec 64) (v345 : BitVec 64) (v350 : BitVec 64) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let m1 := m0.storeAt p76 v332
  let m2 := m1.storeAt p77 v337
  let m3 := m2.storeAt p78 v342
  let m4 := m3.storeAt p79 v345
  let m5 := m4.storeAt p80 v350
  (E, {s with mem := m5})

theorem subtractStores0_execute (E : Env program.Γ) (s : GlobalState) (p76 p77 p78 p79 p80 : Pointer) (v332 : BitVec 64) (v337 : BitVec 64) (v342 : BitVec 64) (v345 : BitVec 64) (v350 : BitVec 64)
    (hr76 : SmallRange s.mem p76 8)
    (hp76 : E.read (%76) = .value p76)
    (hr77 : SmallRange s.mem p77 8)
    (hp77 : E.read (%77) = .value p77)
    (hr78 : SmallRange s.mem p78 8)
    (hp78 : E.read (%78) = .value p78)
    (hr79 : SmallRange s.mem p79 8)
    (hp79 : E.read (%79) = .value p79)
    (hr80 : SmallRange s.mem p80 8)
    (hp80 : E.read (%80) = .value p80)
    (hv332 : E.read (%332) = .value v332)
    (hv337 : E.read (%337) = .value v337)
    (hv342 : E.read (%342) = .value v342)
    (hv345 : E.read (%345) = .value v345)
    (hv350 : E.read (%350) = .value v350)
    : subtractStores0Block.runBodyFrom E 0 s = .value (subtractStores0Result E s p76 p77 p78 p79 p80 v332 v337 v342 v345 v350) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      subtractStores0Block.runBodyFrom E' 0 S = .value (subtractStores0Result E s p76 p77 p78 p79 p80 v332 v337 v342 v345 v350) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf76 : Fits S.mem p76 64 := by rw [hS]; exact hr76.fits
  have hf77 : Fits S.mem p77 64 := by rw [hS]; exact hr77.fits
  have hf78 : Fits S.mem p78 64 := by rw [hS]; exact hr78.fits
  have hf79 : Fits S.mem p79 64 := by rw [hS]; exact hr79.fits
  have hf80 : Fits S.mem p80 64 := by rw [hS]; exact hr80.fits
  step_store [hp76, hp77, hp78, hp79, hp80, hv332, hv337, hv342, hv345, hv350]
  step_store [hp76, hp77, hp78, hp79, hp80, hv332, hv337, hv342, hv345, hv350]
  step_store [hp76, hp77, hp78, hp79, hp80, hv332, hv337, hv342, hv345, hv350]
  step_store [hp76, hp77, hp78, hp79, hp80, hv332, hv337, hv342, hv345, hv350]
  step_store [hp76, hp77, hp78, hp79, hp80, hv332, hv337, hv342, hv345, hv350]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
