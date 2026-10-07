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

def unpackScratch0Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 146).take 1}

def unpackScratch0Result (E : Env program.Γ) (s : GlobalState) (p73 : Pointer) (v134 : BitVec 64) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let m1 := m0.storeAt p73 v134
  (E, {s with mem := m1})

theorem unpackScratch0_execute (E : Env program.Γ) (s : GlobalState) (p73 : Pointer) (v134 : BitVec 64)
    (hr73 : SmallRange s.mem p73 8)
    (hp73 : E.read (%73) = .value p73)
    (hv134 : E.read (%134) = .value v134)
    : unpackScratch0Block.runBodyFrom E 0 s = .value (unpackScratch0Result E s p73 v134) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      unpackScratch0Block.runBodyFrom E' 0 S = .value (unpackScratch0Result E s p73 v134) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf73 : Fits S.mem p73 64 := by rw [hS]; exact hr73.fits
  step_store [hp73, hv134]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

def unpackScratch1Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 165).take 1}

def unpackScratch1Result (E : Env program.Γ) (s : GlobalState) (p74 : Pointer) (v152 : BitVec 64) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let m1 := m0.storeAt p74 v152
  (E, {s with mem := m1})

theorem unpackScratch1_execute (E : Env program.Γ) (s : GlobalState) (p74 : Pointer) (v152 : BitVec 64)
    (hr74 : SmallRange s.mem p74 8)
    (hp74 : E.read (%74) = .value p74)
    (hv152 : E.read (%152) = .value v152)
    : unpackScratch1Block.runBodyFrom E 0 s = .value (unpackScratch1Result E s p74 v152) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      unpackScratch1Block.runBodyFrom E' 0 S = .value (unpackScratch1Result E s p74 v152) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf74 : Fits S.mem p74 64 := by rw [hS]; exact hr74.fits
  step_store [hp74, hv152]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

def unpackScratch2Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 184).take 1}

def unpackScratch2Result (E : Env program.Γ) (s : GlobalState) (p75 : Pointer) (v170 : BitVec 64) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let m1 := m0.storeAt p75 v170
  (E, {s with mem := m1})

theorem unpackScratch2_execute (E : Env program.Γ) (s : GlobalState) (p75 : Pointer) (v170 : BitVec 64)
    (hr75 : SmallRange s.mem p75 8)
    (hp75 : E.read (%75) = .value p75)
    (hv170 : E.read (%170) = .value v170)
    : unpackScratch2Block.runBodyFrom E 0 s = .value (unpackScratch2Result E s p75 v170) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      unpackScratch2Block.runBodyFrom E' 0 S = .value (unpackScratch2Result E s p75 v170) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf75 : Fits S.mem p75 64 := by rw [hS]; exact hr75.fits
  step_store [hp75, hv170]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

def unpackScratch3Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 185).take 8}

def unpackScratch3Result (E : Env program.Γ) (s : GlobalState) (p72 p73 p74 p75 : Pointer) (v21 : BitVec 64) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let m1 := m0.storeAt p72 v21
  let m2 := m1.storeAt p73 v21
  let m3 := m2.storeAt p74 v21
  let m4 := m3.storeAt p75 v21
  (E, {s with mem := m4})

theorem unpackScratch3_execute (E : Env program.Γ) (s : GlobalState) (p72 p73 p74 p75 : Pointer) (v21 : BitVec 64)
    (hr72 : SmallRange s.mem p72 8)
    (hp72 : E.read (%72) = .value p72)
    (hr73 : SmallRange s.mem p73 8)
    (hp73 : E.read (%73) = .value p73)
    (hr74 : SmallRange s.mem p74 8)
    (hp74 : E.read (%74) = .value p74)
    (hr75 : SmallRange s.mem p75 8)
    (hp75 : E.read (%75) = .value p75)
    (hv21 : E.read (%21) = .value v21)
    : unpackScratch3Block.runBodyFrom E 0 s = .value (unpackScratch3Result E s p72 p73 p74 p75 v21) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      unpackScratch3Block.runBodyFrom E' 0 S = .value (unpackScratch3Result E s p72 p73 p74 p75 v21) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf72 : Fits S.mem p72 64 := by rw [hS]; exact hr72.fits
  have hf73 : Fits S.mem p73 64 := by rw [hS]; exact hr73.fits
  have hf74 : Fits S.mem p74 64 := by rw [hS]; exact hr74.fits
  have hf75 : Fits S.mem p75 64 := by rw [hS]; exact hr75.fits
  step_store [hp72, hp73, hp74, hp75, hv21]
  step_pure
  step_store [hp72, hp73, hp74, hp75, hv21]
  step_pure
  step_store [hp72, hp73, hp74, hp75, hv21]
  step_pure
  step_store [hp72, hp73, hp74, hp75, hv21]
  step_pure
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
