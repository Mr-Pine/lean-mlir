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

def cleanupChunks0Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 533).take 10}

def cleanupChunks0Result (E : Env program.Γ) (s : GlobalState) (p67 p68 p69 p70 p71 : Pointer) (v21 : BitVec 64) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let m1 := m0.storeAt p67 v21
  let m2 := m1.storeAt p68 v21
  let m3 := m2.storeAt p69 v21
  let m4 := m3.storeAt p70 v21
  let m5 := m4.storeAt p71 v21
  (E, {s with mem := m5})

theorem cleanupChunks0_execute (E : Env program.Γ) (s : GlobalState) (p67 p68 p69 p70 p71 : Pointer) (v21 : BitVec 64)
    (hr67 : SmallRange s.mem p67 8)
    (hp67 : E.read (%67) = .value p67)
    (hr68 : SmallRange s.mem p68 8)
    (hp68 : E.read (%68) = .value p68)
    (hr69 : SmallRange s.mem p69 8)
    (hp69 : E.read (%69) = .value p69)
    (hr70 : SmallRange s.mem p70 8)
    (hp70 : E.read (%70) = .value p70)
    (hr71 : SmallRange s.mem p71 8)
    (hp71 : E.read (%71) = .value p71)
    (hv21 : E.read (%21) = .value v21)
    : cleanupChunks0Block.runBodyFrom E 0 s = .value (cleanupChunks0Result E s p67 p68 p69 p70 p71 v21) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      cleanupChunks0Block.runBodyFrom E' 0 S = .value (cleanupChunks0Result E s p67 p68 p69 p70 p71 v21) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf67 : Fits S.mem p67 64 := by rw [hS]; exact hr67.fits
  have hf68 : Fits S.mem p68 64 := by rw [hS]; exact hr68.fits
  have hf69 : Fits S.mem p69 64 := by rw [hS]; exact hr69.fits
  have hf70 : Fits S.mem p70 64 := by rw [hS]; exact hr70.fits
  have hf71 : Fits S.mem p71 64 := by rw [hS]; exact hr71.fits
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_store [hp67, hp68, hp69, hp70, hp71, hv21]
  step_store [hp67, hp68, hp69, hp70, hp71, hv21]
  step_store [hp67, hp68, hp69, hp70, hp71, hv21]
  step_store [hp67, hp68, hp69, hp70, hp71, hv21]
  step_store [hp67, hp68, hp69, hp70, hp71, hv21]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

def cleanupChunks1Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 543).take 16}

def cleanupChunks1Result (E : Env program.Γ) (s : GlobalState) (p67 p68 p69 p70 p71 p90 p91 p92 p93 p94 : Pointer) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let v447 : BitVec 64 := m0.readAt p67 64
  let m1 := m0.storeAt p90 v447
  let v448 : BitVec 64 := m1.readAt p68 64
  let m2 := m1.storeAt p91 v448
  let v449 : BitVec 64 := m2.readAt p69 64
  let m3 := m2.storeAt p92 v449
  let v450 : BitVec 64 := m3.readAt p70 64
  let m4 := m3.storeAt p93 v450
  let v451 : BitVec 64 := m4.readAt p71 64
  let m5 := m4.storeAt p94 v451
  (E[%447 := .value v447][%448 := .value v448][%449 := .value v449][%450 := .value v450][%451 := .value v451], {s with mem := m5})

theorem cleanupChunks1_execute (E : Env program.Γ) (s : GlobalState) (p67 p68 p69 p70 p71 p90 p91 p92 p93 p94 : Pointer)
    (hr67 : SmallRange s.mem p67 8)
    (hp67 : E.read (%67) = .value p67)
    (hr68 : SmallRange s.mem p68 8)
    (hp68 : E.read (%68) = .value p68)
    (hr69 : SmallRange s.mem p69 8)
    (hp69 : E.read (%69) = .value p69)
    (hr70 : SmallRange s.mem p70 8)
    (hp70 : E.read (%70) = .value p70)
    (hr71 : SmallRange s.mem p71 8)
    (hp71 : E.read (%71) = .value p71)
    (hr90 : SmallRange s.mem p90 8)
    (hp90 : E.read (%90) = .value p90)
    (hr91 : SmallRange s.mem p91 8)
    (hp91 : E.read (%91) = .value p91)
    (hr92 : SmallRange s.mem p92 8)
    (hp92 : E.read (%92) = .value p92)
    (hr93 : SmallRange s.mem p93 8)
    (hp93 : E.read (%93) = .value p93)
    (hr94 : SmallRange s.mem p94 8)
    (hp94 : E.read (%94) = .value p94)
    : cleanupChunks1Block.runBodyFrom E 0 s = .value (cleanupChunks1Result E s p67 p68 p69 p70 p71 p90 p91 p92 p93 p94) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      cleanupChunks1Block.runBodyFrom E' 0 S = .value (cleanupChunks1Result E s p67 p68 p69 p70 p71 p90 p91 p92 p93 p94) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf67 : Fits S.mem p67 64 := by rw [hS]; exact hr67.fits
  have hf68 : Fits S.mem p68 64 := by rw [hS]; exact hr68.fits
  have hf69 : Fits S.mem p69 64 := by rw [hS]; exact hr69.fits
  have hf70 : Fits S.mem p70 64 := by rw [hS]; exact hr70.fits
  have hf71 : Fits S.mem p71 64 := by rw [hS]; exact hr71.fits
  have hf90 : Fits S.mem p90 64 := by rw [hS]; exact hr90.fits
  have hf91 : Fits S.mem p91 64 := by rw [hS]; exact hr91.fits
  have hf92 : Fits S.mem p92 64 := by rw [hS]; exact hr92.fits
  have hf93 : Fits S.mem p93 64 := by rw [hS]; exact hr93.fits
  have hf94 : Fits S.mem p94 64 := by rw [hS]; exact hr94.fits
  step_load [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94] inline
  step_store [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94]
  step_load [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94] inline
  step_store [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94]
  step_load [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94] inline
  step_store [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94]
  step_load [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94] inline
  step_store [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94]
  step_load [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94] inline
  step_store [hp67, hp68, hp69, hp70, hp71, hp90, hp91, hp92, hp93, hp94]
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

def cleanupChunks2Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 559).take 18}

def cleanupChunks2Result (E : Env program.Γ) (s : GlobalState) (p81 p82 p83 p84 p85 p86 p87 p88 p89 : Pointer) (v61 : BitVec 128) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let m1 := m0.storeAt p81 v61
  let m2 := m1.storeAt p82 v61
  let m3 := m2.storeAt p83 v61
  let m4 := m3.storeAt p84 v61
  let m5 := m4.storeAt p85 v61
  let m6 := m5.storeAt p86 v61
  let m7 := m6.storeAt p87 v61
  let m8 := m7.storeAt p88 v61
  let m9 := m8.storeAt p89 v61
  (E, {s with mem := m9})

theorem cleanupChunks2_execute (E : Env program.Γ) (s : GlobalState) (p81 p82 p83 p84 p85 p86 p87 p88 p89 : Pointer) (v61 : BitVec 128)
    (hr81 : SmallRange s.mem p81 16)
    (hp81 : E.read (%81) = .value p81)
    (hr82 : SmallRange s.mem p82 16)
    (hp82 : E.read (%82) = .value p82)
    (hr83 : SmallRange s.mem p83 16)
    (hp83 : E.read (%83) = .value p83)
    (hr84 : SmallRange s.mem p84 16)
    (hp84 : E.read (%84) = .value p84)
    (hr85 : SmallRange s.mem p85 16)
    (hp85 : E.read (%85) = .value p85)
    (hr86 : SmallRange s.mem p86 16)
    (hp86 : E.read (%86) = .value p86)
    (hr87 : SmallRange s.mem p87 16)
    (hp87 : E.read (%87) = .value p87)
    (hr88 : SmallRange s.mem p88 16)
    (hp88 : E.read (%88) = .value p88)
    (hr89 : SmallRange s.mem p89 16)
    (hp89 : E.read (%89) = .value p89)
    (hv61 : E.read (%61) = .value v61)
    : cleanupChunks2Block.runBodyFrom E 0 s = .value (cleanupChunks2Result E s p81 p82 p83 p84 p85 p86 p87 p88 p89 v61) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      cleanupChunks2Block.runBodyFrom E' 0 S = .value (cleanupChunks2Result E s p81 p82 p83 p84 p85 p86 p87 p88 p89 v61) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf81 : Fits S.mem p81 128 := by rw [hS]; exact hr81.fits
  have hf82 : Fits S.mem p82 128 := by rw [hS]; exact hr82.fits
  have hf83 : Fits S.mem p83 128 := by rw [hS]; exact hr83.fits
  have hf84 : Fits S.mem p84 128 := by rw [hS]; exact hr84.fits
  have hf85 : Fits S.mem p85 128 := by rw [hS]; exact hr85.fits
  have hf86 : Fits S.mem p86 128 := by rw [hS]; exact hr86.fits
  have hf87 : Fits S.mem p87 128 := by rw [hS]; exact hr87.fits
  have hf88 : Fits S.mem p88 128 := by rw [hS]; exact hr88.fits
  have hf89 : Fits S.mem p89 128 := by rw [hS]; exact hr89.fits
  step_store [hp81, hp82, hp83, hp84, hp85, hp86, hp87, hp88, hp89, hv61]
  step_pure
  step_store [hp81, hp82, hp83, hp84, hp85, hp86, hp87, hp88, hp89, hv61]
  step_pure
  step_store [hp81, hp82, hp83, hp84, hp85, hp86, hp87, hp88, hp89, hv61]
  step_pure
  step_store [hp81, hp82, hp83, hp84, hp85, hp86, hp87, hp88, hp89, hv61]
  step_pure
  step_store [hp81, hp82, hp83, hp84, hp85, hp86, hp87, hp88, hp89, hv61]
  step_pure
  step_store [hp81, hp82, hp83, hp84, hp85, hp86, hp87, hp88, hp89, hv61]
  step_pure
  step_store [hp81, hp82, hp83, hp84, hp85, hp86, hp87, hp88, hp89, hv61]
  step_pure
  step_store [hp81, hp82, hp83, hp84, hp85, hp86, hp87, hp88, hp89, hv61]
  step_pure
  step_store [hp81, hp82, hp83, hp84, hp85, hp86, hp87, hp88, hp89, hv61]
  step_pure
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

def cleanupChunks3Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 577).take 10}

def cleanupChunks3Result (E : Env program.Γ) (s : GlobalState) (p62 p63 p64 p65 p66 : Pointer) (v21 : BitVec 64) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let m1 := m0.storeAt p62 v21
  let m2 := m1.storeAt p63 v21
  let m3 := m2.storeAt p64 v21
  let m4 := m3.storeAt p65 v21
  let m5 := m4.storeAt p66 v21
  (E, {s with mem := m5})

theorem cleanupChunks3_execute (E : Env program.Γ) (s : GlobalState) (p62 p63 p64 p65 p66 : Pointer) (v21 : BitVec 64)
    (hr62 : SmallRange s.mem p62 8)
    (hp62 : E.read (%62) = .value p62)
    (hr63 : SmallRange s.mem p63 8)
    (hp63 : E.read (%63) = .value p63)
    (hr64 : SmallRange s.mem p64 8)
    (hp64 : E.read (%64) = .value p64)
    (hr65 : SmallRange s.mem p65 8)
    (hp65 : E.read (%65) = .value p65)
    (hr66 : SmallRange s.mem p66 8)
    (hp66 : E.read (%66) = .value p66)
    (hv21 : E.read (%21) = .value v21)
    : cleanupChunks3Block.runBodyFrom E 0 s = .value (cleanupChunks3Result E s p62 p63 p64 p65 p66 v21) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      cleanupChunks3Block.runBodyFrom E' 0 S = .value (cleanupChunks3Result E s p62 p63 p64 p65 p66 v21) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf62 : Fits S.mem p62 64 := by rw [hS]; exact hr62.fits
  have hf63 : Fits S.mem p63 64 := by rw [hS]; exact hr63.fits
  have hf64 : Fits S.mem p64 64 := by rw [hS]; exact hr64.fits
  have hf65 : Fits S.mem p65 64 := by rw [hS]; exact hr65.fits
  have hf66 : Fits S.mem p66 64 := by rw [hS]; exact hr66.fits
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_store [hp62, hp63, hp64, hp65, hp66, hv21]
  step_store [hp62, hp63, hp64, hp65, hp66, hv21]
  step_store [hp62, hp63, hp64, hp65, hp66, hv21]
  step_store [hp62, hp63, hp64, hp65, hp66, hv21]
  step_store [hp62, hp63, hp64, hp65, hp66, hv21]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

def cleanupChunks4Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 587).take 10}

def cleanupChunks4Result (E : Env program.Γ) (s : GlobalState) (p62 p63 p64 p65 p66 p76 p77 p78 p79 p80 : Pointer) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  let v452 : BitVec 64 := m0.readAt p62 64
  let m1 := m0.storeAt p76 v452
  let v453 : BitVec 64 := m1.readAt p63 64
  let m2 := m1.storeAt p77 v453
  let v454 : BitVec 64 := m2.readAt p64 64
  let m3 := m2.storeAt p78 v454
  let v455 : BitVec 64 := m3.readAt p65 64
  let m4 := m3.storeAt p79 v455
  let v456 : BitVec 64 := m4.readAt p66 64
  let m5 := m4.storeAt p80 v456
  (E[%452 := .value v452][%453 := .value v453][%454 := .value v454][%455 := .value v455][%456 := .value v456], {s with mem := m5})

theorem cleanupChunks4_execute (E : Env program.Γ) (s : GlobalState) (p62 p63 p64 p65 p66 p76 p77 p78 p79 p80 : Pointer)
    (hr62 : SmallRange s.mem p62 8)
    (hp62 : E.read (%62) = .value p62)
    (hr63 : SmallRange s.mem p63 8)
    (hp63 : E.read (%63) = .value p63)
    (hr64 : SmallRange s.mem p64 8)
    (hp64 : E.read (%64) = .value p64)
    (hr65 : SmallRange s.mem p65 8)
    (hp65 : E.read (%65) = .value p65)
    (hr66 : SmallRange s.mem p66 8)
    (hp66 : E.read (%66) = .value p66)
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
    : cleanupChunks4Block.runBodyFrom E 0 s = .value (cleanupChunks4Result E s p62 p63 p64 p65 p66 p76 p77 p78 p79 p80) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      cleanupChunks4Block.runBodyFrom E' 0 S = .value (cleanupChunks4Result E s p62 p63 p64 p65 p66 p76 p77 p78 p79 p80) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf62 : Fits S.mem p62 64 := by rw [hS]; exact hr62.fits
  have hf63 : Fits S.mem p63 64 := by rw [hS]; exact hr63.fits
  have hf64 : Fits S.mem p64 64 := by rw [hS]; exact hr64.fits
  have hf65 : Fits S.mem p65 64 := by rw [hS]; exact hr65.fits
  have hf66 : Fits S.mem p66 64 := by rw [hS]; exact hr66.fits
  have hf76 : Fits S.mem p76 64 := by rw [hS]; exact hr76.fits
  have hf77 : Fits S.mem p77 64 := by rw [hS]; exact hr77.fits
  have hf78 : Fits S.mem p78 64 := by rw [hS]; exact hr78.fits
  have hf79 : Fits S.mem p79 64 := by rw [hS]; exact hr79.fits
  have hf80 : Fits S.mem p80 64 := by rw [hS]; exact hr80.fits
  step_load [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80] inline
  step_store [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80]
  step_load [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80] inline
  step_store [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80]
  step_load [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80] inline
  step_store [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80]
  step_load [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80] inline
  step_store [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80]
  step_load [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80] inline
  step_store [hp62, hp63, hp64, hp65, hp66, hp76, hp77, hp78, hp79, hp80]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

def cleanupChunks5Block : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 597).take 25}

def cleanupChunks5Result (E : Env program.Γ) (s : GlobalState) :
    Env program.Γ × GlobalState :=
  let m0 := s.mem
  (E, {s with mem := m0})

theorem cleanupChunks5_execute (E : Env program.Γ) (s : GlobalState)
    : cleanupChunks5Block.runBodyFrom E 0 s = .value (cleanupChunks5Result E s ) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      cleanupChunks5Block.runBodyFrom E' 0 S = .value (cleanupChunks5Result E s ) by
    exact this E rfl s rfl
  intro E' hE S hS
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
