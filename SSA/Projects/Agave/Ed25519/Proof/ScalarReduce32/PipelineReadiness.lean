import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PipelineMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackingWords
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Pipeline
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Output
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StartupWitnesses
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackRegisters

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Verifier.Execution
open ScalarMontgomeryMul
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Explicit pointer, product, subtraction, and byte witnesses. -/
def wordPipelineData (s : GlobalState) (bits : BitVec 256)
    (quotient : Fin 5 → BitVec 52) : PipelineData where
  scratch := startupScratch s
  inputWords := inputWords bits
  products := reductionProducts (inputWords bits)
  quotient := quotient
  packingWords := reductionPackingWords quotient
  bytes := reductionBytes (reductionPackingWords quotient)

/-- Five normalized values at the exact carry/subtraction boundary. -/
structure QuotientRegisters (E : Env program.Γ) (x : Fin 5 → BitVec 52) : Prop where
  x0 : E.read (%286) = .value ((x 0).setWidth 64)
  x1 : E.read (%294) = .value ((x 1).setWidth 64)
  x2 : E.read (%300) = .value ((x 2).setWidth 64)
  x3 : E.read (%306) = .value ((x 3).setWidth 64)
  x4 : E.read (%308) = .value ((x 4).setWidth 64)

/-- Structural caller invariants, separated from the quotient arithmetic. -/
theorem wordPipelineData_ready (out input : Pointer) (s : GlobalState) (bits : BitVec 256)
    (hwf : s.WF) (hout : SmallRange s.mem out 32) (hin : Dalek.ReadBytes s input 32 bits)
    (quotient : Fin 5 → BitVec 52)
    (hquotient : ∀ E, QuotientRegisters
      (montgomeryPhaseEnv E (reductionProducts (inputWords bits))) quotient) :
    PipelineReady out input s (wordPipelineData s bits quotient) := by
  let d := wordPipelineData s bits quotient
  let q := pipelineStages out input s d
  have hs : ∀ i, SmallRange (q 2).2.mem (d.scratch i) (allocationSize i.val) := by
    intro i
    simp only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9]
    exact startupScratch_live s hwf i
  have hi : SmallRange (q 2).2.mem input 32 := by
    simp only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9]
    exact allocationStates_smallRange s hwf input 32 hin.1 33
  have hir : (q 2).2.mem.readAt input 256 = bits := by
    simp only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9]
    change (allocationStates s 33).mem.readAt input 256 = bits
    rw [allocationStates_read s hwf input 256 hin.1 33]
    exact hin.2
  have hun : InputWordRegisters (q 3).1 (inputWords bits) := by
    simp only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9]
    apply unpack_registers _ _ input d.unpackScratch bits hi hir
    intro i
    exact startupScratch_ne_caller s hwf input hin.1.fits _
  have huLive : ∀ (p : Pointer) (count : Nat), SmallRange (q 2).2.mem p count →
      SmallRange (q 3).2.mem p count := by
    intro p count h
    simp only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] at h ⊢
    exact unpackPhase_live _ _ _ _ _ _ h
  have hpLive : ∀ (p : Pointer) (count : Nat), SmallRange (q 3).2.mem p count →
      SmallRange (q 5).2.mem p count := by
    intro p count h
    simp only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] at h ⊢
    exact productPhase_live _ _ _ _ _ h
  have hsubLive : ∀ (p : Pointer) (count : Nat), SmallRange (q 5).2.mem p count →
      SmallRange (q 7).2.mem p count := by
    intro p count h
    simp only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] at h ⊢
    exact subtractState_live _ _ _ _ _ h
  have hm := hquotient (q 4).1
  simp only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9]
    at hs hi hir hun huLive hpLive hsubLive hm
  change PipelineReady out input s d
  refine {
    unpackRegisters := ?_
    inputLive := hi
    unpackLive := ?_
    productRegisters := ?_
    inputBounds := inputWords_bound bits
    productLive := ?_
    montgomeryRegisters := ?_
    productBounds := reductionProducts_bound (inputWords bits) (inputWords_bound bits)
    subtractRegisters := ?_
    subtractWF := ?_
    subtractLive := ?_
    packRegisters := ?_
    outputLive := ?_
    outputRegister := ?_
    storeRegisters := ?_
    cleanupRegisters := ?_
    cleanupLive := ?_ }
  all_goals simp only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9]
  · exact startup_unpackReady out input s
  · intro i
    change SmallRange (allocationStates s 33).mem
      (startupScratch s ⟨10 + i.val, by omega⟩) 8
    have h := startupScratch_live s hwf ⟨10 + i.val, by omega⟩
    simpa [allocationSize, show ¬ (19 ≤ 10 + i.val ∧ 10 + i.val < 28) by omega,
      ↓reduceIte] using h
  · constructor
    · exact hun.x0
    · exact hun.x1
    · exact hun.x2
    · exact hun.x3
    · exact hun.x4
    all_goals rfl
  · intro i
    apply huLive
    change SmallRange (allocationStates s 33).mem
      (startupScratch s ⟨19 + i.val, by omega⟩) 16
    have h := startupScratch_live s hwf ⟨19 + i.val, by omega⟩
    simpa [allocationSize, show 19 ≤ 19 + i.val ∧ 19 + i.val < 28 by omega,
      ↓reduceIte] using h
  · constructor <;> rfl
  · constructor
    · exact hm.x0
    · exact hm.x1
    · exact hm.x2
    · exact hm.x3
    · exact hm.x4
    all_goals rfl
  · apply productPhase_wf
    apply unpackPhase_wf
    exact allocationStates_wf s hwf 33
  · intro i
    apply hpLive
    apply huLive
    change SmallRange (allocationStates s 33).mem
      (startupScratch s ⟨14 + i.val, by omega⟩) 8
    have h := startupScratch_live s hwf ⟨14 + i.val, by omega⟩
    simpa [allocationSize, show ¬ (19 ≤ 14 + i.val ∧ 14 + i.val < 28) by omega,
      ↓reduceIte] using h
  · constructor
    all_goals first | exact reductionPackingWords_bound d.quotient | rfl
  · apply hsubLive
    apply hpLive
    apply huLive
    exact allocationStates_smallRange s hwf out 32 hout 33
  · rfl
  · constructor <;> rfl
  · constructor <;> rfl
  · intro i
    apply storeBytes_live
    apply hsubLive
    apply hpLive
    apply huLive
    exact hs i

end Agave.Ed25519.ScalarReduce32.Execution
