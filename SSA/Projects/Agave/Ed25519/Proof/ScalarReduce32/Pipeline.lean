import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Setup
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.MontgomeryPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Subtract
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StorePhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CleanupPhase

/-! Full phase composition through concrete register and memory states.
`PipelineReady` lists outstanding word/range invariants, not phase-execution
hypotheses. Establishing those invariants from caller bytes, and identifying the
final bytes as the canonical scalar remainder, remain separate obligations. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

structure PipelineData where
  scratch : Fin 33 → Pointer
  inputWords : Fin 5 → BitVec 64
  products : Fin 9 → BitVec 128
  quotient : Fin 5 → BitVec 52
  packingWords : Fin 5 → BitVec 64
  bytes : Bytes

def PipelineData.unpackScratch (d : PipelineData) : Fin 4 → Pointer :=
  fun i => d.scratch ⟨10 + i.val, by omega⟩

def PipelineData.productScratch (d : PipelineData) : Fin 9 → Pointer :=
  fun i => d.scratch ⟨19 + i.val, by omega⟩

def PipelineData.subtractScratch (d : PipelineData) : Fin 5 → Pointer :=
  fun i => d.scratch ⟨14 + i.val, by omega⟩

/-- The model uses only explicit word functions and memory writes already
matched by the exact instruction-slice theorems. It does not execute the RIR. -/
def pipelineStages (out input : Pointer) (s : GlobalState) (d : PipelineData) :
    Fin 10 → Env program.Γ × GlobalState :=
  let args := program.args (.value out) (.value input)
  let q0 : Env program.Γ × GlobalState := (Env.init args.get, s)
  let q1 := (constantsEnv q0.1, q0.2)
  let q2 := allocationSchedule q1.1 q1.2
  let q3 := unpackPhaseResult q2.1 q2.2 input d.unpackScratch
  let q4 := (productPhaseEnv q3.1 d.inputWords,
    productPhaseState q3.2 d.inputWords d.productScratch)
  let q5 := (montgomeryPhaseEnv q4.1 d.products, q4.2)
  let q6 := (subtractEnv q5.1 d.quotient,
    subtractState q5.2 d.quotient d.subtractScratch)
  let q7 := (packedEnv q6.1 (d.packingWords 0) (d.packingWords 1)
    (d.packingWords 2) (d.packingWords 3) (d.packingWords 4), q6.2)
  let q8 := (storeFinalEnv q7.1 out,
    {q7.2 with mem := storeBytes q7.2.mem out d.bytes})
  let q9 := cleanupPhaseResult q8.1 q8.2 d.scratch
  ![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]

/-! Concrete vector-selector lemmas keep phase conversion independent of the
size of the register and memory expressions stored in each stage. -/
theorem pipelineVector_get0 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 0 = q0 := rfl

theorem pipelineVector_get1 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 1 = q1 := rfl

theorem pipelineVector_get2 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 2 = q2 := rfl

theorem pipelineVector_get3 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 3 = q3 := rfl

theorem pipelineVector_get4 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 4 = q4 := rfl

theorem pipelineVector_get5 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 5 = q5 := rfl

theorem pipelineVector_get6 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 6 = q6 := rfl

theorem pipelineVector_get7 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 7 = q7 := rfl

theorem pipelineVector_get8 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 8 = q8 := rfl

theorem pipelineVector_get9 {α : Type} (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : α) :
    (![q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] : Fin 10 → α) 9 = q9 := rfl

/-- These are concrete local entry invariants still to be derived from the
function's public precondition. No field asserts execution of any instruction. -/
structure PipelineReady (out input : Pointer) (s : GlobalState) (d : PipelineData) : Prop where
  unpackRegisters : UnpackReady (pipelineStages out input s d 2).1 input d.unpackScratch
  inputLive : SmallRange (pipelineStages out input s d 2).2.mem input 32
  unpackLive : ∀ i, SmallRange (pipelineStages out input s d 2).2.mem (d.unpackScratch i) 8
  productRegisters : ProductReady (pipelineStages out input s d 3).1 d.inputWords d.productScratch
  inputBounds : ∀ i, (d.inputWords i).toNat < 2 ^ 52
  productLive : ∀ i, SmallRange (pipelineStages out input s d 3).2.mem (d.productScratch i) 16
  montgomeryRegisters : MontgomeryReady (pipelineStages out input s d 4).1 d.products
  productBounds : ∀ i, (d.products i).toNat < 2 ^ 107
  subtractRegisters : SubtractReady (pipelineStages out input s d 5).1 d.quotient d.subtractScratch
  subtractWF : (pipelineStages out input s d 5).2.WF
  subtractLive : ∀ i, SmallRange (pipelineStages out input s d 5).2.mem (d.subtractScratch i) 8
  packRegisters : PackReady (pipelineStages out input s d 6).1
    (d.packingWords 0) (d.packingWords 1) (d.packingWords 2) (d.packingWords 3) (d.packingWords 4)
  outputLive : SmallRange (pipelineStages out input s d 7).2.mem out 32
  outputRegister : (pipelineStages out input s d 7).1.read (%arg0) = .value out
  storeRegisters : StoreReady (pipelineStages out input s d 7).1 d.bytes
  cleanupRegisters : CleanupReady (pipelineStages out input s d 8).1 d.scratch
  cleanupLive : ∀ i, SmallRange (pipelineStages out input s d 8).2.mem (d.scratch i) (scratchBytes i)

/-- Compose all 622 source instructions and the actual call-frame erasure.
The only hypotheses beyond concrete data are the explicitly listed invariants. -/
theorem pipeline_call (out input : Pointer) (s : GlobalState) (d : PipelineData)
    (hr : PipelineReady out input s d) :
    program.call (program.args (.value out) (.value input)) s =
      .value (.nil, {(pipelineStages out input s d 9).2 with
        mem := (pipelineStages out input s d 9).2.mem.eraseFrom s.alloc.nextFreeBlock}) := by
  let q := pipelineStages out input s d
  have h0 := constants_execute (q 0).1 (q 0).2
  have h1 := allocations_execute (q 1).1 (q 1).2
  have h2 := unpack_phase (q 2).1 (q 2).2 input d.unpackScratch
    hr.unpackRegisters hr.inputLive hr.unpackLive
  have h3 := product_phase (q 3).1 (q 3).2 d.inputWords d.productScratch
    hr.productRegisters hr.inputBounds hr.productLive
  have h4 := montgomery_phase (q 4).1 (q 4).2 d.products
    hr.montgomeryRegisters hr.productBounds
  have h5 := subtract_body (q 5).1 (q 5).2 d.quotient d.subtractScratch
    hr.subtractRegisters hr.subtractWF hr.subtractLive
  have h6 := pack_phase (q 6).1 (q 6).2 (d.packingWords 0) (d.packingWords 1)
    (d.packingWords 2) (d.packingWords 3) (d.packingWords 4) hr.packRegisters
  have h7 := store_phase (q 7).1 (q 7).2 out d.bytes
    hr.outputLive hr.outputRegister hr.storeRegisters
  have h8 := cleanup_phase (q 8).1 (q 8).2 d.scratch hr.cleanupRegisters hr.cleanupLive
  apply call_of_phases (program.args (.value out) (.value input))
    (q 1).1 (q 2).1 (q 3).1 (q 4).1 (q 5).1 (q 6).1 (q 7).1 (q 8).1 (q 9).1
    s (q 1).2 (q 2).2 (q 3).2 (q 4).2 (q 5).2 (q 6).2 (q 7).2 (q 8).2 (q 9).2
  · simpa only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] using h0
  · simpa only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] using h1
  · simpa only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] using h2
  · simpa only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] using h3
  · simpa only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] using h4
  · simpa only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] using h5
  · simpa only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] using h6
  · simpa only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] using h7
  · simpa only [q, pipelineStages, pipelineVector_get0, pipelineVector_get1, pipelineVector_get2, pipelineVector_get3, pipelineVector_get4, pipelineVector_get5, pipelineVector_get6, pipelineVector_get7, pipelineVector_get8, pipelineVector_get9] using h8

end Agave.Ed25519.ScalarReduce32.Execution
