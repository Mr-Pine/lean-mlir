import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Startup
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Frame

/-! The actual five result-limb stores preceding input cleanup. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
set_option maxRecDepth 100000

def resultSlotMemory (mem : MemoryState) (slots : Fin 5 → Pointer)
    (words : Fin 5 → BitVec 64) : MemoryState :=
  ((((mem.storeAt (slots 0) (words 0)).storeAt (slots 1) (words 1)).storeAt
    (slots 2) (words 2)).storeAt (slots 3) (words 3)).storeAt (slots 4) (words 4)

theorem resultSlots_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (slots : Fin 5 → Pointer) (words : Fin 5 → BitVec 64)
    (hlive : ∀ i, Fits state.mem (slots i) 64)
    (hs0 : E.read (%84) = .value (slots 0))
    (hs1 : E.read (%85) = .value (slots 1))
    (hs2 : E.read (%86) = .value (slots 2))
    (hs3 : E.read (%87) = .value (slots 3))
    (hs4 : E.read (%88) = .value (slots 4))
    (hw0 : E.read (%336) = .value (words 0))
    (hw1 : E.read (%341) = .value (words 1))
    (hw2 : E.read (%346) = .value (words 2))
    (hw3 : E.read (%349) = .value (words 3))
    (hw4 : E.read (%354) = .value (words 4)) :
    List.foldlM Instr.run E (((program.entry p g).body.drop 400).take 5) state =
      .value (E, {state with mem := resultSlotMemory state.mem slots words}) := by
  have hf0 := hlive 0
  have hf1 := hlive 1
  have hf2 := hlive 2
  have hf3 := hlive 3
  have hf4 := hlive 4
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run, resultSlotMemory,
    Operation.store, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf,
    hf0, hf1, hf2, hf3, hf4, hs0, hs1, hs2, hs3, hs4, hw0, hw1, hw2, hw3, hw4]

theorem resultSlots_erase (mem : MemoryState) (slots : Fin 5 → Pointer)
    (words : Fin 5 → BitVec 64) (mark : Nat) (hs : ∀ i, mark ≤ (slots i).id.id) :
    (resultSlotMemory mem slots words).eraseFrom mark = mem.eraseFrom mark := by
  simp only [resultSlotMemory, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (hs _)]

end Agave.Ed25519.Verifier.Execution.ScalarWide
