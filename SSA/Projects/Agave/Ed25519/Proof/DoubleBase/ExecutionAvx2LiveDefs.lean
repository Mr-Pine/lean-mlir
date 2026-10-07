import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ArithmeticBridge

/-! The actual entry and table-setup snapshots retain every arithmetic live-in.
The descending control trace may update registers 421 and above only. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Avx2PointAdd.Phases (Scratch)
open Conformance.BackendExecution (Invocation)
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def loopScratch (initial : GlobalState) (site : Fin 4) : Scratch :=
  let indices : Fin 4 → Fin 6 → Nat :=
    ![![24, 16, 15, 14, 13, 17], ![25, 12, 11, 10, 9, 17],
      ![22, 7, 6, 5, 4, 8], ![23, 3, 2, 1, 0, 8]]
  let q := fun k => avx2StackPtr initial (indices site k)
  ⟨q 0, q 1, q 2, q 3, q 4, q 5⟩

/-- A witness from the exact prefix, followed only by writes in the descending
loop's register interval. The scan and table setup are not recomputed. -/
def LoopRegisters (g : Avx2CFG.Globals) (i : Invocation) (initial : GlobalState)
    (E : ⟪avx2Kernel.Γ⟫) : Prop :=
  ∃ (ES : ⟪avx2Kernel.Γ⟫) (pos : Fin 256),
    RegisterFrame 268 421 (entryLoopEnv (Env.init i.args.get) g initial) ES ∧
    RegisterFrame 421 avx2Kernel.Γ.n
      (tableSetupResult ES (stackSetupSlots initial) (avx2StackPtr initial 27) pos) E

theorem LoopRegisters.prefix
    (hf : RegisterFrame 268 421 (entryLoopEnv (Env.init i.args.get) g initial) ES)
    (pos : Fin 256) :
    LoopRegisters g i initial
      (tableSetupResult ES (stackSetupSlots initial) (avx2StackPtr initial 27) pos) :=
  ⟨ES, pos, hf, RegisterFrame.refl _ _ _⟩

theorem LoopRegisters.frame (h : LoopRegisters g i initial E)
    (hf : RegisterFrame 421 avx2Kernel.Γ.n E E') : LoopRegisters g i initial E' := by
  obtain ⟨ES, pos, he, hr⟩ := h
  exact ⟨ES, pos, he, hr.trans hf⟩

end Agave.Ed25519.DoubleBase.ExecutionAvx2
