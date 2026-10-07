import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2LiveDefs

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Avx2PointAdd.Phases (Scratch)
open Conformance.BackendExecution (Invocation)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem LoopRegisters.addConstants (h : LoopRegisters g i initial E) :
    Avx2PointAdd.CFG.Constants E := by
  obtain ⟨ES, pos, he, hr⟩ := h
  constructor
  · have hn : E.read (%26) = ES.read (%26) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%26) (by decide)
    refine hn.trans ((he.read (%26) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%135) = ES.read (%135) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%135) (by decide)
    refine hn.trans ((he.read (%135) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%152) = ES.read (%152) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%152) (by decide)
    refine hn.trans ((he.read (%152) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%170) = ES.read (%170) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%170) (by decide)
    refine hn.trans ((he.read (%170) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%187) = ES.read (%187) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%187) (by decide)
    refine hn.trans ((he.read (%187) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%204) = ES.read (%204) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%204) (by decide)
    refine hn.trans ((he.read (%204) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%221) = ES.read (%221) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%221) (by decide)
    refine hn.trans ((he.read (%221) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel

theorem LoopRegisters.doubleConstants (h : LoopRegisters g i initial E) :
    Avx2PointDouble.CFG.Constants E := by
  obtain ⟨ES, pos, he, hr⟩ := h
  constructor
  · have hn : E.read (%26) = ES.read (%26) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%26) (by decide)
    refine hn.trans ((he.read (%26) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%27) = ES.read (%27) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%27) (by decide)
    refine hn.trans ((he.read (%27) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%45) = ES.read (%45) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%45) (by decide)
    refine hn.trans ((he.read (%45) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%62) = ES.read (%62) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%62) (by decide)
    refine hn.trans ((he.read (%62) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%81) = ES.read (%81) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%81) (by decide)
    refine hn.trans ((he.read (%81) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%99) = ES.read (%99) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%99) (by decide)
    refine hn.trans ((he.read (%99) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%116) = ES.read (%116) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%116) (by decide)
    refine hn.trans ((he.read (%116) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel

theorem LoopRegisters.addition22 (h : LoopRegisters g i initial E) :
    AdditionStatic22 E (loopScratch initial 0) (avx2StackPtr initial 27) := by
  have hc := h.addConstants
  obtain ⟨ES, pos, he, hr⟩ := h
  constructor
  · exact hc
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%3) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%20) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%21) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%22) (by decide)
  · have hn : E.read (%153) = ES.read (%153) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%153) (by decide)
    refine hn.trans ((he.read (%153) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%250) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%251) (by decide)
  · have hn : E.read (%252) = ES.read (%252) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%252) (by decide)
    refine hn.trans ((he.read (%252) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%253) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%254) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%261) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%264) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%355) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%356) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%357) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%358) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%359) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%360) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%361) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%362) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%363) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%364) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%365) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%366) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%367) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%368) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%369) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%370) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%371) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%372) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%373) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%374) (by decide)

theorem LoopRegisters.addition25 (h : LoopRegisters g i initial E) :
    AdditionStatic25 E (loopScratch initial 1) (avx2StackPtr initial 27) := by
  have hc := h.addConstants
  obtain ⟨ES, pos, he, hr⟩ := h
  constructor
  · exact hc
  · have hn : E.read (%153) = ES.read (%153) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%153) (by decide)
    refine hn.trans ((he.read (%153) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%246) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%247) (by decide)
  · have hn : E.read (%248) = ES.read (%248) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%248) (by decide)
    refine hn.trans ((he.read (%248) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%249) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%262) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%264) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%339) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%340) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%341) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%342) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%343) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%344) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%345) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%346) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%347) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%348) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%349) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%350) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%351) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%352) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%353) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%354) (by decide)

theorem LoopRegisters.addition29 (h : LoopRegisters g i initial E) :
    AdditionStatic29 E (loopScratch initial 2) g.address2 := by
  have hc := h.addConstants
  obtain ⟨ES, pos, he, hr⟩ := h
  constructor
  · exact hc
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%3) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%20) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%21) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%22) (by decide)
  · have hn : E.read (%153) = ES.read (%153) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%153) (by decide)
    refine hn.trans ((he.read (%153) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%224) = ES.read (%224) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%224) (by decide)
    refine hn.trans ((he.read (%224) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%241) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%242) (by decide)
  · have hn : E.read (%243) = ES.read (%243) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%243) (by decide)
    refine hn.trans ((he.read (%243) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%244) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%245) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%259) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%391) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%392) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%393) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%394) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%395) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%396) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%397) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%398) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%399) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%400) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%401) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%402) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%403) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%404) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%405) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%406) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%407) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%408) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%409) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%410) (by decide)

theorem LoopRegisters.addition33 (h : LoopRegisters g i initial E) :
    AdditionStatic33 E (loopScratch initial 3) g.address2 := by
  have hc := h.addConstants
  obtain ⟨ES, pos, he, hr⟩ := h
  constructor
  · exact hc
  · have hn : E.read (%153) = ES.read (%153) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%153) (by decide)
    refine hn.trans ((he.read (%153) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · have hn : E.read (%224) = ES.read (%224) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%224) (by decide)
    refine hn.trans ((he.read (%224) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%237) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%238) (by decide)
  · have hn : E.read (%239) = ES.read (%239) := by
      simpa [tableSetupResult, tableSetupInput, mlir_env] using hr.read (%239) (by decide)
    refine hn.trans ((he.read (%239) (by decide)).trans ?_)
    simp [entryLoopEnv, avx2EntryEnv, loopScratch,
      Avx2PointAdd.CFG.prepareConstants, Avx2PointAdd.CFG.differenceConstants,
      Avx2PointAdd.CFG.negateConstants, Avx2PointAdd.Phases.evenConstant,
      Avx2PointAdd.Phases.oddConstant, Avx2PointDouble.zeroPrefix,
      Avx2PointDouble.zeroDifference, Avx2PointDouble.lazyConstants,
      Avx2PointDouble.zeroSum, Ty.wrap_vec, mlir_env] <;> decide +kernel
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%240) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%260) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%375) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%376) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%377) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%378) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%379) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%380) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%381) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%382) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%383) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%384) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%385) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%386) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%387) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%388) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%389) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%390) (by decide)

theorem LoopRegisters.doublePointers (h : LoopRegisters g i initial E) :
    Avx2PointDouble.CFG.Pointers E (avx2StackPtr initial 19)
      (avx2StackPtr initial 18) (avx2StackPtr initial 26) := by
  obtain ⟨ES, pos, he, hr⟩ := h
  constructor
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%256) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%327) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%328) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%329) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%330) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%255) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%331) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%332) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%333) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%334) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%263) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%335) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%336) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%337) (by decide)
  · simpa [tableSetupResult, tableSetupInput, loopScratch, stackSetupSlots,
      setupStackIndex, mlir_env] using hr.read (%338) (by decide)

end Agave.Ed25519.DoubleBase.ExecutionAvx2
