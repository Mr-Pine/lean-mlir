import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialCacheFragments
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorLoopWrapper

namespace Agave.Ed25519.Tables.SerialConstructorLoopRegisters
open LeanMLIR.RIR
open DoubleBase.RIR (PrefixEq)
open SerialConstructorStack (constants)
open SerialConstructorLoopWrapper
abbrev Slots := Fin 7 → Pointer
variable {E F : ⟪SerialConstructor.kernel.Γ⟫}
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Ready (g : SerialConstructor.Globals) (slots : Slots) (table : Pointer)
    (E : ⟪SerialConstructor.kernel.Γ⟫) : Prop where
  constants : constants E g = E
  r31 : E.read (%31) = .value (slots 2)
  r32 : E.read (%32) = .value (slots 3)
  r33 : E.read (%33) = .value (slots 4)
  r34 : E.read (%34) = .value (slots 5)
  r36 : E.read (%36) = .value (table)
  r115 : E.read (%115) = .value ((slots 2).add 120)
  r116 : E.read (%116) = .value ((slots 2).add 40)
  r117 : E.read (%117) = .value ((slots 2).add 80)
  r118 : E.read (%118) = .value ((slots 3).add 40)
  r119 : E.read (%119) = .value ((slots 3).add 80)
  r120 : E.read (%120) = .value ((slots 3).add 120)
  r121 : E.read (%121) = .value ((slots 3).add 48)
  r122 : E.read (%122) = .value ((slots 3).add 56)
  r123 : E.read (%123) = .value ((slots 3).add 64)
  r124 : E.read (%124) = .value ((slots 3).add 72)
  r125 : E.read (%125) = .value ((slots 3).add 8)
  r126 : E.read (%126) = .value ((slots 3).add 16)
  r127 : E.read (%127) = .value ((slots 3).add 24)
  r128 : E.read (%128) = .value ((slots 3).add 32)
  r129 : E.read (%129) = .value ((slots 4).add 80)
  r130 : E.read (%130) = .value ((slots 4).add 120)
  r131 : E.read (%131) = .value ((slots 4).add 8)
  r132 : E.read (%132) = .value ((slots 4).add 16)
  r133 : E.read (%133) = .value ((slots 4).add 24)
  r134 : E.read (%134) = .value ((slots 4).add 32)
  r135 : E.read (%135) = .value ((slots 4).add 40)
  r136 : E.read (%136) = .value ((slots 4).add 48)
  r137 : E.read (%137) = .value ((slots 4).add 56)
  r138 : E.read (%138) = .value ((slots 4).add 64)
  r139 : E.read (%139) = .value ((slots 4).add 72)

theorem Ready.preserve (h : Ready g slots table E) (hf : PrefixEq E F 140) :
    Ready g slots table F := by
  refine ⟨?_, ((hf.read (%31) (by intro i ht he; cases he; decide)).trans h.r31), ((hf.read (%32) (by intro i ht he; cases he; decide)).trans h.r32), ((hf.read (%33) (by intro i ht he; cases he; decide)).trans h.r33), ((hf.read (%34) (by intro i ht he; cases he; decide)).trans h.r34), ((hf.read (%36) (by intro i ht he; cases he; decide)).trans h.r36), ((hf.read (%115) (by intro i ht he; cases he; decide)).trans h.r115), ((hf.read (%116) (by intro i ht he; cases he; decide)).trans h.r116), ((hf.read (%117) (by intro i ht he; cases he; decide)).trans h.r117), ((hf.read (%118) (by intro i ht he; cases he; decide)).trans h.r118), ((hf.read (%119) (by intro i ht he; cases he; decide)).trans h.r119), ((hf.read (%120) (by intro i ht he; cases he; decide)).trans h.r120), ((hf.read (%121) (by intro i ht he; cases he; decide)).trans h.r121), ((hf.read (%122) (by intro i ht he; cases he; decide)).trans h.r122), ((hf.read (%123) (by intro i ht he; cases he; decide)).trans h.r123), ((hf.read (%124) (by intro i ht he; cases he; decide)).trans h.r124), ((hf.read (%125) (by intro i ht he; cases he; decide)).trans h.r125), ((hf.read (%126) (by intro i ht he; cases he; decide)).trans h.r126), ((hf.read (%127) (by intro i ht he; cases he; decide)).trans h.r127), ((hf.read (%128) (by intro i ht he; cases he; decide)).trans h.r128), ((hf.read (%129) (by intro i ht he; cases he; decide)).trans h.r129), ((hf.read (%130) (by intro i ht he; cases he; decide)).trans h.r130), ((hf.read (%131) (by intro i ht he; cases he; decide)).trans h.r131), ((hf.read (%132) (by intro i ht he; cases he; decide)).trans h.r132), ((hf.read (%133) (by intro i ht he; cases he; decide)).trans h.r133), ((hf.read (%134) (by intro i ht he; cases he; decide)).trans h.r134), ((hf.read (%135) (by intro i ht he; cases he; decide)).trans h.r135), ((hf.read (%136) (by intro i ht he; cases he; decide)).trans h.r136), ((hf.read (%137) (by intro i ht he; cases he; decide)).trans h.r137), ((hf.read (%138) (by intro i ht he; cases he; decide)).trans h.r138), ((hf.read (%139) (by intro i ht he; cases he; decide)).trans h.r139)⟩
  apply SerialConstructorStack.constants_of_prefix E F g
  rw [h.constants]
  exact hf.mono (by decide)

theorem Ready.c18 (h : Ready g slots table E) : E.read (%18) = .value 160#64 := by
  have hc := congrArg (fun F : ⟪SerialConstructor.kernel.Γ⟫ => F.read (%18)) h.constants
  simpa [SerialConstructorStack.constants, mlir_env] using hc.symm

theorem Ready.c26 (h : Ready g slots table E) : E.read (%26) = .value 1#64 := by
  have hc := congrArg (fun F : ⟪SerialConstructor.kernel.Γ⟫ => F.read (%26)) h.constants
  simpa [SerialConstructorStack.constants, mlir_env] using hc.symm

theorem Ready.c27 (h : Ready g slots table E) : E.read (%27) = .value 7#64 := by
  have hc := congrArg (fun F : ⟪SerialConstructor.kernel.Γ⟫ => F.read (%27)) h.constants
  simpa [SerialConstructorStack.constants, mlir_env] using hc.symm

theorem Ready.c28 (h : Ready g slots table E) : E.read (%28) = .value 1280#64 := by
  have hc := congrArg (fun F : ⟪SerialConstructor.kernel.Γ⟫ => F.read (%28)) h.constants
  simpa [SerialConstructorStack.constants, mlir_env] using hc.symm

theorem Ready.prefix (h : Ready g slots table E) (k : Fin 7)
    (hc : E.read (%140) = .value (BitVec.ofNat 64 k.val)) :
    prefixInput E (slots 2) (slots 3) (slots 5) table k = E := by
  unfold prefixInput
  rw [Env.write_of_read E (%26) h.c26,
    Env.write_of_read E (%31) h.r31,
    Env.write_of_read E (%32) h.r32,
    Env.write_of_read E (%34) h.r34,
    Env.write_of_read E (%36) h.r36,
    Env.write_of_read E (%115) h.r115,
    Env.write_of_read E (%116) h.r116,
    Env.write_of_read E (%117) h.r117,
    Env.write_of_read E (%118) h.r118,
    Env.write_of_read E (%119) h.r119,
    Env.write_of_read E (%120) h.r120,
    Env.write_of_read E (%140) hc]

theorem Ready.cache (h : Ready g slots table E) :
    SerialCacheExecution.loopInput E (slots 4) (slots 3) = E := by
  unfold SerialCacheExecution.loopInput
  rw [Env.write_of_read E (%32) h.r32,
    Env.write_of_read E (%33) h.r33,
    Env.write_of_read E (%118) h.r118,
    Env.write_of_read E (%119) h.r119,
    Env.write_of_read E (%120) h.r120,
    Env.write_of_read E (%121) h.r121,
    Env.write_of_read E (%122) h.r122,
    Env.write_of_read E (%123) h.r123,
    Env.write_of_read E (%124) h.r124,
    Env.write_of_read E (%125) h.r125,
    Env.write_of_read E (%126) h.r126,
    Env.write_of_read E (%127) h.r127,
    Env.write_of_read E (%128) h.r128,
    Env.write_of_read E (%129) h.r129,
    Env.write_of_read E (%130) h.r130,
    Env.write_of_read E (%131) h.r131,
    Env.write_of_read E (%132) h.r132,
    Env.write_of_read E (%133) h.r133,
    Env.write_of_read E (%134) h.r134,
    Env.write_of_read E (%135) h.r135,
    Env.write_of_read E (%136) h.r136,
    Env.write_of_read E (%137) h.r137,
    Env.write_of_read E (%138) h.r138,
    Env.write_of_read E (%139) h.r139]

theorem Ready.tail (h : Ready g slots table E) (k : Fin 7)
    (hc : E.read (%141) = .value (BitVec.ofNat 64 (k.val+1))) :
    tailInput E table (slots 4) k = E := by
  unfold tailInput
  rw [Env.write_of_read E (%18) h.c18,
    Env.write_of_read E (%27) h.c27,
    Env.write_of_read E (%33) h.r33,
    Env.write_of_read E (%36) h.r36,
    Env.write_of_read E (%141) hc]

theorem Ready.returnInput (h : Ready g slots table E) :
    ConstructorMemory.serialReturnInput E table = E := by
  unfold ConstructorMemory.serialReturnInput
  rw [Env.write_of_read E (%28) h.c28,
    Env.write_of_read E (%36) h.r36]

end Agave.Ed25519.Tables.SerialConstructorLoopRegisters
