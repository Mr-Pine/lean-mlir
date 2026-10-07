import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.InputFragments

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

structure InputWordRegisters (E : Env program.Γ) (x : Fin 5 → BitVec 64) : Prop where
  x0 : E.read (%176) = PoisonOr.value (x 0)
  x1 : E.read (%175) = PoisonOr.value (x 1)
  x2 : E.read (%174) = PoisonOr.value (x 2)
  x3 : E.read (%172) = PoisonOr.value (x 3)
  x4 : E.read (%171) = PoisonOr.value (x 4)

/-- Fresh private blocks cannot alter any byte observed by the subsequent
mixed-width input loads. This connects the exact unpack state to caller bytes. -/
theorem unpack_registers (E : Env program.Γ) (s : GlobalState) (a : Pointer)
    (scratch : Fin 4 → Pointer) (bytes : BitVec 256)
    (ha : SmallRange s.mem a 32) (hread : s.mem.readAt a 256 = bytes)
    (hne : ∀ i, (scratch i).id ≠ a.id) :
    InputWordRegisters (unpackPhaseResult E s a scratch).1 (inputWords bytes) := by
  let s1 : GlobalState := {s with mem := s.mem.storeAt (scratch 1) (unpackV134 s a)}
  let s2 : GlobalState := {s1 with mem := s1.mem.storeAt (scratch 2) (unpackV152 s1 a)}
  have ha1 : SmallRange s1.mem a 32 := ha.storeAt _ _
  have ha2 : SmallRange s2.mem a 32 := ha1.storeAt _ _
  have hr1 : s1.mem.readAt a 256 = bytes := by
    rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne (hne 1))]
    exact hread
  have hr2 : s2.mem.readAt a 256 = bytes := by
    rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne (hne 2))]
    exact hr1
  have f111 := unpackV111_fragment s a bytes ha hread
  have f116 := unpackV116_fragment s a bytes ha hread
  have f124 := unpackV124_fragment s a bytes ha hread
  have f133 := unpackV133_fragment s a bytes ha hread
  have f147 := unpackV147_fragment s1 a bytes ha1 hr1
  have f152 := unpackV152_fragment s1 a bytes ha1 hr1
  have f160 := unpackV160_fragment s2 a bytes ha2 hr2
  have f169 := unpackV169_fragment s2 a bytes ha2 hr2
  constructor
  · change PoisonOr.value (unpackV111 s a &&& 4503599627370495#64) = PoisonOr.value (inputWords bytes 0)
    rw [f111]
    rfl
  · change PoisonOr.value (inputFunnel (unpackV124 s a) (unpackV116 s a) 12) =
      PoisonOr.value (inputWords bytes 1)
    rw [f124, f116]
    rfl
  · change PoisonOr.value (inputFunnel (unpackV147 s1 a) (unpackV133 s a) 24 &&&
      4503599627370495#64) = PoisonOr.value (inputWords bytes 2)
    rw [f147, f133]
    rfl
  · change PoisonOr.value (inputFunnel (unpackV160 s2 a) (unpackV152 s1 a) 36) =
      PoisonOr.value (inputWords bytes 3)
    rw [f160, f152]
    rfl
  · change PoisonOr.value (unpackV169 s2 a >>> 16) = PoisonOr.value (inputWords bytes 4)
    rw [f169]
    rfl

end Agave.Ed25519.ScalarReduce32.Execution
