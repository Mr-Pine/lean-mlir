import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeMemory
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline117

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes

theorem entry_constants (g : Globals) (E : Env program.Γ) (s : GlobalState) :
    Inline308.Constants (entryResult g E s).1 := by
  constructor <;> rfl

theorem entry_sqrtM1 (g : Globals) (E : Env program.Γ) (s : GlobalState) :
    (entryResult g E s).1.read (%52) = .value g.address0 := rfl

theorem frame_constants (E F : Env program.Γ) (h : SerializerFrame.Frame 84 E F)
    (hc : Inline308.Constants E) : Inline308.Constants F := by
  constructor
  · exact (h.2 1 (by decide)).trans hc.c1
  · exact (h.2 3 (by decide)).trans hc.c3
  · exact (h.2 4 (by decide)).trans hc.c4
  · exact (h.2 5 (by decide)).trans hc.c5
  · exact (h.2 6 (by decide)).trans hc.c6
  · exact (h.2 7 (by decide)).trans hc.c7
  · exact (h.2 8 (by decide)).trans hc.c8
  · exact (h.2 9 (by decide)).trans hc.c9
  · exact (h.2 10 (by decide)).trans hc.c10
  · exact (h.2 11 (by decide)).trans hc.c11
  · exact (h.2 12 (by decide)).trans hc.c12
  · exact (h.2 13 (by decide)).trans hc.c13
  · exact (h.2 14 (by decide)).trans hc.c14
  · exact (h.2 15 (by decide)).trans hc.c15
  · exact (h.2 16 (by decide)).trans hc.c16
  · exact (h.2 17 (by decide)).trans hc.c17
  · exact (h.2 18 (by decide)).trans hc.c18
  · exact (h.2 19 (by decide)).trans hc.c19
  · exact (h.2 20 (by decide)).trans hc.c20
  · exact (h.2 21 (by decide)).trans hc.c21
  · exact (h.2 22 (by decide)).trans hc.c22
  · exact (h.2 23 (by decide)).trans hc.c23
  · exact (h.2 24 (by decide)).trans hc.c24
  · exact (h.2 25 (by decide)).trans hc.c25
  · exact (h.2 26 (by decide)).trans hc.c26
  · exact (h.2 27 (by decide)).trans hc.c27
  · exact (h.2 28 (by decide)).trans hc.c28
  · exact (h.2 29 (by decide)).trans hc.c29
  · exact (h.2 30 (by decide)).trans hc.c30
  · exact (h.2 31 (by decide)).trans hc.c31
  · exact (h.2 32 (by decide)).trans hc.c32
  · exact (h.2 33 (by decide)).trans hc.c33
  · exact (h.2 34 (by decide)).trans hc.c34
  · exact (h.2 35 (by decide)).trans hc.c35
  · exact (h.2 36 (by decide)).trans hc.c36
  · exact (h.2 37 (by decide)).trans hc.c37
  · exact (h.2 38 (by decide)).trans hc.c38
  · exact (h.2 39 (by decide)).trans hc.c39
  · exact (h.2 40 (by decide)).trans hc.c40
  · exact (h.2 41 (by decide)).trans hc.c41
  · exact (h.2 42 (by decide)).trans hc.c42
  · exact (h.2 43 (by decide)).trans hc.c43
  · exact (h.2 44 (by decide)).trans hc.c44
  · exact (h.2 45 (by decide)).trans hc.c45
  · exact (h.2 46 (by decide)).trans hc.c46
  · exact (h.2 50 (by decide)).trans hc.c50
  · exact (h.2 54 (by decide)).trans hc.c54
  · exact (h.2 59 (by decide)).trans hc.c59
  · exact (h.2 47 (by decide)).trans hc.c47
  · exact (h.2 48 (by decide)).trans hc.c48
  · exact (h.2 49 (by decide)).trans hc.c49
  · exact (h.2 51 (by decide)).trans hc.c51

theorem frame_slot (E F : Env program.Γ) (h : SerializerFrame.Frame 84 E F)
    (i : Fin 22) : F.read (slotRegister i) = E.read (slotRegister i) := by
  fin_cases i <;> exact h.2 _ (by decide)

def state306 (s : GlobalState) (u v : Pointer) : GlobalState :=
  Inline117.resultState (state117 s u v) (slot s 5)
    (readLimbs (state117 s u v) (slot s 13))

theorem state306_scratch (s : GlobalState) (u v : Pointer) (hwf : s.WF) :
    ScratchFrame s (state306 s u v) :=
  (state117_scratch s u v hwf).storeBytes (slot s 5) _ (slot_private s 5)

/-- The first canonical check bytes and their cached SSA values are obtained
from the actual prefix, with no intermediate execution premise. -/
theorem prefix306 (g : Globals) (E : Env program.Γ) (s : GlobalState) (u v : Pointer)
    (hwf : s.WF) (hu : SmallRange s.mem u 40) (hv : SmallRange s.mem v 40)
    (heu : E.read (%arg1) = .value u) (hev : E.read (%arg2) = .value v) :
    ∃ F : Env program.Γ, Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 306 E s =
        .value (F,state306 s u v) ∧
      SerializerFrame.Frame 84 (entryResult g E s).1 F ∧
      Inline308.Cached F (ToBytes.machine (readLimbs (state117 s u v) (slot s 13))) ∧
      F.read (%85) = .value ((slot s 13).add 8#64) ∧
      F.read (%87) = .value ((slot s 13).add 16#64) ∧
      F.read (%89) = .value ((slot s 13).add 24#64) ∧
      F.read (%91) = .value ((slot s 13).add 32#64) := by
  have hs := state117_scratch s u v hwf
  obtain ⟨F,hseg,hframe,hcached,h85,h87,h89,h91⟩ := Inline117.segment sqrtRatioPrimitives g
    (entryResult g E s).1 (state117 s u v) (slot s 5) (slot s 13)
    hs.wf (hs.slots 5) (hs.slots 13) (entry_constants g E s)
    (entry_slot g E s 5) (entry_slot g E s 13)
  refine ⟨F,?_,hframe,hcached,h85,h87,h89,h91⟩
  rw [show 306 = 117 + 189 from rfl,segment_append]
  simp only [EffectM.bind_eq,prefix117 g E s u v hwf hu hv heu hev,PoisonOr.value_bind]
  exact hseg

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
