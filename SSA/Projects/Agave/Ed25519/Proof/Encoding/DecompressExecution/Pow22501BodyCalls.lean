import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501Program
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.RIR.Run.Tactic

/-! Exact execution of the imported pow22501 body, with one opaque state for
 each of its 21 primitive calls. Premises describe only individual calls and
 the final memcpy's live ranges and disjointness. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The allocation used by source register `7 + i`. -/
def scratch (initial : GlobalState) (i : Nat) : Pointer :=
  ⟨⟨initial.alloc.nextFreeBlock + i⟩, 0⟩

/-- The original twenty allocations, before the first primitive call. -/
def scratchState (initial : GlobalState) : Nat → GlobalState
  | 0 => initial
  | n + 1 => (scratchState initial n).alloca 40

/-- State immediately after each primitive invocation, in source order. -/
abbrev CallStates := Fin 21 → GlobalState

/-- The original final memcpy from source register 22 to the second output. -/
def copyState (initial : GlobalState) (r : Pointer) (s : GlobalState) : GlobalState :=
  {s with mem := s.mem.storeAt (r.add 40#64) (s.mem.readAt (scratch initial 15) 320)}

/-- Exact local invocation facts for the 21 calls, followed by conditions for
 the source GEP and 40-byte memcpy. -/
structure BodyCalls (prim : Primitives) (initial : GlobalState) (r a : Pointer)
    (states : CallStates) : Prop where
  call0 : prim.pow2k (.cons (.value (scratch initial 19))
    (.cons (.value a) (.cons (.value 1#32) .nil)))
    (scratchState initial 20) = .value (.nil, states 0)
  call1 : prim.pow2k (.cons (.value (scratch initial 17))
    (.cons (.value (scratch initial 19)) (.cons (.value 1#32) .nil)))
    (states 0) = .value (.nil, states 1)
  call2 : prim.pow2k (.cons (.value (scratch initial 18))
    (.cons (.value (scratch initial 17)) (.cons (.value 1#32) .nil)))
    (states 1) = .value (.nil, states 2)
  call3 : prim.mul (.cons (.value (scratch initial 16))
    (.cons (.value a) (.cons (.value (scratch initial 18)) .nil)))
    (states 2) = .value (.nil, states 3)
  call4 : prim.mul (.cons (.value (scratch initial 15))
    (.cons (.value (scratch initial 19)) (.cons (.value (scratch initial 16)) .nil)))
    (states 3) = .value (.nil, states 4)
  call5 : prim.pow2k (.cons (.value (scratch initial 14))
    (.cons (.value (scratch initial 15)) (.cons (.value 1#32) .nil)))
    (states 4) = .value (.nil, states 5)
  call6 : prim.mul (.cons (.value (scratch initial 13))
    (.cons (.value (scratch initial 16)) (.cons (.value (scratch initial 14)) .nil)))
    (states 5) = .value (.nil, states 6)
  call7 : prim.pow2k (.cons (.value (scratch initial 12))
    (.cons (.value (scratch initial 13)) (.cons (.value 5#32) .nil)))
    (states 6) = .value (.nil, states 7)
  call8 : prim.mul (.cons (.value (scratch initial 11))
    (.cons (.value (scratch initial 12)) (.cons (.value (scratch initial 13)) .nil)))
    (states 7) = .value (.nil, states 8)
  call9 : prim.pow2k (.cons (.value (scratch initial 10))
    (.cons (.value (scratch initial 11)) (.cons (.value 10#32) .nil)))
    (states 8) = .value (.nil, states 9)
  call10 : prim.mul (.cons (.value (scratch initial 9))
    (.cons (.value (scratch initial 10)) (.cons (.value (scratch initial 11)) .nil)))
    (states 9) = .value (.nil, states 10)
  call11 : prim.pow2k (.cons (.value (scratch initial 8))
    (.cons (.value (scratch initial 9)) (.cons (.value 20#32) .nil)))
    (states 10) = .value (.nil, states 11)
  call12 : prim.mul (.cons (.value (scratch initial 7))
    (.cons (.value (scratch initial 8)) (.cons (.value (scratch initial 9)) .nil)))
    (states 11) = .value (.nil, states 12)
  call13 : prim.pow2k (.cons (.value (scratch initial 6))
    (.cons (.value (scratch initial 7)) (.cons (.value 10#32) .nil)))
    (states 12) = .value (.nil, states 13)
  call14 : prim.mul (.cons (.value (scratch initial 5))
    (.cons (.value (scratch initial 6)) (.cons (.value (scratch initial 11)) .nil)))
    (states 13) = .value (.nil, states 14)
  call15 : prim.pow2k (.cons (.value (scratch initial 4))
    (.cons (.value (scratch initial 5)) (.cons (.value 50#32) .nil)))
    (states 14) = .value (.nil, states 15)
  call16 : prim.mul (.cons (.value (scratch initial 3))
    (.cons (.value (scratch initial 4)) (.cons (.value (scratch initial 5)) .nil)))
    (states 15) = .value (.nil, states 16)
  call17 : prim.pow2k (.cons (.value (scratch initial 2))
    (.cons (.value (scratch initial 3)) (.cons (.value 100#32) .nil)))
    (states 16) = .value (.nil, states 17)
  call18 : prim.mul (.cons (.value (scratch initial 1))
    (.cons (.value (scratch initial 2)) (.cons (.value (scratch initial 3)) .nil)))
    (states 17) = .value (.nil, states 18)
  call19 : prim.pow2k (.cons (.value (scratch initial 0))
    (.cons (.value (scratch initial 1)) (.cons (.value 50#32) .nil)))
    (states 18) = .value (.nil, states 19)
  call20 : prim.mul (.cons (.value r)
    (.cons (.value (scratch initial 0)) (.cons (.value (scratch initial 5)) .nil)))
    (states 19) = .value (.nil, states 20)
  outputLive : SmallRange (states 20).mem r 80
  sourceLive : SmallRange (states 20).mem (scratch initial 15) 40
  copyDisjoint : (Range.of (r.add 40#64) 320).Disjoint
    (Range.of (scratch initial 15) 320)

private theorem modifyGet_run (f : GlobalState → α × GlobalState) (s : GlobalState) :
    (modifyGet f : EffectM α) s = .value (f s) := rfl

/-- Full imported body execution: all 20 allocations, 21 helper calls,
 lifetime markers, the output GEP, final memcpy, and original return. -/
theorem program_run_of_calls (prim : Primitives) (r a : Pointer)
    (initial : GlobalState) (states : CallStates)
    (calls : BodyCalls prim initial r a states) :
    (program prim).run (program.args (.value r) (.value a)) initial =
      .value (.nil, copyState initial r (states 20)) := by
  rcases calls with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hout, hsource, hdisjoint⟩
  have hgep := hout.gep (k := 40) (by decide)
  have hd := hout.fits_add (k := 40) (count := 40) (by decide)
  have hs := hsource.fits
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [scratchState] at hc0
  simp [scratch] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13 hc14 hc15 hc16 hc17 hc18 hc19 hc20 hd hs hdisjoint
  rw [Func.run_runFrom_eq, Func.runFrom_eq]
  simp (config := {maxSteps := 1000000}) [BasicBlock.run, program.entry, List.foldlM_cons, List.foldlM_nil,
    Instr.run, modifyGet_run, Ty.wrap, EffectM.bind_eq,
    EffectM.pure_eq, mlir_effect, mlir_env, Env.init, program.args,
    Operation.memcpy, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange, Env.writeMany_nil, Exit.run, Regs.read_nil,
    Func.continue, scratch, GlobalState.allocaPtr, GlobalState.alloca_alloc,
    Nat.add_assoc, copyState, hgep, hd, hs, hdisjoint, throwUBIf,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20]

/-- The same body result with the RIR call's normal stack-frame erasure. -/
theorem program_call_of_calls (prim : Primitives) (r a : Pointer)
    (initial : GlobalState) (states : CallStates)
    (calls : BodyCalls prim initial r a states) :
    (program prim).call (program.args (.value r) (.value a)) initial =
      .value (.nil, {(copyState initial r (states 20)) with
        mem := (copyState initial r (states 20)).mem.eraseFrom initial.alloc.nextFreeBlock}) := by
  exact Func.call_of_run (program_run_of_calls prim r a initial states calls)

/-- info: 'Agave.Ed25519.Encoding.Decompress.Execution.Pow22501.program_run_of_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms program_run_of_calls

/-- info: 'Agave.Ed25519.Encoding.Decompress.Execution.Pow22501.program_call_of_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms program_call_of_calls

end Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
