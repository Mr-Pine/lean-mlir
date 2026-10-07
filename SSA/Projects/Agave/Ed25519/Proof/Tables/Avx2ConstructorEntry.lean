import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorConstantValues
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorLoads
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs

/-! Entry through the first reduced packed point, with the actual constructor
constants, stack allocations, input loads, and instruction stream. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Entry
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2PointAdd.CFG (runSlice)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def allocated (E : ⟪kernel.Γ⟫) (s : GlobalState) : ⟪kernel.Γ⟫ :=
  Stack.result (Constants.result E) s

def loaded (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) : ⟪kernel.Γ⟫ :=
  Loads.result (allocated E s) (Stack.state s 9).mem a

theorem register_frame (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) :
    RegisterFrame 352 400 (Constants.result E) (loaded E s a) :=
  ((Stack.register_frame (Constants.result E) s).weaken (by decide) (by decide)).trans
    ((Loads.register_frame (allocated E s) (Stack.state s 9).mem a).weaken
      (by decide) (by decide))

theorem load_input_ready (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    Loads.input (allocated E s) = allocated E s := by
  have h1 : (allocated E s).read (%1) = .value 8#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%1) (by decide)).trans (Constants.read_1 E)
  have h2 : (allocated E s).read (%2) = .value 16#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%2) (by decide)).trans (Constants.read_2 E)
  have h3 : (allocated E s).read (%3) = .value 24#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%3) (by decide)).trans (Constants.read_3 E)
  have h4 : (allocated E s).read (%4) = .value 32#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%4) (by decide)).trans (Constants.read_4 E)
  have h5 : (allocated E s).read (%5) = .value 40#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%5) (by decide)).trans (Constants.read_5 E)
  have h6 : (allocated E s).read (%6) = .value 48#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%6) (by decide)).trans (Constants.read_6 E)
  have h7 : (allocated E s).read (%7) = .value 56#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%7) (by decide)).trans (Constants.read_7 E)
  have h8 : (allocated E s).read (%8) = .value 64#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%8) (by decide)).trans (Constants.read_8 E)
  have h9 : (allocated E s).read (%9) = .value 72#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%9) (by decide)).trans (Constants.read_9 E)
  have h10 : (allocated E s).read (%10) = .value 80#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%10) (by decide)).trans (Constants.read_10 E)
  have h11 : (allocated E s).read (%11) = .value 88#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%11) (by decide)).trans (Constants.read_11 E)
  have h12 : (allocated E s).read (%12) = .value 96#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%12) (by decide)).trans (Constants.read_12 E)
  have h13 : (allocated E s).read (%13) = .value 104#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%13) (by decide)).trans (Constants.read_13 E)
  have h14 : (allocated E s).read (%14) = .value 112#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%14) (by decide)).trans (Constants.read_14 E)
  have h15 : (allocated E s).read (%15) = .value 120#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%15) (by decide)).trans (Constants.read_15 E)
  have h16 : (allocated E s).read (%16) = .value 128#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%16) (by decide)).trans (Constants.read_16 E)
  have h17 : (allocated E s).read (%17) = .value 136#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%17) (by decide)).trans (Constants.read_17 E)
  have h18 : (allocated E s).read (%18) = .value 144#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%18) (by decide)).trans (Constants.read_18 E)
  have h19 : (allocated E s).read (%19) = .value 152#64 :=
    ((Stack.register_frame (Constants.result E) s).read (%19) (by decide)).trans (Constants.read_19 E)
  unfold Loads.input
  rw [Env.write_of_read (allocated E s) (%1) h1,
    Env.write_of_read (allocated E s) (%2) h2,
    Env.write_of_read (allocated E s) (%3) h3,
    Env.write_of_read (allocated E s) (%4) h4,
    Env.write_of_read (allocated E s) (%5) h5,
    Env.write_of_read (allocated E s) (%6) h6,
    Env.write_of_read (allocated E s) (%7) h7,
    Env.write_of_read (allocated E s) (%8) h8,
    Env.write_of_read (allocated E s) (%9) h9,
    Env.write_of_read (allocated E s) (%10) h10,
    Env.write_of_read (allocated E s) (%11) h11,
    Env.write_of_read (allocated E s) (%12) h12,
    Env.write_of_read (allocated E s) (%13) h13,
    Env.write_of_read (allocated E s) (%14) h14,
    Env.write_of_read (allocated E s) (%15) h15,
    Env.write_of_read (allocated E s) (%16) h16,
    Env.write_of_read (allocated E s) (%17) h17,
    Env.write_of_read (allocated E s) (%18) h18,
    Env.write_of_read (allocated E s) (%19) h19]

theorem packing_input_ready (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) :
    TightPrefix.entry (loaded E s a) (Loads.point (Stack.state s 9).mem a) = loaded E s a := by
  have h20 : (loaded E s a).read (%20) = Ty.poisoned (.vec 4 32) :=
    ((register_frame E s a).read (%20) (by decide)).trans (Constants.read_20 E)
  have h21 : (loaded E s a).read (%21) = .value 0#64 :=
    ((register_frame E s a).read (%21) (by decide)).trans (Constants.read_21 E)
  have h22 : (loaded E s a).read (%22) = .value 1#64 :=
    ((register_frame E s a).read (%22) (by decide)).trans (Constants.read_22 E)
  have h23 : (loaded E s a).read (%23) = .value 2#64 :=
    ((register_frame E s a).read (%23) (by decide)).trans (Constants.read_23 E)
  have h24 : (loaded E s a).read (%24) = .value 3#64 :=
    ((register_frame E s a).read (%24) (by decide)).trans (Constants.read_24 E)
  have h25 : (loaded E s a).read (%25) = Vector.replicate 4 (.value 67108863#32) :=
    ((register_frame E s a).read (%25) (by decide)).trans (Constants.read_25 E)
  have h26 : (loaded E s a).read (%26) = Ty.poisoned (.vec 4 64) :=
    ((register_frame E s a).read (%26) (by decide)).trans (Constants.read_26 E)
  have h27 : (loaded E s a).read (%27) = Vector.replicate 4 (.value 26#64) :=
    ((register_frame E s a).read (%27) (by decide)).trans (Constants.read_27 E)
  have h28 : (loaded E s a).read (%28) = Ty.wrap Normalization.shifts :=
    by simpa [Ty.wrap_vec, Normalization.shifts, Normalization.masks] using
      ((register_frame E s a).read (%28) (by decide)).trans (Constants.read_28 E)
  have h29 : (loaded E s a).read (%29) = Ty.wrap Normalization.masks :=
    by simpa [Ty.wrap_vec, Normalization.shifts, Normalization.masks] using
      ((register_frame E s a).read (%29) (by decide)).trans (Constants.read_29 E)
  have h30 : (loaded E s a).read (%30) = Ty.wrap (#v[0,0,127,127,0,0,127,127] : Vector (BitVec 32) 8) :=
    by simpa [Ty.wrap_vec, Normalization.shifts, Normalization.masks] using
      ((register_frame E s a).read (%30) (by decide)).trans (Constants.read_30 E)
  have h31 : (loaded E s a).read (%31) = Ty.poisoned (.vec 8 32) :=
    ((register_frame E s a).read (%31) (by decide)).trans (Constants.read_31 E)
  have h32 : (loaded E s a).read (%32) = Vector.replicate 4 (.value 19#64) :=
    ((register_frame E s a).read (%32) (by decide)).trans (Constants.read_32 E)
  have h361 : (loaded E s a).read (%361) =
      .value (Loads.point (Stack.state s 9).mem a 0 0) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 0 0
    simpa [Loads.reads, loaded] using h
  have h363 : (loaded E s a).read (%363) =
      .value (Loads.point (Stack.state s 9).mem a 0 1) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 0 1
    simpa [Loads.reads, loaded] using h
  have h365 : (loaded E s a).read (%365) =
      .value (Loads.point (Stack.state s 9).mem a 0 2) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 0 2
    simpa [Loads.reads, loaded] using h
  have h367 : (loaded E s a).read (%367) =
      .value (Loads.point (Stack.state s 9).mem a 0 3) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 0 3
    simpa [Loads.reads, loaded] using h
  have h369 : (loaded E s a).read (%369) =
      .value (Loads.point (Stack.state s 9).mem a 0 4) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 0 4
    simpa [Loads.reads, loaded] using h
  have h371 : (loaded E s a).read (%371) =
      .value (Loads.point (Stack.state s 9).mem a 1 0) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 1 0
    simpa [Loads.reads, loaded] using h
  have h373 : (loaded E s a).read (%373) =
      .value (Loads.point (Stack.state s 9).mem a 1 1) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 1 1
    simpa [Loads.reads, loaded] using h
  have h375 : (loaded E s a).read (%375) =
      .value (Loads.point (Stack.state s 9).mem a 1 2) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 1 2
    simpa [Loads.reads, loaded] using h
  have h377 : (loaded E s a).read (%377) =
      .value (Loads.point (Stack.state s 9).mem a 1 3) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 1 3
    simpa [Loads.reads, loaded] using h
  have h379 : (loaded E s a).read (%379) =
      .value (Loads.point (Stack.state s 9).mem a 1 4) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 1 4
    simpa [Loads.reads, loaded] using h
  have h381 : (loaded E s a).read (%381) =
      .value (Loads.point (Stack.state s 9).mem a 2 0) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 2 0
    simpa [Loads.reads, loaded] using h
  have h383 : (loaded E s a).read (%383) =
      .value (Loads.point (Stack.state s 9).mem a 2 1) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 2 1
    simpa [Loads.reads, loaded] using h
  have h385 : (loaded E s a).read (%385) =
      .value (Loads.point (Stack.state s 9).mem a 2 2) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 2 2
    simpa [Loads.reads, loaded] using h
  have h387 : (loaded E s a).read (%387) =
      .value (Loads.point (Stack.state s 9).mem a 2 3) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 2 3
    simpa [Loads.reads, loaded] using h
  have h389 : (loaded E s a).read (%389) =
      .value (Loads.point (Stack.state s 9).mem a 2 4) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 2 4
    simpa [Loads.reads, loaded] using h
  have h391 : (loaded E s a).read (%391) =
      .value (Loads.point (Stack.state s 9).mem a 3 0) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 3 0
    simpa [Loads.reads, loaded] using h
  have h393 : (loaded E s a).read (%393) =
      .value (Loads.point (Stack.state s 9).mem a 3 1) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 3 1
    simpa [Loads.reads, loaded] using h
  have h395 : (loaded E s a).read (%395) =
      .value (Loads.point (Stack.state s 9).mem a 3 2) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 3 2
    simpa [Loads.reads, loaded] using h
  have h397 : (loaded E s a).read (%397) =
      .value (Loads.point (Stack.state s 9).mem a 3 3) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 3 3
    simpa [Loads.reads, loaded] using h
  have h399 : (loaded E s a).read (%399) =
      .value (Loads.point (Stack.state s 9).mem a 3 4) := by
    have h := Loads.reads_result (allocated E s) (Stack.state s 9).mem a 3 4
    simpa [Loads.reads, loaded] using h
  unfold TightPrefix.entry TightPrefix.constants Packing.input
  rw [Env.write_of_read (loaded E s a) (%28) h28,
    Env.write_of_read (loaded E s a) (%29) h29,
    Env.write_of_read (loaded E s a) (%30) h30,
    Env.write_of_read (loaded E s a) (%31) h31,
    Env.write_of_read (loaded E s a) (%32) h32,
    Env.write_of_read (loaded E s a) (%20) h20,
    Env.write_of_read (loaded E s a) (%21) h21,
    Env.write_of_read (loaded E s a) (%22) h22,
    Env.write_of_read (loaded E s a) (%23) h23,
    Env.write_of_read (loaded E s a) (%24) h24,
    Env.write_of_read (loaded E s a) (%25) h25,
    Env.write_of_read (loaded E s a) (%26) h26,
    Env.write_of_read (loaded E s a) (%27) h27,
    Env.write_of_read (loaded E s a) (%361) h361,
    Env.write_of_read (loaded E s a) (%363) h363,
    Env.write_of_read (loaded E s a) (%365) h365,
    Env.write_of_read (loaded E s a) (%367) h367,
    Env.write_of_read (loaded E s a) (%369) h369,
    Env.write_of_read (loaded E s a) (%371) h371,
    Env.write_of_read (loaded E s a) (%373) h373,
    Env.write_of_read (loaded E s a) (%375) h375,
    Env.write_of_read (loaded E s a) (%377) h377,
    Env.write_of_read (loaded E s a) (%379) h379,
    Env.write_of_read (loaded E s a) (%381) h381,
    Env.write_of_read (loaded E s a) (%383) h383,
    Env.write_of_read (loaded E s a) (%385) h385,
    Env.write_of_read (loaded E s a) (%387) h387,
    Env.write_of_read (loaded E s a) (%389) h389,
    Env.write_of_read (loaded E s a) (%391) h391,
    Env.write_of_read (loaded E s a) (%393) h393,
    Env.write_of_read (loaded E s a) (%395) h395,
    Env.write_of_read (loaded E s a) (%397) h397,
    Env.write_of_read (loaded E s a) (%399) h399]

def result (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) : ⟪kernel.Γ⟫ :=
  TightPrefix.result (loaded E s a) (Loads.point (Stack.state s 9).mem a)

theorem run (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer)
    (hwf : s.WF) (ha : Buffer s.mem a 160) (harg : E.read (%arg1) = .value a) :
    runSlice (kernel.bb0 p) E 0 505 s = .value (result E s a, Stack.state s 9) := by
  have hc := Constants.run p E s
  have hs := Stack.run p (Constants.result E) s (Constants.read_0 E)
  have hcs := TightPrefix.runSlice_add (kernel.bb0 p) E (Constants.result E)
    (allocated E s) 0 352 9 s s (Stack.state s 9) hc hs
  have harg' : (allocated E s).read (%arg1) = .value a := by
    unfold allocated
    rw [(Stack.register_frame (Constants.result E) s).read (%arg1) (by trivial),
      (Constants.register_frame E).read (%arg1) (by trivial), harg]
  have hl := Loads.run p (allocated E s) (Stack.state s 9) a
    (Stack.live hwf ha 9) harg'
  rw [load_input_ready] at hl
  have hcsl := TightPrefix.runSlice_add (kernel.bb0 p) E (allocated E s)
    (loaded E s a) 0 361 39 s (Stack.state s 9) (Stack.state s 9) hcs hl
  have hp := TightPrefix.run_slice p (loaded E s a)
    (Loads.point (Stack.state s 9).mem a) (Stack.state s 9)
  rw [packing_input_ready] at hp
  exact TightPrefix.runSlice_add (kernel.bb0 p) E (loaded E s a)
    (result E s a) 0 400 105 s (Stack.state s 9) (Stack.state s 9) hcsl hp

theorem point_stack (s : GlobalState) (a : Pointer) (hwf : s.WF)
    (ha : Buffer s.mem a 160) :
    Loads.point (Stack.state s 9).mem a = Loads.point s.mem a := by
  funext e k
  apply Stack.read_existing hwf
  exact ha.slice (40*e.val + 8*k.val) 8 (by have := e.isLt; have := k.isLt; omega)

theorem serial_value (s : GlobalState) (a : Pointer) :
    Normalization.serialPointValue (Loads.point s.mem a) =
      Conformance.BackendExecution.readPoint s a := rfl

/-- The exact entry prefix establishes a reduced point with the caller's field
value. The serial input may use the complete verifier Tight bound. -/
theorem tight_run (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer)
    (hwf : s.WF) (ha : Buffer s.mem a 160) (harg : E.read (%arg1) = .value a)
    (htight : DoubleBase.ExecutionAvx2.serialLimbsBounded s a) :
    runSlice (kernel.bb0 p) E 0 505 s = .value (result E s a, Stack.state s 9) ∧
    (∀ k, Normalization.reads (result E s a) k =
      Ty.wrap (Avx2PointAdd.Phases.packPoint (Normalization.normalizedPoint
        (Loads.point s.mem a)) k)) ∧
    Avx2PointAdd.pointReduced (Normalization.normalizedPoint (Loads.point s.mem a)) ∧
    Avx2PointAdd.pointValue (Normalization.normalizedPoint (Loads.point s.mem a)) =
      Conformance.BackendExecution.readPoint s a := by
  refine ⟨run p E s a hwf ha harg, ?_, Normalization.normalized_reduced _ htight, ?_⟩
  · intro k
    have h := TightPrefix.reads_result (loaded E s a) (Loads.point (Stack.state s 9).mem a) k
    change Normalization.reads (result E s a) k = _ at h
    rw [point_stack s a hwf ha] at h
    exact h
  · exact (Normalization.normalized_value _ htight).trans (serial_value s a)

theorem continue_run (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer)
    (hwf : s.WF) (ha : Buffer s.mem a 160) (harg : E.read (%arg1) = .value a) :
    (kernel.bb0 p).runBodyFrom E 0 s =
      (kernel.bb0 p).runBodyFrom (result E s a) 505 (Stack.state s 9) :=
  Avx2PointAdd.CFG.runBodyFrom_slice _ _ _ 0 505 s (Stack.state s 9) (run p E s a hwf ha harg)

end Agave.Ed25519.Tables.Avx2Constructor.Entry
