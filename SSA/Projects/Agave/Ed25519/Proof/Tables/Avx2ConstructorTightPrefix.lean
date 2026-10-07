import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorNormalizationRepresentation

/-! The constructor's contiguous 105-instruction packing and initial carry
interval accepts the verifier's full Tight input invariant. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.TightPrefix
open LeanMLIR.RIR Packing Normalization CachePhases Avx2PointAdd Avx2PointAdd.Phases
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def constants (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  E[%28 := Ty.wrap shifts, %29 := Ty.wrap masks,
    %30 := Ty.wrap (#v[0,0,127,127,0,0,127,127] : V32),
    %31 := Ty.poisoned (.vec 8 32), %32 := Vector.replicate 4 (.value 19#64)]

def entry (E : ⟪kernel.Γ⟫) (a : SerialPoint) : ⟪kernel.Γ⟫ :=
  Packing.input (constants E) a

def packed (E : ⟪kernel.Γ⟫) (a : SerialPoint) : ⟪kernel.Γ⟫ :=
  Packing.result (entry E a)

private theorem packed_constant_28 (E : ⟪kernel.Γ⟫) :
    (Packing.result E).read (%28) = E.read (%28) := by
  unfold Packing.result
  extract_lets
  simp (disch := decide) only [Env.read_write_ne]

private theorem packed_constant_29 (E : ⟪kernel.Γ⟫) :
    (Packing.result E).read (%29) = E.read (%29) := by
  unfold Packing.result
  extract_lets
  simp (disch := decide) only [Env.read_write_ne]

private theorem packed_constant_30 (E : ⟪kernel.Γ⟫) :
    (Packing.result E).read (%30) = E.read (%30) := by
  unfold Packing.result
  extract_lets
  simp (disch := decide) only [Env.read_write_ne]

private theorem packed_constant_31 (E : ⟪kernel.Γ⟫) :
    (Packing.result E).read (%31) = E.read (%31) := by
  unfold Packing.result
  extract_lets
  simp (disch := decide) only [Env.read_write_ne]

private theorem packed_constant_32 (E : ⟪kernel.Γ⟫) :
    (Packing.result E).read (%32) = E.read (%32) := by
  unfold Packing.result
  extract_lets
  simp (disch := decide) only [Env.read_write_ne]

/-- Resetting the normalization interface is an identity: every input register
already has the required value from the preceding imported packing interval. -/
theorem packed_ready (E : ⟪kernel.Γ⟫) (a : SerialPoint) :
    Normalization.input (packed E a) a = packed E a := by
  have h28 : (packed E a).read (%28) = Ty.wrap shifts := by
    rw [packed, packed_constant_28]
    simp (disch := decide) only [entry, Packing.input, constants, mlir_env]
  have h29 : (packed E a).read (%29) = Ty.wrap masks := by
    rw [packed, packed_constant_29]
    simp (disch := decide) only [entry, Packing.input, constants, mlir_env]
  have h30 : (packed E a).read (%30) = Ty.wrap (#v[0,0,127,127,0,0,127,127] : V32) := by
    rw [packed, packed_constant_30]
    simp (disch := decide) only [entry, Packing.input, constants, mlir_env]
  have h31 : (packed E a).read (%31) = Ty.poisoned (.vec 8 32) := by
    rw [packed, packed_constant_31]
    simp (disch := decide) only [entry, Packing.input, constants, mlir_env]
  have h32 : (packed E a).read (%32) = Vector.replicate 4 (.value 19#64) := by
    rw [packed, packed_constant_32]
    simp (disch := decide) only [entry, Packing.input, constants, mlir_env]
  have h0 : (packed E a).read (%415) = Ty.wrap (pack a 0) := by
    have h := Packing.reads_result (constants E) a 0
    simpa [Packing.reads, packed, entry] using h
  have h1 : (packed E a).read (%431) = Ty.wrap (pack a 1) := by
    have h := Packing.reads_result (constants E) a 1
    simpa [Packing.reads, packed, entry] using h
  have h2 : (packed E a).read (%447) = Ty.wrap (pack a 2) := by
    have h := Packing.reads_result (constants E) a 2
    simpa [Packing.reads, packed, entry] using h
  have h3 : (packed E a).read (%463) = Ty.wrap (pack a 3) := by
    have h := Packing.reads_result (constants E) a 3
    simpa [Packing.reads, packed, entry] using h
  have h4 : (packed E a).read (%479) = Ty.wrap (pack a 4) := by
    have h := Packing.reads_result (constants E) a 4
    simpa [Packing.reads, packed, entry] using h
  unfold Normalization.input
  rw [Env.write_of_read (packed E a) (%28) h28, Env.write_of_read (packed E a) (%29) h29,
    Env.write_of_read (packed E a) (%30) h30, Env.write_of_read (packed E a) (%31) h31, Env.write_of_read (packed E a) (%32) h32,
    Env.write_of_read (packed E a) (%415) h0, Env.write_of_read (packed E a) (%431) h1, Env.write_of_read (packed E a) (%447) h2,
    Env.write_of_read (packed E a) (%463) h3, Env.write_of_read (packed E a) (%479) h4]

theorem runSlice_add (block : BasicBlock Γ tRets bp)
    (E E1 E2 : ⟪Γ⟫) (start n m : Nat) (s s1 s2 : GlobalState)
    (h1 : runSlice block E start n s = .value (E1,s1))
    (h2 : runSlice block E1 (start+n) m s1 = .value (E2,s2)) :
    runSlice block E start (n+m) s = .value (E2,s2) := by
  unfold runSlice
  rw [List.take_add, List.foldlM_append]
  change (runSlice block E start n s >>= fun es =>
    List.foldlM Instr.run es.1 (((block.body.drop start).drop n).take m) es.2) = _
  rw [h1]
  simpa only [runSlice, PoisonOr.value_bind, List.drop_drop, Nat.add_comm] using h2

def result (E : ⟪kernel.Γ⟫) (a : SerialPoint) : ⟪kernel.Γ⟫ :=
  normalizeResult (packed E a)

/-- Exact unchanged bb0 interval: input packing, carry propagation, top fold. -/
theorem run_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (a : SerialPoint)
    (s : GlobalState) :
    runSlice (kernel.bb0 p) (entry E a) 400 105 s = .value (result E a,s) := by
  apply runSlice_add _ _ (packed E a) _ 400 80 25 s s s (Packing.run_slice p _ s)
  exact runSlice_add _ _ (normalize0 (packed E a)) _ 480 15 10 s s s
    (normalize0_slice p _ s) (normalize1_slice p _ s)

theorem reads_result (E : ⟪kernel.Γ⟫) (a : SerialPoint) (k : Fin 5) :
    Normalization.reads (result E a) k = Ty.wrap (packPoint (normalizedPoint a) k) := by
  have h := network_point (packed E a) a k
  rw [packed_ready] at h
  exact h

/-- Local execution refinement at the real verifier's Tight bound. The entire
state, including memory and globals, is unchanged by this pure source interval. -/
theorem tight_run (p : Primitives) (E : ⟪kernel.Γ⟫) (a : SerialPoint)
    (s : GlobalState) (ha : ∀ e k, (a e k).toNat < 2^52) :
    runSlice (kernel.bb0 p) (entry E a) 400 105 s = .value (result E a,s) ∧
    (∀ k, Normalization.reads (result E a) k = Ty.wrap (packPoint (normalizedPoint a) k)) ∧
    pointReduced (normalizedPoint a) ∧
    pointValue (normalizedPoint a) = serialPointValue a :=
  ⟨run_slice p E a s, reads_result E a, normalized_reduced a ha, normalized_value a ha⟩

/-- The same result reconnects directly to the original remaining bb0 body. -/
theorem tight_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (a : SerialPoint)
    (s : GlobalState) (ha : ∀ e k, (a e k).toNat < 2^52) :
    (kernel.bb0 p).runBodyFrom (entry E a) 400 s =
      (kernel.bb0 p).runBodyFrom (result E a) 505 s ∧
    (∀ k, Normalization.reads (result E a) k = Ty.wrap (packPoint (normalizedPoint a) k)) ∧
    pointReduced (normalizedPoint a) ∧
    pointValue (normalizedPoint a) = serialPointValue a :=
  ⟨runBodyFrom_slice _ _ _ 400 105 s s (run_slice p E a s),
    reads_result E a, normalized_reduced a ha, normalized_value a ha⟩

end Agave.Ed25519.Tables.Avx2Constructor.TightPrefix
