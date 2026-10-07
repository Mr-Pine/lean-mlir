import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructor
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2Constructor
import SSA.Projects.Agave.Ed25519.Proof.Tables.Memory

/-!
# The imported table constructors' memory boundaries

Both constructors iterate over seven successor records in an eight-entry
1280-byte table. The current and next record bounds are derived from that
allocation. Their actual return blocks copy the constructed bytes to the
caller. These theorems do not assume or assert that those bytes contain odd
point multiples; that remaining theorem must execute the field/point calls.
-/
namespace Agave.Ed25519.Tables.ConstructorMemory

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

/-- Exact common induction, exit comparison, and typed record scaling. -/
theorem cursor_arithmetic : ∀ i : Fin 7,
    Operation.add {nsw := true, nuw := true} (.value (BitVec.ofNat 64 i.val)) (.value 1#64) =
      .value (BitVec.ofNat 64 (i.val + 1)) ∧
    Operation.icmp .eq (.value (BitVec.ofNat 64 (i.val + 1))) (.value 7#64) =
      .value (if i.val = 6 then 1#1 else 0#1) ∧
    Operation.gepInboundsIndex 160 (.value (BitVec.ofNat 64 i.val)) =
      .value ((160 * i.val : Nat) : Int) ∧
    Operation.gepInboundsIndex 160 (.value (BitVec.ofNat 64 (i.val + 1))) =
      .value ((160 * (i.val + 1) : Nat) : Int) := by
  decide +kernel

/-- Every current and next record, including the last one, is wholly live. -/
theorem record_bounds (h : Buffer mem table 1280) (i : Fin 7) :
    Buffer mem (table.add (BitVec.ofNat 64 (160 * i.val))) 160 ∧
    Buffer mem (table.add (BitVec.ofNat 64 (160 * (i.val + 1)))) 160 := by
  constructor
  · exact h.slice _ _ (by have := i.isLt; omega)
  · exact h.slice _ _ (by have := i.isLt; omega)

/-- All emitted address promises follow from the outer table allocation. -/
theorem record_geps (h : Buffer mem table 1280) (i : Fin 7) :
    Operation.gepInboundsLive mem (.value table)
      [Operation.gepInboundsIndex 160 (.value (BitVec.ofNat 64 i.val))] =
        .value (table.add (BitVec.ofNat 64 (160 * i.val))) ∧
    Operation.gepInboundsLive mem (.value table)
      [Operation.gepInboundsIndex 160 (.value (BitVec.ofNat 64 (i.val + 1)))] =
        .value (table.add (BitVec.ofNat 64 (160 * (i.val + 1)))) := by
  obtain ⟨_, _, hcurrent, hnext⟩ := cursor_arithmetic i
  constructor
  · rw [hcurrent]
    exact h.gep _ (by have := i.isLt; omega)
  · rw [hnext]
    exact h.gep _ (by have := i.isLt; omega)

/-- The common real final memcpy; caller and scratch ranges derive its checks. -/
theorem copy_table (E : ⟪Γ⟫) (s : GlobalState) (out table : Pointer)
    (hout : Buffer s.mem out 1280) (htable : Buffer s.mem table 1280)
    (hseparate : out.id ≠ table.id) :
    Operation.memcpy (.value out) (.value table) (.value 1280#64) E s =
      .value (E, {s with mem := s.mem.storeAt out (s.mem.readAt table 10240)}) := by
  exact run_memcpy (n := 1280) (env := E) (s := s)
    (show (1280#64).toNat = 1280 from rfl)
    (Range.disjoint_of_id_ne hseparate) hout.fits htable.fits

def serialReturnInput (E : ⟪SerialConstructor.kernel.Γ⟫) (table : Pointer) :
    ⟪SerialConstructor.kernel.Γ⟫ :=
  E[%28 := .value 1280#64, %36 := .value table]

/-- The exact serial return block, including its compiler memcpy. -/
theorem serial_return_block (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState)
    (out table : Pointer) (hout : Buffer s.mem out 1280)
    (htable : Buffer s.mem table 1280) (hseparate : out.id ≠ table.id)
    (harg : E.read (%arg0) = .value out) :
    SerialConstructor.kernel.bb1.run SerialConstructor.kernel.blockParams
      (serialReturnInput E table) s =
      .value ((serialReturnInput E table, .inl .nil),
        {s with mem := s.mem.storeAt out (s.mem.readAt table 10240)}) := by
  change E.args 0 = .value out at harg
  have hcopy (env : ⟪SerialConstructor.kernel.Γ⟫) :=
    copy_table env s out table hout htable hseparate
  simp [BasicBlock.run, SerialConstructor.kernel.bb1, serialReturnInput,
    List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, harg, hcopy, Exit.run, Regs.read_nil]

theorem serial_return_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out table : Pointer)
    (hout : Buffer s.mem out 1280) (htable : Buffer s.mem table 1280)
    (hseparate : out.id ≠ table.id) (harg : E.read (%arg0) = .value out) :
    (SerialConstructor.kernel p g).runFrom (serialReturnInput E table) 1 s =
      .value (.nil, {s with mem := s.mem.storeAt out (s.mem.readAt table 10240)}) := by
  rw [Func.runFrom_eq,
    show (SerialConstructor.kernel p g).blocks 1 = SerialConstructor.kernel.bb1 from rfl,
    serial_return_block E s out table hout htable hseparate harg]
  rfl

def avx2ReturnInput (E : ⟪Avx2Constructor.kernel.Γ⟫) (table : Pointer) :
    ⟪Avx2Constructor.kernel.Γ⟫ :=
  E[%351 := .value 1280#64, %360 := .value table]

/-- The exact AVX2 return block performs the same 1280-byte copy. -/
theorem avx2_return_block (E : ⟪Avx2Constructor.kernel.Γ⟫) (s : GlobalState)
    (out table : Pointer) (hout : Buffer s.mem out 1280)
    (htable : Buffer s.mem table 1280) (hseparate : out.id ≠ table.id)
    (harg : E.read (%arg0) = .value out) :
    Avx2Constructor.kernel.bb1.run Avx2Constructor.kernel.blockParams
      (avx2ReturnInput E table) s =
      .value ((avx2ReturnInput E table, .inl .nil),
        {s with mem := s.mem.storeAt out (s.mem.readAt table 10240)}) := by
  change E.args 0 = .value out at harg
  have hcopy (env : ⟪Avx2Constructor.kernel.Γ⟫) :=
    copy_table env s out table hout htable hseparate
  simp [BasicBlock.run, Avx2Constructor.kernel.bb1, avx2ReturnInput,
    List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, harg, hcopy, Exit.run, Regs.read_nil]

theorem avx2_return_run (p : Avx2Constructor.Primitives)
    (E : ⟪Avx2Constructor.kernel.Γ⟫) (s : GlobalState) (out table : Pointer)
    (hout : Buffer s.mem out 1280) (htable : Buffer s.mem table 1280)
    (hseparate : out.id ≠ table.id) (harg : E.read (%arg0) = .value out) :
    (Avx2Constructor.kernel p).runFrom (avx2ReturnInput E table) 1 s =
      .value (.nil, {s with mem := s.mem.storeAt out (s.mem.readAt table 10240)}) := by
  rw [Func.runFrom_eq,
    show (Avx2Constructor.kernel p).blocks 1 = Avx2Constructor.kernel.bb1 from rfl,
    avx2_return_block E s out table hout htable hseparate harg]
  rfl

end Agave.Ed25519.Tables.ConstructorMemory
