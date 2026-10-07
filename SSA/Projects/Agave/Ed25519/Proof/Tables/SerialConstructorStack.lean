import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorRegisters
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorContext
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialPrefixMemory

namespace Agave.Ed25519.Tables.SerialConstructorStack
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase.RIR (PrefixEq)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def stackSize : Nat → Nat
  | 0 => 120
  | 1 | 2 | 3 | 4 | 5 | 6 => 160
  | 7 => 1280
  | _ => 0

def stack (s : GlobalState) : Nat → GlobalState
  | 0 => s
  | n + 1 => (stack s n).alloca (stackSize n)

def stackPtr (s : GlobalState) (n : Nat) : Pointer := (stack s n).allocaPtr

theorem stack_wf (hwf : s.WF) (n : Nat) : (stack s n).WF := by
  induction n with
  | zero => exact hwf
  | succ n ih => exact ih.alloca

theorem stack_existing (hwf : s.WF) (h : Buffer s.mem q bytes) (n : Nat) :
    Buffer (stack s n).mem q bytes := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca_existing (stack_wf hwf n) _

theorem stack_read_existing (hwf : s.WF) (h : Buffer s.mem q bytes)
    (n bits : Nat) : (stack s n).mem.readAt q bits = s.mem.readAt q bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((stack s n).alloca _).mem.readAt q bits = _
    rw [MemoryState.readAt_alloca (stack_wf hwf n)
      (stack_existing hwf h n).fits, ih]

theorem stack_buffer (hwf : s.WF) (i n : Nat) (hi : i < n)
    (hsize : stackSize i < 2 ^ 63) :
    Buffer (stack s n).mem (stackPtr s i) (stackSize i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : i = n
    · subst i
      exact Buffer.alloca _ _ hsize
    · exact (ih (by omega)).alloca_existing (stack_wf hwf n) _

theorem stack_separate_caller (hwf : s.WF) (h : Buffer s.mem q bytes)
    (n : Nat) : (stackPtr s n).id ≠ q.id :=
  (GlobalState.ne_allocaPtr_of_fits (stack_wf hwf n)
    (stack_existing hwf h n).fits).symm

theorem stack_counter (s : GlobalState) (n : Nat) :
    (stack s n).alloc.nextFreeBlock = s.alloc.nextFreeBlock + n := by
  induction n with
  | zero => simp [stack]
  | succ n ih => simp only [stack, GlobalState.alloca, ih, Nat.add_assoc]

theorem stackPtr_id (s : GlobalState) (n : Nat) :
    (stackPtr s n).id.id = s.alloc.nextFreeBlock + n := by
  exact stack_counter s n

theorem stack_separate (s : GlobalState) (i j : Nat) (hij : i ≠ j) :
    (stackPtr s i).id ≠ (stackPtr s j).id := by
  intro heq
  have hv := congrArg BlockId.id heq
  rw [stackPtr_id, stackPtr_id] at hv
  omega

theorem stack_globals (hg : SerialConstructorContext.GlobalsReady g s) (hwf : s.WF)
    (n : Nat) : SerialConstructorContext.GlobalsReady g (stack s n) := by
  induction n with
  | zero => exact hg
  | succ n ih => exact ih.alloca (stack_wf hwf n)

def constants (E : ⟪SerialConstructor.kernel.Γ⟫) (g : SerialConstructor.Globals) :
    ⟪SerialConstructor.kernel.Γ⟫ :=
  E[%0 := .value 1#32,
    %1 := .value 40#64,
    %2 := .value 48#64,
    %3 := .value 56#64,
    %4 := .value 64#64,
    %5 := .value 72#64,
    %6 := .value 8#64,
    %7 := .value 16#64,
    %8 := .value 24#64,
    %9 := .value 32#64,
    %10 := .value 36028797018963664#64,
    %11 := .value 36028797018963952#64,
    %12 := .value 51#64,
    %13 := .value 2251799813685247#64,
    %14 := .value 19#64,
    %15 := .value 80#64,
    %16 := .value 120#64,
    %17 := .value g.address0,
    %18 := .value 160#64,
    %19 := .value 320#64,
    %20 := .value 480#64,
    %21 := .value 640#64,
    %22 := .value 800#64,
    %23 := .value 960#64,
    %24 := .value 1120#64,
    %25 := .value 0#64,
    %26 := .value 1#64,
    %27 := .value 7#64,
    %28 := .value 1280#64]

theorem constants_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) :
    List.foldlM Instr.run E ((SerialConstructor.kernel.bb0 p g).body.take 29) s =
      .value (constants E g, s) := by
  simp [SerialConstructor.kernel.bb0, constants, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Ty.wrap, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]

/-- Constants need not be replayed when entering a source-body fragment. -/
theorem constants_of_prefix (E F : ⟪SerialConstructor.kernel.Γ⟫)
    (g : SerialConstructor.Globals) (h : PrefixEq (constants E g) F 29) :
    constants F g = F := by
  have h0 : F.read (%0) = .value 1#32 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h1 : F.read (%1) = .value 40#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h2 : F.read (%2) = .value 48#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h3 : F.read (%3) = .value 56#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h4 : F.read (%4) = .value 64#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h5 : F.read (%5) = .value 72#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h6 : F.read (%6) = .value 8#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h7 : F.read (%7) = .value 16#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h8 : F.read (%8) = .value 24#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h9 : F.read (%9) = .value 32#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h10 : F.read (%10) = .value 36028797018963664#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h11 : F.read (%11) = .value 36028797018963952#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h12 : F.read (%12) = .value 51#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h13 : F.read (%13) = .value 2251799813685247#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h14 : F.read (%14) = .value 19#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h15 : F.read (%15) = .value 80#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h16 : F.read (%16) = .value 120#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h17 : F.read (%17) = .value g.address0 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h18 : F.read (%18) = .value 160#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h19 : F.read (%19) = .value 320#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h20 : F.read (%20) = .value 480#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h21 : F.read (%21) = .value 640#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h22 : F.read (%22) = .value 800#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h23 : F.read (%23) = .value 960#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h24 : F.read (%24) = .value 1120#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h25 : F.read (%25) = .value 0#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h26 : F.read (%26) = .value 1#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h27 : F.read (%27) = .value 7#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  have h28 : F.read (%28) = .value 1280#64 := by
    rw [h.read _ (by intro i ht he; cases he; decide)]
    simp [constants, mlir_env]
  unfold constants
  rw [Env.write_of_read F (%0) h0,
    Env.write_of_read F (%1) h1,
    Env.write_of_read F (%2) h2,
    Env.write_of_read F (%3) h3,
    Env.write_of_read F (%4) h4,
    Env.write_of_read F (%5) h5,
    Env.write_of_read F (%6) h6,
    Env.write_of_read F (%7) h7,
    Env.write_of_read F (%8) h8,
    Env.write_of_read F (%9) h9,
    Env.write_of_read F (%10) h10,
    Env.write_of_read F (%11) h11,
    Env.write_of_read F (%12) h12,
    Env.write_of_read F (%13) h13,
    Env.write_of_read F (%14) h14,
    Env.write_of_read F (%15) h15,
    Env.write_of_read F (%16) h16,
    Env.write_of_read F (%17) h17,
    Env.write_of_read F (%18) h18,
    Env.write_of_read F (%19) h19,
    Env.write_of_read F (%20) h20,
    Env.write_of_read F (%21) h21,
    Env.write_of_read F (%22) h22,
    Env.write_of_read F (%23) h23,
    Env.write_of_read F (%24) h24,
    Env.write_of_read F (%25) h25,
    Env.write_of_read F (%26) h26,
    Env.write_of_read F (%27) h27,
    Env.write_of_read F (%28) h28]

def initial (E : ⟪SerialConstructor.kernel.Γ⟫) (g : SerialConstructor.Globals)
    (s : GlobalState) : ⟪SerialConstructor.kernel.Γ⟫ :=
  (constants E g)[%29 := .value (stackPtr s 0),
    %30 := .value (stackPtr s 1),
    %31 := .value (stackPtr s 2),
    %32 := .value (stackPtr s 3),
    %33 := .value (stackPtr s 4),
    %34 := .value (stackPtr s 5),
    %35 := .value (stackPtr s 6),
    %36 := .value (stackPtr s 7)]

theorem initial_prefix (E : ⟪SerialConstructor.kernel.Γ⟫)
    (g : SerialConstructor.Globals) (s : GlobalState) :
    PrefixEq (constants E g) (initial E g s) 29 := by
  unfold initial
  iterate 8 apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

private theorem modifyGet_run {α : Type} (f : GlobalState → α × GlobalState)
    (s : GlobalState) : (modifyGet f : EffectM α) s = .value (f s) := rfl

/-- Exact 29 constants and eight allocations of the original entry body. -/
theorem initial_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) :
    List.foldlM Instr.run E ((SerialConstructor.kernel.bb0 p g).body.take 37) s =
      .value (initial E g s, stack s 8) := by
  simp [SerialConstructor.kernel.bb0, initial, constants, stack, stackSize, stackPtr,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Ty.wrap, EffectM.bind_eq,
    EffectM.pure_eq, PoisonOr.value_bind, modifyGet_run]

end Agave.Ed25519.Tables.SerialConstructorStack
