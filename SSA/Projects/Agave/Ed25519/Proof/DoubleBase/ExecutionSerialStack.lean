import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialInit

/-! The twelve fresh allocations in the original serial entry block. All
scratch ranges and separation from caller allocations follow from `WF`. -/
namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

/-- Allocation sizes in the exact order of registers 30 through 41. -/
def serialStackSize : Nat → Nat
  | 0 | 1 => 40
  | 2 | 8 => 120
  | 3 | 4 | 5 | 6 | 7 => 160
  | 9 => 1280
  | 10 | 11 => 256
  | _ => 0

def serialStack (s : GlobalState) : Nat → GlobalState
  | 0 => s
  | n + 1 => (serialStack s n).alloca (serialStackSize n)

def serialStackPtr (s : GlobalState) (n : Nat) : Pointer := (serialStack s n).allocaPtr

theorem serialStack_wf (hwf : s.WF) (n : Nat) : (serialStack s n).WF := by
  induction n with
  | zero => exact hwf
  | succ n ih => exact ih.alloca

theorem serialStack_existing (hwf : s.WF) (h : Buffer s.mem q bytes) (n : Nat) :
    Buffer (serialStack s n).mem q bytes := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca_existing (serialStack_wf hwf n) _

theorem serialStack_read_existing (hwf : s.WF) (h : Buffer s.mem q bytes)
    (n bits : Nat) : (serialStack s n).mem.readAt q bits = s.mem.readAt q bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((serialStack s n).alloca _).mem.readAt q bits = _
    rw [MemoryState.readAt_alloca (serialStack_wf hwf n)
      (serialStack_existing hwf h n).fits, ih]

theorem serialStack_buffer (hwf : s.WF) (i n : Nat) (hi : i < n)
    (hsize : serialStackSize i < 2 ^ 63) :
    Buffer (serialStack s n).mem (serialStackPtr s i) (serialStackSize i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : i = n
    · subst i
      exact Buffer.alloca _ _ hsize
    · exact (ih (by omega)).alloca_existing (serialStack_wf hwf n) _

theorem serialStack_separate_caller (hwf : s.WF) (h : Buffer s.mem q bytes)
    (n : Nat) : (serialStackPtr s n).id ≠ q.id :=
  (GlobalState.ne_allocaPtr_of_fits (serialStack_wf hwf n)
    (serialStack_existing hwf h n).fits).symm

private theorem modifyGet_run {α : Type} (f : GlobalState → α × GlobalState)
    (s : GlobalState) : (modifyGet f : EffectM α) s = .value (f s) := rfl

def serialEntryEnv (E : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) : ⟪serialKernel.Γ⟫ :=
  E[%0 := .value 1#32, %1 := .value 0#8, %2 := .value 256#64, %3 := .value 32#64,
    %4 := .value 0#64, %5 := .value 6#64, %6 := .value 63#64, %7 := .value 59#64,
    %8 := .value 8#64, %9 := .value 31#64, %10 := .value 1#64, %11 := .value 15#64,
    %12 := .value 224#8, %13 := .value 5#64, %14 := .value 251#64,
    %15 := .value 56#64, %16 := .value 255#64, %17 := .value 127#64,
    %18 := .value 248#64, %19 := .value (-1 : BitVec 64), %20 := .value 40#64,
    %21 := .value g.address0, %22 := .value 80#64, %23 := .value 120#64,
    %24 := .value 16#8, %25 := .value g.address1, %26 := .value 255#8,
    %27 := .value 64#64, %28 := .value g.address2, %29 := .value g.address3,
    %30 := .value (serialStackPtr s 0), %31 := .value (serialStackPtr s 1),
    %32 := .value (serialStackPtr s 2), %33 := .value (serialStackPtr s 3),
    %34 := .value (serialStackPtr s 4), %35 := .value (serialStackPtr s 5),
    %36 := .value (serialStackPtr s 6), %37 := .value (serialStackPtr s 7),
    %38 := .value (serialStackPtr s 8), %39 := .value (serialStackPtr s 9),
    %40 := .value (serialStackPtr s 10), %41 := .value (serialStackPtr s 11),
    %42 := .value ((serialStackPtr s 1).add 32#64), %43 := .value 0#64, %44 := .value 0#64]

/-- The complete imported entry block: constants, twelve allocations, zero
NAF output, padded scalar copy, and initial zero cursor/carry. -/
theorem serial_entry_block (E : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) (input : Pointer) (scalar : BitVec 256) (hwf : s.WF)
    (hinput : Buffer s.mem input 32) (hscalar : s.mem.readAt input 256 = scalar)
    (harg : E.args 1 = .value input) :
    (serialKernel.bb0 g).run serialKernel.blockParams E s =
      .value ((serialEntryEnv E g s, .inr 1),
        nafInitialized (serialStack s 12) (serialStackPtr s 11) (serialStackPtr s 1) scalar) := by
  have hdigits : Buffer (serialStack s 12).mem (serialStackPtr s 11) 256 :=
    serialStack_buffer hwf 11 12 (by decide) (by decide)
  have hscratch : Buffer (serialStack s 12).mem (serialStackPtr s 1) 40 :=
    serialStack_buffer hwf 1 12 (by decide) (by decide)
  have hzero (env : ⟪serialKernel.Γ⟫) := NAF.Memory.zero_digits hdigits env
  have hscale : Operation.gepInboundsIndex 1 (.value 32#64) = .value (32 : Int) := by
    decide +kernel
  have hgep := (hscratch.storeAt (serialStackPtr s 11) (0 : BitVec 2048)).gep 32 (by decide)
  simp only [Int.cast_ofNat_Int] at hgep
  have hfits := (hscratch.storeAt (serialStackPtr s 11) (0 : BitVec 2048)).fits_at 32 8 (by decide)
  have hstore (env : ⟪serialKernel.Γ⟫) :
      Operation.store (τ := .bv 64) (.value ((serialStackPtr s 1).add 32#64)) (.value 0#64) env
        (nafCleared (serialStack s 12) (serialStackPtr s 11)) =
          .value (env, nafPadded (serialStack s 12) (serialStackPtr s 11) (serialStackPtr s 1)) :=
    run_store (env := env) hfits rfl
  have hread : (serialStack s 12).mem.readAt input 256 = scalar := by
    rw [serialStack_read_existing hwf hinput, hscalar]
  have hcopy (env : ⟪serialKernel.Γ⟫) := nafSetup_copy env (serialStack s 12)
    (serialStackPtr s 11) (serialStackPtr s 1) input scalar hscratch
    (serialStack_existing hwf hinput 12) (serialStack_separate_caller hwf hinput 11)
    (serialStack_separate_caller hwf hinput 1) hread
  simp [serialStack, serialStackSize, serialStackPtr, nafCleared] at hzero hgep hstore hcopy
  simp [BasicBlock.run, serialKernel.bb0, serialEntryEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    modifyGet_run, harg, hzero, hscale, hgep, hstore, hcopy,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    serialStack, serialStackSize, serialStackPtr, nafCleared, Ty.wrap]

end Agave.Ed25519.DoubleBase.RIR
