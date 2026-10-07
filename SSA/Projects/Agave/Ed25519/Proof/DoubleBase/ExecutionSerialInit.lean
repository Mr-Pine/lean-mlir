import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialBlocks
import SSA.Projects.Agave.Ed25519.Proof.NAF.Memory
import SSA.Projects.RIR.Run.BasicBlock

/-! Shared scalar-buffer initialization and the actual serial width-eight setup
block. Scratch separation is supplied by the preceding stack allocations. -/
namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

def nafCleared (s : GlobalState) (digits : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt digits (0 : BitVec 2048)}

def nafPadded (s : GlobalState) (digits scratch : Pointer) : GlobalState :=
  {nafCleared s digits with
    mem := (nafCleared s digits).mem.storeAt (scratch.add 32#64) (0#64)}

def nafInitialized (s : GlobalState) (digits scratch : Pointer) (scalar : BitVec 256) :
    GlobalState :=
  {nafPadded s digits scratch with mem := (nafPadded s digits scratch).mem.storeAt scratch scalar}

theorem nafSetup_buffer (h : Buffer s.mem p bytes) :
    Buffer (nafInitialized s digits scratch scalar).mem p bytes :=
  ((h.storeAt _ _).storeAt _ _).storeAt _ _

theorem nafSetup_copy (E : ⟪Γ⟫) (s : GlobalState) (digits scratch input : Pointer)
    (scalar : BitVec 256) (hscratch : Buffer s.mem scratch 40)
    (hinput : Buffer s.mem input 32) (hdi : digits.id ≠ input.id)
    (hsi : scratch.id ≠ input.id) (hscalar : s.mem.readAt input 256 = scalar) :
    Operation.memcpy (.value scratch) (.value input) (.value 32#64) E
      (nafPadded s digits scratch) =
        .value (E, nafInitialized s digits scratch scalar) := by
  have hdst := ((hscratch.storeAt digits (0 : BitVec 2048)).storeAt
    (scratch.add 32#64) (0#64)).fits_at 0 32 (by decide)
  simp only [Pointer.add_zero] at hdst
  have hsrc := ((hinput.storeAt digits (0 : BitVec 2048)).storeAt
    (scratch.add 32#64) (0#64)).fits
  have hread : (nafPadded s digits scratch).mem.readAt input 256 = scalar := by
    unfold nafPadded nafCleared
    rw [MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hsi)),
      MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hdi), hscalar]
  have hcopy := run_memcpy (env := E) (s := nafPadded s digits scratch)
    (show (32#64).toNat = 32 from rfl) (Range.disjoint_of_id_ne hsi) hdst hsrc
  rw [hread] at hcopy
  exact hcopy

theorem nafSetup_digits_zero (s : GlobalState) (digits scratch : Pointer)
    (scalar : BitVec 256) (hdigits : Buffer s.mem digits 256)
    (hsd : scratch.id ≠ digits.id) :
    (nafInitialized s digits scratch scalar).mem.readAt digits 2048 = 0 := by
  unfold nafInitialized nafPadded nafCleared
  rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hsd),
    MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hsd)),
    MemoryState.readAt_storeAt_self hdigits.fits]

/-- The two stores and memcpy preserve every separately allocated caller object. -/
theorem nafSetup_read_other (s : GlobalState) (digits scratch q : Pointer)
    (scalar : BitVec 256) (bits : Nat) (hdq : digits.id ≠ q.id)
    (hsq : scratch.id ≠ q.id) :
    (nafInitialized s digits scratch scalar).mem.readAt q bits = s.mem.readAt q bits := by
  unfold nafInitialized nafPadded nafCleared
  rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hsq),
    MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hsq)),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hdq)]

def setupInput8 (E : ⟪serialKernel.Γ⟫) (digits scratch : Pointer) : ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8, %2 := .value 256#64, %3 := .value 32#64,
    %4 := .value 0#64, %30 := .value scratch, %40 := .value digits]

def setupResult8 (E : ⟪serialKernel.Γ⟫) (digits scratch : Pointer) : ⟪serialKernel.Γ⟫ :=
  (setupInput8 E digits scratch)[%73 := .value (scratch.add 32#64),
    %74 := .value 0#64, %75 := .value 0#64]

/-- The real width-eight setup clears all 256 digit bytes, pads the fifth word,
and copies the scalar before entering the original carry block. -/
theorem serial8_setup_block (E : ⟪serialKernel.Γ⟫) (s : GlobalState)
    (digits scratch input : Pointer) (scalar : BitVec 256)
    (hdigits : Buffer s.mem digits 256) (hscratch : Buffer s.mem scratch 40)
    (hinput : Buffer s.mem input 32) (hdi : digits.id ≠ input.id)
    (hsi : scratch.id ≠ input.id) (hscalar : s.mem.readAt input 256 = scalar)
    (harg : E.args 3 = .value input) :
    serialKernel.bb7.run serialKernel.blockParams (setupInput8 E digits scratch) s =
      .value ((setupResult8 E digits scratch, .inr 8), nafInitialized s digits scratch scalar) := by
  have hzero (env : ⟪serialKernel.Γ⟫) :
      Operation.memset (.value digits) (.value 0#8) (.value 256#64) env s =
        .value (env, nafCleared s digits) := NAF.Memory.zero_digits hdigits env
  have hscale : Operation.gepInboundsIndex 1 (.value 32#64) = .value (32 : Int) := by
    decide +kernel
  have hgep := (hscratch.storeAt digits (0 : BitVec 2048)).gep 32 (by decide)
  simp only [Int.cast_ofNat_Int] at hgep
  change Operation.gepInboundsLive (nafCleared s digits).mem (.value scratch)
    [.value (32 : Int)] = .value (scratch.add 32#64) at hgep
  have hfits := (hscratch.storeAt digits (0 : BitVec 2048)).fits_at 32 8 (by decide)
  have hstore (env : ⟪serialKernel.Γ⟫) :
      Operation.store (τ := .bv 64) (.value (scratch.add 32#64)) (.value 0#64) env
        (nafCleared s digits) = .value (env, nafPadded s digits scratch) :=
    run_store (env := env) (s := nafCleared s digits) hfits rfl
  have hcopy (env : ⟪serialKernel.Γ⟫) := nafSetup_copy env s digits scratch input scalar
    hscratch hinput hdi hsi hscalar
  simp [BasicBlock.run, serialKernel.bb7, setupInput8, setupResult8,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    harg, hzero, hscale, hgep, hstore, hcopy,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

end Agave.Ed25519.DoubleBase.RIR
