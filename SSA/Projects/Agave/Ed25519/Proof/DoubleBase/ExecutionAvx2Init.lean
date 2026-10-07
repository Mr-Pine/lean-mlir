import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Control
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialInit

/-! The real second-emitter setup. The state transformers are shared with the
serial setup because their memset/padding/copy memory behavior is identical. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

/-- Initialization establishes the exact five-word scalar, using only the
fresh object's zero contents and separation from the digit output. -/
theorem nafSetup_scalar_buffer (s : GlobalState) (digits scratch : Pointer)
    (scalar : BitVec 256) (hscratch : Buffer s.mem scratch 40)
    (hseparate : digits.id ≠ scratch.id) (hzero : s.mem.readAt scratch 320 = 0) :
    (nafInitialized s digits scratch scalar).mem.readAt scratch 320 =
      NAF.WordWindow.scalarBuffer scalar := by
  have hclear : (nafCleared s digits).mem.readAt scratch 320 = 0 := by
    unfold nafCleared
    rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hseparate), hzero]
  have hb : Buffer (nafCleared s digits).mem scratch 40 := hscratch.storeAt _ _
  have hpad : (nafPadded s digits scratch).mem.readAt scratch 320 = 0 := by
    have hp := MemoryState.readAt_add_storeAt (off := 32#64) hb.fits
      (hb.offset_noOverflow 32 (by decide)) (by decide : (32#64).toNat * 8 + 64 ≤ 320) (0#64)
    change ((nafCleared s digits).mem.storeAt (scratch.add 32#64) (0#64)).readAt scratch 320 = 0
    rw [hp, hclear]
    simp [LeanMLIR.RIR.Memory.spliceBits]
  exact NAF.Memory.copy_scalar_words (hb.storeAt _ _) hpad scalar

theorem nafSetup_wf (hwf : s.WF) : (nafInitialized s digits scratch scalar).WF :=
  hwf.storeAt.storeAt.storeAt

def setupInput8 (E : ⟪avx2Kernel.Γ⟫) (digits scratch : Pointer) : ⟪avx2Kernel.Γ⟫ :=
  E[%1 := .value 0#8, %2 := .value 256#64, %3 := .value 32#64,
    %4 := .value 0#64, %257 := .value scratch, %265 := .value digits]

def setupResult8 (E : ⟪avx2Kernel.Γ⟫) (digits scratch : Pointer) : ⟪avx2Kernel.Γ⟫ :=
  (setupInput8 E digits scratch)[%298 := .value (scratch.add 32#64),
    %299 := .value 0#64, %300 := .value 0#64]

/-- The real width-eight setup clears all 256 digit bytes, pads the fifth word,
and copies the scalar before entering the original carry block. -/
theorem setup8_block (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (digits scratch input : Pointer) (scalar : BitVec 256)
    (hdigits : Buffer s.mem digits 256) (hscratch : Buffer s.mem scratch 40)
    (hinput : Buffer s.mem input 32) (hdi : digits.id ≠ input.id)
    (hsi : scratch.id ≠ input.id) (hscalar : s.mem.readAt input 256 = scalar)
    (harg : E.args 3 = .value input) :
    avx2Kernel.bb7.run avx2Kernel.blockParams (setupInput8 E digits scratch) s =
      .value ((setupResult8 E digits scratch, .inr 8), nafInitialized s digits scratch scalar) := by
  have hzero (env : ⟪avx2Kernel.Γ⟫) :
      Operation.memset (.value digits) (.value 0#8) (.value 256#64) env s =
        .value (env, nafCleared s digits) := NAF.Memory.zero_digits hdigits env
  have hscale : Operation.gepInboundsIndex 1 (.value 32#64) = .value (32 : Int) := by
    decide +kernel
  have hgep := (hscratch.storeAt digits (0 : BitVec 2048)).gep 32 (by decide)
  simp only [Int.cast_ofNat_Int] at hgep
  change Operation.gepInboundsLive (nafCleared s digits).mem (.value scratch)
    [.value (32 : Int)] = .value (scratch.add 32#64) at hgep
  have hfits := (hscratch.storeAt digits (0 : BitVec 2048)).fits_at 32 8 (by decide)
  have hstore (env : ⟪avx2Kernel.Γ⟫) :
      Operation.store (τ := .bv 64) (.value (scratch.add 32#64)) (.value 0#64) env
        (nafCleared s digits) = .value (env, nafPadded s digits scratch) :=
    run_store (env := env) (s := nafCleared s digits) hfits rfl
  have hcopy (env : ⟪avx2Kernel.Γ⟫) := nafSetup_copy env s digits scratch input scalar
    hscratch hinput hdi hsi hscalar
  simp [BasicBlock.run, avx2Kernel.bb7, setupInput8, setupResult8,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    harg, hzero, hscale, hgep, hstore, hcopy,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem setup8_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (digits scratch input : Pointer) (scalar : BitVec 256)
    (hdigits : Buffer s.mem digits 256) (hscratch : Buffer s.mem scratch 40)
    (hinput : Buffer s.mem input 32) (hdi : digits.id ≠ input.id)
    (hsi : scratch.id ≠ input.id) (hscalar : s.mem.readAt input 256 = scalar)
    (harg : E.args 3 = .value input) :
    (avx2Kernel p g).runFrom (setupInput8 E digits scratch) 7 s =
      (avx2Kernel p g).runFrom
        ((setupResult8 E digits scratch)[%301 := .value 0#64]) 9
        (nafInitialized s digits scratch scalar) := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 7 = avx2Kernel.bb7 from rfl,
    setup8_block E s digits scratch input scalar hdigits hscratch hinput hdi hsi hscalar harg]
  change (avx2Kernel p g).runFrom (setupResult8 E digits scratch) 8 _ = _
  rw [carry8_run]
  simp [setupResult8, mlir_env]

end Agave.Ed25519.DoubleBase.ExecutionAvx2
