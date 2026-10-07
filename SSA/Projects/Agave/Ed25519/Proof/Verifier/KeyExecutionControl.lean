import SSA.Projects.Agave.Ed25519.Proof.Verifier.WrapperExecution

/-! Exact constructor entry, malformed-input branch, and Result-tag return.
The decoder is the only external call in this extracted function. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Agave.Ed25519.Verifier.Execution.Key
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

def args (out bytes : Pointer) : Vals [.ptr, .ptr] :=
  .cons (.value out) (.cons (.value bytes) .nil)

def optionSlot (s : GlobalState) : Pointer := s.allocaPtr

def entryEnv (E : Env program.Γ) (s : GlobalState) (valid : Bool) : Env program.Γ :=
  E[%0 := .value 1, %1 := .value 1, %2 := .value 1, %3 := .value 8,
    %4 := .value 16, %5 := .value 32, %6 := .value 48, %7 := .value 80,
    %8 := .value 40, %9 := .value 88, %10 := .value 120, %11 := .value 128,
    %12 := .value 136, %13 := .value 152,
    %14 := Ty.wrap #v[36028797018963664#64, 36028797018963952#64],
    %15 := Ty.wrap (Vector.replicate 2 (36028797018963952#64)),
    %16 := Ty.wrap (Vector.replicate 2 (51#64)), %17 := .value 0,
    %18 := .value 2251799813685247,
    %19 := Ty.wrap (Vector.replicate 2 (2251799813685247#64)),
    %20 := .value 64, %21 := .value 51, %22 := .value 19,
    %23 := .value 160, %24 := .value 168, %25 := .value 184, %26 := .value 0,
    %27 := .value (optionSlot s),
    %28 := .value (if valid then 1 else 0), %29 := .value (BitVec.ofBool valid)]

@[simp] theorem block_0 (p : Primitives) : (program p).blocks 0 = program.bb0 p := rfl
@[simp] theorem block_1 (p : Primitives) : (program p).blocks 1 = program.bb1 := rfl
@[simp] theorem block_2 (p : Primitives) : (program p).blocks 2 = program.bb2 := rfl
@[simp] theorem block_3 (p : Primitives) : (program p).blocks 3 = program.bb3 := rfl

private theorem modifyGet_run (f : GlobalState → α × GlobalState) (s : GlobalState) :
    (modifyGet f : EffectM α) s = .value (f s) := rfl

/-- The constructor dispatches on the actual 64-bit decoder Option tag. -/
theorem entry_block (p : Primitives) (E : Env program.Γ)
    (initial decoded : GlobalState) (bytes : Pointer) (valid : Bool)
    (hbytes : E.read (%arg1) = .value bytes)
    (hcall : p.decompress (args (optionSlot initial) bytes) (initial.alloca 168) =
      .value (.nil, decoded))
    (hfit : Fits decoded.mem (optionSlot initial) 64)
    (htag : decoded.mem.readAt (optionSlot initial) 64 = if valid then 1 else 0) :
    (program.bb0 p).run program.blockParams E initial =
      .value ((entryEnv E initial valid, .inr (if valid then 1 else 2)), decoded) := by
  change E.args 1 = .value bytes at hbytes
  dsimp only [args, optionSlot] at hcall hfit htag
  cases valid <;>
    simp [BasicBlock.run, program.bb0, entryEnv, optionSlot, args,
      List.foldlM_cons, List.foldlM_nil, Instr.run,
      EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
      run_alloca, modifyGet_run, Operation.load, Operation.store, throwUBIf, UnOp.compute, mlir_operation,
      hbytes, hcall, hfit, htag, Exit.run, Jump.run, program.blockParams] <;> rfl

/-- Write the caller-owned result discriminant, then return. -/
theorem return_block (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (out : Pointer) (tag : BitVec 8)
    (hout : E.read (%arg0) = .value out) (htag : E.read (%86) = .value tag)
    (hfit : Fits s.mem out 8) :
    (program p).runFrom E 3 s =
      .value (.nil, { s with mem := s.mem.storeAt out tag }) := by
  change E.args 0 = .value out at hout
  have hb : program.bb3.run program.blockParams E s =
      .value ((E, .inl .nil), { s with mem := s.mem.storeAt out tag }) := by
    simp [BasicBlock.run, program.bb3, List.foldlM_cons, List.foldlM_nil,
      Instr.run, EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
      run_alloca, modifyGet_run, Operation.load, Operation.store, throwUBIf, UnOp.compute, mlir_operation,
      hout, htag, hfit, Exit.run]
  rw [Func.runFrom_eq, block_3, hb]
  rfl

def rejectedState (s : GlobalState) (out : Pointer) : GlobalState :=
  { s with mem := (s.mem.storeAt (out.add 1) (1#8)).storeAt out (1#8) }

/-- A malformed compressed key stores the error payload byte and error tag.
It does not access any uninitialized point payload. -/
theorem reject_block (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (out : Pointer) (hout : E.read (%arg0) = .value out)
    (hone : E.read (%1) = .value (1#64)) (herror : E.read (%2) = .value (1#8))
    (hrange : SmallRange s.mem out 200) :
    (program p).runFrom E 2 s = .value (.nil, rejectedState s out) := by
  change E.args 0 = .value out at hout
  have hgep := hrange.gep (k := 1) (by decide)
  have hfit := hrange.fits_add (k := 1) (count := 1) (by decide)
  norm_num only [Nat.cast_ofNat, Nat.reduceMul] at hgep hfit
  have hb : program.bb2.run program.blockParams E s =
      .value (((E[%85 := .value (out.add 1)])[%86 := .value (1#8)], .inr 3),
        { s with mem := s.mem.storeAt (out.add 1) (1#8) }) := by
    simp [BasicBlock.run, program.bb2, List.foldlM_cons, List.foldlM_nil,
      Instr.run, EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
      run_alloca, modifyGet_run, Operation.load, Operation.store, throwUBIf, UnOp.compute, mlir_operation,
      hout, hone, herror, hgep, hfit, GepIndex.inboundsOffset,
      Exit.run, Jump.run, program.blockParams, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil]
    rfl
  rw [Func.runFrom_eq, block_2, hb]
  change (program p).runFrom _ 3 _ = _
  apply return_block
  · simpa [mlir_env] using hout
  · simp [mlir_env]
  · exact (Fits.mono (by decide) hrange.fits).storeAt

theorem run_rejected (p : Primitives) (initial decoded : GlobalState)
    (out bytes : Pointer)
    (hcall : p.decompress (args (optionSlot initial) bytes) (initial.alloca 168) =
      .value (.nil, decoded))
    (hfit : Fits decoded.mem (optionSlot initial) 64)
    (htag : decoded.mem.readAt (optionSlot initial) 64 = 0)
    (hrange : SmallRange decoded.mem out 200) :
    (program p).run (args out bytes) initial = .value (.nil, rejectedState decoded out) := by
  rw [Func.run_runFrom_eq, Func.runFrom_eq]
  change ((program.bb0 p).run program.blockParams (Env.init (args out bytes).get) initial >>= _) = _
  rw [entry_block p _ initial decoded bytes false (by simp [args, Env.init, mlir_env, Vals.get])
    hcall hfit (by simpa using htag)]
  change (program p).runFrom _ 2 decoded = _
  apply reject_block
  · simp [entryEnv, args, Env.init, mlir_env, Vals.get]
  · simp [entryEnv, mlir_env]
  · simp [entryEnv, mlir_env]
  · exact hrange

end Agave.Ed25519.Verifier.Execution.Key
