import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendCounter
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory
import SSA.Projects.RIR.Semantics.Func

/-! Exact basic-block execution for the imported C streaming append. The only
opaque effect is the supplied compression call; copies and stores execute the
RIR memory semantics and all their range/non-overlap checks. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

@[simp] theorem params1 : program.blockParams 1 = .nil := rfl
@[simp] theorem params2 : program.blockParams 2 = .nil := rfl
@[simp] theorem params3 : program.blockParams 3 = .nil := rfl
@[simp] theorem params4 : program.blockParams 4 = .nil := rfl
@[simp] theorem params5 : program.blockParams 5 = .cons (%33) (.cons (%34) (.cons (%35) .nil)) := rfl
@[simp] theorem params6 : program.blockParams 6 = .cons (%36) (.cons (%37) .nil) := rfl
@[simp] theorem params7 : program.blockParams 7 = .nil := rfl
@[simp] theorem params8 : program.blockParams 8 = .nil := rfl
@[simp] theorem params9 : program.blockParams 9 = .nil := rfl
@[simp] theorem params10 : program.blockParams 10 = .nil := rfl

def entryEnv (E : Env program.Γ) (size : Word) : Env program.Γ :=
  E[%0 := .value 0#64, %1 := .value 128#64, %2 := .value 200#64,
    %3 := .value 208#64, %4 := .value 216#64, %5 := .value 3#64,
    %6 := .value 61#64, %7 := .value 1#64, %8 := .value 7#64,
    %9 := .value 127#64, %10 := .value (-128 : Word),
    %11 := .value (BitVec.ofBool (size == 0))]

theorem entry_block (E : Env program.Γ) (s : GlobalState) (size : Word)
    (hs : E.read (%arg2) = .value size) (hn : size ≠ 0#64) :
    program.bb0.run program.blockParams E s =
      .value ((entryEnv E size, .inr 1), s) := by
  change E.args 2 = .value size at hs
  simp [program.bb0, BasicBlock.run, entryEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
    Operation.icmp, BinOp.compute, hs, hn, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, ofBool_eq_one_iff]

structure CommonReady (E : Env program.Γ) (context : Pointer) : Prop where
  argContext : E.read (%arg0) = .value context
  zero : E.read (%0) = .value 0#64
  full : E.read (%1) = .value 128#64
  one : E.read (%7) = .value 1#64
  shift : E.read (%8) = .value 7#64
  low : E.read (%9) = .value 127#64
  high : E.read (%10) = .value (-128 : Word)
  chain : E.read (%12) = .value (context.add 128#64)
  count : E.read (%13) = .value (context.add 200#64)

def bufferEnv (E : Env program.Γ) (context : Pointer) (used size : Word) : Env program.Γ :=
  E[%27 := .value (128 - used), %28 := .value (BitVec.ofBool (size.ult (128 - used))),
    %29 := .value (context.add used)]

theorem buffer_body (E : Env program.Γ) (s : GlobalState) (context : Pointer)
    (used size : Word) (h : CommonReady E context)
    (hu : E.read (%14) = .value used) (hs : E.read (%arg2) = .value size)
    (hc : SmallRange s.mem context 224) (hub : used.toNat < 128) :
    List.foldlM Instr.run E program.bb2.body s =
      .value (bufferEnv E context used size, s) := by
  have hcontext : E.args 0 = .value context := h.argContext
  change E.args 2 = .value size at hs
  have hg := hc.gep (k := used.toNat) (by omega)
  have hi : used.toInt = (used.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hg
  have hsmall : used.toNat < 9223372036854775808 := by omega
  have h64 : used.toNat < 18446744073709551616 := used.isLt
  have hint : (used.toNat : Int) % 18446744073709551616 < 18446744073709551616 := Int.emod_lt_of_pos _ (by decide)
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bufferEnv, hcontext, hs, hu, h.full, Operation.sub, Operation.icmp,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hg, hi, hsmall, h64, hint, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

def copyMemory (m : MemoryState) (dst src : Pointer) (size : Word) : MemoryState :=
  m.storeAt dst (m.readAt src (8 * size.toNat))

theorem short_body (E : Env program.Γ) (s : GlobalState) (context data : Pointer)
    (used size : Word) (hp : E.read (%29) = .value (context.add used))
    (hd : E.read (%arg1) = .value data) (hu : E.read (%14) = .value used)
    (hs : E.read (%arg2) = .value size)
    (hc : SmallRange s.mem context 224) (hi : SmallRange s.mem data size.toNat)
    (hb : used.toNat + size.toNat ≤ 128) (hne : context.id ≠ data.id) :
    List.foldlM Instr.run E program.bb3.body s =
      .value (E[%30 := .value (used + size)],
        {s with mem := copyMemory s.mem (context.add used) data size}) := by
  change E.args 1 = .value data at hd
  change E.args 2 = .value size at hs
  have hf := hc.fits_add (k := used.toNat) (count := size.toNat) (by omega)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hf
  have hdis : (Range.of (context.add used) (8 * size.toNat)).Disjoint
      (Range.of data (8 * size.toNat)) := Or.inl hne
  simp [program.bb3, List.foldlM_cons, List.foldlM_nil, Instr.run,
    copyMemory, hp, hd, hu, hs, Operation.memcpy, Operation.add, hi.fits, hf, hdis,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

def countMemory (m : MemoryState) (context : Pointer) (used : Word) : MemoryState :=
  m.storeAt (context.add 200#64) used

theorem count_body (E : Env program.Γ) (s : GlobalState) (context : Pointer)
    (used : Word) (hp : E.read (%13) = .value (context.add 200#64))
    (hu : E.read (%33) = .value used) (hc : SmallRange s.mem context 224) :
    List.foldlM Instr.run E program.bb5.body s =
      .value (E, {s with mem := countMemory s.mem context used}) := by
  have hf := hc.fits_add (k := 200) (count := 8) (by decide)
  simp [program.bb5, List.foldlM_cons, List.foldlM_nil, Instr.run,
    countMemory, hp, hu, Operation.store, hf,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_body (E : Env program.Γ) (s : GlobalState) (size : Word)
    (hs : E.read (%37) = .value size) (hf : E.read (%1) = .value 128#64) :
    List.foldlM Instr.run E program.bb6.body s =
      .value (E[%38 := .value (BitVec.ofBool (size.ult 128))], s) := by
  simp [program.bb6, List.foldlM_cons, List.foldlM_nil, Instr.run,
    hs, hf, Operation.icmp, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect]

theorem remainder_body (E : Env program.Γ) (s : GlobalState) (size : Word)
    (hs : E.read (%37) = .value size) (hl : E.read (%9) = .value 127#64)
    (hz : E.read (%0) = .value 0#64) :
    List.foldlM Instr.run E program.bb8.body s =
      .value (E[%40 := .value (size &&& 127),
        %41 := .value (BitVec.ofBool (size &&& 127 == 0))], s) := by
  simp [program.bb8, List.foldlM_cons, List.foldlM_nil, Instr.run,
    hs, hl, hz, Operation.and, Operation.icmp, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect]

theorem return_block (E : Env program.Γ) (s : GlobalState) (context : PoisonOr Pointer)
    (hp : E.read (%arg0) = context) :
    program.bb10.run program.blockParams E s =
      .value ((E, .inl (.cons context .nil)), s) := by
  change E.args 0 = context at hp
  simp [program.bb10, BasicBlock.run, Exit.run, Regs.read_cons, Regs.read_nil,
    List.foldlM_nil, hp, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
