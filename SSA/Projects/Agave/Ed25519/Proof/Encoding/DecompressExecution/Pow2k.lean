import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2kBody

namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow2k
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

set_option maxHeartbeats 1600000
set_option maxRecDepth 30000

abbrev storeEnv (E : ⟪program.Γ⟫) (a : Words) : ⟪program.Γ⟫ :=
  E[%94 := .value (a 0), %93 := .value (a 1),
    %80 := .value (a 2), %85 := .value (a 3), %89 := .value (a 4)]

theorem storeEnv_args (E : ⟪program.Γ⟫) (a : Words) :
    (storeEnv E a).args = E.args := by
  simp only [storeEnv, Env.write_args]

/-- All final field stores of the original pow2k helper. -/
theorem store_run (E : ⟪program.Γ⟫) (r : Pointer) (a : Words)
    (s : GlobalState) (hr : SmallRange s.mem r 40)
    (harg : E.read (%arg0) = .value r) :
    program.runFrom (storeEnv E a) 2 s =
      .value (.nil, {s with mem := storeLimbs s.mem r a}) := by
  change E.args 0 = .value r at harg
  have hs1 := hr.storeAt r (a 0)
  have hs2 := hs1.storeAt (r.add 8#64) (a 1)
  have hs3 := hs2.storeAt (r.add 16#64) (a 2)
  have hs4 := hs3.storeAt (r.add 24#64) (a 3)
  have hf0 := hr.fits_add (k := 0) (count := 8) (by decide)
  have hf8 := hs1.fits_add (k := 8) (count := 8) (by decide)
  have hf16 := hs2.fits_add (k := 16) (count := 8) (by decide)
  have hf24 := hs3.fits_add (k := 24) (count := 8) (by decide)
  have hf32 := hs4.fits_add (k := 32) (count := 8) (by decide)
  have hg8 := hs1.gep (k := 8) (by decide)
  have hg16 := hs2.gep (k := 16) (by decide)
  have hg24 := hs3.gep (k := 24) (by decide)
  have hg32 := hs4.gep (k := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  norm_num only [Nat.cast_ofNat] at hg8 hg16 hg24 hg32
  rw [Func.runFrom_eq, BasicBlock.run_eq]
  rw [show program.blocks 2 = program.bb2 from rfl]
  dsimp only [program.bb2, BasicBlock.runBodyFrom, List.drop]
  simp only [List.foldlM_cons, List.foldlM_nil, EffectM.bind_eq, EffectM.pure_eq]
  simp [storeEnv, Instr.run, Operation.store, Ty.flatten, mlir_env, mlir_effect,
    GepIndex.inboundsOffset, harg, hf0, hf8, hf16, hf24, hf32,
    hg8, hg16, hg24, hg32, throwUBIf, storeLimbs,
    Exit.run, Regs.read_nil, Func.continue]

private theorem decrement (n : Nat) :
    BitVec.ofNat 32 (n + 1) + 4294967295#32 = BitVec.ofNat 32 n := by
  rw [BitVec.ofNat_add]
  have hm : 4294967295#32 = -1#32 := by decide
  rw [hm, BitVec.add_assoc, show 1#32 + -1#32 = 0#32 from rfl, BitVec.add_zero]

attribute [-simp] BitVec.shiftLeft_add_distrib in
private theorem loop_one (E : ⟪program.Γ⟫) (r : Pointer) (a : Words)
    (s : GlobalState) (hr : SmallRange s.mem r 40)
    (harg : E.args 0 = .value r) :
    program.runFrom (loopEnv E a 1#32) 1 s =
      .value (.nil, {s with mem := storeLimbs s.mem r (iterateSquare 1 a)}) := by
  generalize hE : loopEnv E a 1#32 = E'
  symm at hE
  have hEargs : E'.args = E.args :=
    (congrArg Env.args hE).trans (loopEnv_args E a _)
  dsimp only [loopEnv] at hE
  extract_state
  block_init
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  finish_block
  step_loop using (store_run (a := SerialPoint.squareMachine a))
  all_goals rfl

private theorem loop_backedge (E : ⟪program.Γ⟫) (a : Words) (count : BitVec 32)
    (s : GlobalState)
    (hc : E[%4 := .value 19#64, %5 := .value 1#128, %6 := .value 51#128,
      %7 := .value 18446744073709551615#128, %8 := .value 2251799813685247#64,
      %9 := .value 51#64, %10 := .value 4294967295#32, %11 := .value 0#32] = E)
    (h80 : E.read (%80) = .value (a 2))
    (h85 : E.read (%85) = .value (a 3))
    (h89 : E.read (%89) = .value (a 4))
    (h93 : E.read (%93) = .value (a 1))
    (h94 : E.read (%94) = .value (a 0))
    (h95 : E.read (%95) = .value count)
    (h96 : E.read (%96) = .value 0#1) :
    Exit.run program.blockParams E program.bb1.exit s =
      .value (((loopEnv E a count), .inr 1), s) := by
  have heq : loopEnv E a count = E[%21 := .value (a 4), %22 := .value (a 3),
      %23 := .value (a 2), %24 := .value (a 1), %25 := .value (a 0), %26 := .value count] := by
    change E[%4 := .value 19#64, %5 := .value 1#128, %6 := .value 51#128,
      %7 := .value 18446744073709551615#128, %8 := .value 2251799813685247#64,
      %9 := .value 51#64, %10 := .value 4294967295#32, %11 := .value 0#32][
        %21 := .value (a 4), %22 := .value (a 3), %23 := .value (a 2),
        %24 := .value (a 1), %25 := .value (a 0), %26 := .value count] = _
    rw [hc]
  rw [heq]
  simp [program.bb1, Exit.run, h96, h80, h85, h89, h93, h94, h95,
    Jump.run, Regs.read_cons, Regs.read_nil, reduceWriteManyDsts,
    Env.writeMany_cons, Env.writeMany_nil, EffectM.pure_eq]

private theorem body_next {f : Func} {E E' E'' : ⟪f.Γ⟫} {i j : Fin f.n}
    {s : GlobalState}
    (hb : (f.blocks i).runBodyFrom E 0 s = .value (E', s))
    (he : Exit.run f.blockParams E' (f.blocks i).exit s = .value ((E'', .inr j), s)) :
    f.runFrom E i s = f.runFrom E'' j s := by
  rw [Func.runFrom_eq, BasicBlock.run_eq]
  simp only [EffectM.bind_eq, hb, PoisonOr.value_bind, he]
  exact Func.continue_next

private theorem loop_continue (n : Nat) (hn : n + 1 + 1 < 2 ^ 32)
    (E : ⟪program.Γ⟫) (a : Words) (s : GlobalState)
    (out : PoisonOr (Vals program.tRets × GlobalState))
    (next : ∀ E', E'.args = E.args →
      program.runFrom (loopEnv E' (SerialPoint.squareMachine a) (BitVec.ofNat 32 (n + 1))) 1 s = out) :
    program.runFrom (loopEnv E a (BitVec.ofNat 32 (n + 1 + 1))) 1 s = out := by
  have hn' : n + 1 < 2 ^ 32 := by omega
  have hne : BitVec.ofNat 32 (n + 1) ≠ 0#32 := by
    intro he
    have ht := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn'] at ht
    omega
  have hcmp : (BitVec.ofNat 32 (n + 1) == 0#32) = false := beq_false_of_ne hne
  have h95 : (bodyEnv (loopEnv E a (BitVec.ofNat 32 (n + 1 + 1)))).read (%95) =
      .value (BitVec.ofNat 32 (n + 1)) := by
    rw [bodyEnv_read95, decrement]
  have h96 : (bodyEnv (loopEnv E a (BitVec.ofNat 32 (n + 1 + 1)))).read (%96) =
      .value 0#1 := by
    rw [bodyEnv_read96, decrement, hcmp]
    rfl
  apply Eq.trans (body_next (f := program) (i := 1) (j := 1) (body_run _ s)
    (loop_backedge _ (SerialPoint.squareMachine a) _ s
      (bodyEnv_constants E a _) (bodyEnv_read80 E a _) (bodyEnv_read85 E a _)
      (bodyEnv_read89 E a _) (bodyEnv_read93 E a _) (bodyEnv_read94 E a _) h95 h96))
  exact next _ ((bodyEnv_args _).trans (loopEnv_args E a _))

/-- Execution of the original loop for a nonzero, nonwrapping iteration count.
The only stores happen after the final square, so input/output aliasing is safe. -/
theorem loop_run (n : Nat) (hn : n + 1 < 2 ^ 32)
    (E : ⟪program.Γ⟫) (r : Pointer) (a : Words)
    (s : GlobalState) (hr : SmallRange s.mem r 40)
    (harg : E.read (%arg0) = .value r) :
    program.runFrom (loopEnv E a (BitVec.ofNat 32 (n + 1))) 1 s =
      .value (.nil, {s with mem := storeLimbs s.mem r (iterateSquare (n + 1) a)}) := by
  change E.args 0 = .value r at harg
  induction n generalizing E a with
  | zero => exact loop_one E r a s hr harg
  | succ n ih =>
    apply loop_continue n hn E a s
    intro E' hargs
    exact ih (by omega) E' (SerialPoint.squareMachine a) (by simpa only [hargs] using harg)

/-- Actual imported pow2k call, including five input loads, the entire loop,
and the five output stores. Only the nonzero machine iteration count is needed
in addition to live input/output ranges and state freshness. -/
theorem program_run (count : Nat) (hpos : 0 < count) (hcount : count < 2 ^ 32)
    (r input : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem input 40) :
    program.run (program.args (.value r) (.value input) (.value (BitVec.ofNat 32 count))) s =
      .value (.nil, {s with mem := storeLimbs s.mem r (iterateSquare count (readLimbs s input))}) := by
  cases count with
  | zero => omega
  | succ n =>
    have hr0 := hr.fits_add (k := 0) (count := 8) (by decide)
    have hr8 := hr.fits_add (k := 8) (count := 8) (by decide)
    have hr16 := hr.fits_add (k := 16) (count := 8) (by decide)
    have hr24 := hr.fits_add (k := 24) (count := 8) (by decide)
    have hr32 := hr.fits_add (k := 32) (count := 8) (by decide)
    have ha0 := ha.fits_add (k := 0) (count := 8) (by decide)
    have ha8 := ha.fits_add (k := 8) (count := 8) (by decide)
    have ha16 := ha.fits_add (k := 16) (count := 8) (by decide)
    have ha24 := ha.fits_add (k := 24) (count := 8) (by decide)
    have ha32 := ha.fits_add (k := 32) (count := 8) (by decide)
    simp only [Pointer.add_zero] at hr0 ha0
    rw [Func.run_runFrom_eq]
    extract_state
    extract_env
    block_init
    step_pure
    step_pure
    step_pure
    step_pure
    step_pure
    step_pure
    step_pure
    step_pure
    step_pure
    step_pure
    step_pure
    step_pure
    step_load
    have hgep := ha.gep (k := 8) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    try simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset]
    clear hgep
    step_load
    have hgep := ha.gep (k := 16) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    try simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset]
    clear hgep
    step_load
    have hgep := ha.gep (k := 24) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    try simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset]
    clear hgep
    step_load
    have hgep := ha.gep (k := 32) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    try simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset]
    clear hgep
    step_load
    finish_block
    step_loop using (loop_run n hcount (a := readLimbs S₀ input))
    all_goals try simp [readLimbs, Pointer.add, mlir_env]

/-- Calls have the same stores as the run: the loop creates no allocations. -/
theorem program_call (count : Nat) (hpos : 0 < count) (hcount : count < 2 ^ 32)
    (r input : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem input 40) :
    program.call (program.args (.value r) (.value input) (.value (BitVec.ofNat 32 count))) s =
      .value (.nil, {s with mem := storeLimbs s.mem r (iterateSquare count (readLimbs s input))}) := by
  refine Func.call_eq_of_run_eq (program_run count hpos hcount r input s hwf hr ha) ?_ rfl
  simpa only [storeLimbs, GlobalState.WF_storeAt] using hwf

/-- Field result of the actual imported helper, with its caller invariant. -/
theorem program_call_field (count : Nat) (hpos : 0 < count) (hcount : count < 2 ^ 32)
    (r input : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem input 40)
    (hlimbs : SerialPoint.Tight (unsigned (readLimbs s input))) :
    ∃ output : Words,
      program.call (program.args (.value r) (.value input) (.value (BitVec.ofNat 32 count))) s =
        .value (.nil, {s with mem := storeLimbs s.mem r output}) ∧
      wordValue output = wordValue (readLimbs s input) ^ (2 ^ count) ∧
      SerialPoint.Tight (unsigned output) := by
  refine ⟨iterateSquare count (readLimbs s input),
    program_call count hpos hcount r input s hwf hr ha, ?_, ?_⟩
  · exact iterateSquare_value count _ hlimbs
  · exact iterateSquare_tight count _ hlimbs

end Agave.Ed25519.Encoding.Decompress.Execution.Pow2k
