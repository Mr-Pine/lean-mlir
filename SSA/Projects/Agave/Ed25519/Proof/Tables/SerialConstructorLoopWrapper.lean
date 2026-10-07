import SSA.Projects.Agave.Ed25519.Proof.Tables.ConstructorMemory
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialCacheExecution
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialConversionCalls
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialScanComplete

/-! Exact loop wrappers around the separately checked 57-instruction cache
conversion. Only the cached-add helper call is a premise of `prefix_run`;
all four conversion multiplies are bound to their imported kernel. -/
namespace Agave.Ed25519.Tables.SerialConstructorLoopWrapper
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open DoubleBase.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem emptyVals_eq (v : Vals []) : v = .nil := by cases v; rfl

def prefixInput (E : ⟪SerialConstructor.kernel.Γ⟫)
    (completed extended doubled table : Pointer) (i : Fin 7) :
    ⟪SerialConstructor.kernel.Γ⟫ :=
  E[%26 := .value 1#64, %31 := .value completed, %32 := .value extended,
    %34 := .value doubled, %36 := .value table,
    %115 := .value (completed.add 120), %116 := .value (completed.add 40),
    %117 := .value (completed.add 80), %118 := .value (extended.add 40),
    %119 := .value (extended.add 80), %120 := .value (extended.add 120),
    %140 := .value (BitVec.ofNat 64 i.val)]

def prefixResult (E : ⟪SerialConstructor.kernel.Γ⟫)
    (completed extended doubled table : Pointer) (i : Fin 7) :
    ⟪SerialConstructor.kernel.Γ⟫ :=
  (prefixInput E completed extended doubled table i)[
    %141 := .value (BitVec.ofNat 64 (i.val + 1)),
    %142 := .value (table.add (BitVec.ofNat 64 (160 * i.val)))]

/-- The exact first ten original instructions retain the five helper calls. -/
theorem prefix_body (p : SerialConstructor.Primitives)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (completed extended doubled table : Pointer)
    (i : Fin 7) (s : GlobalState) (htable : SmallRange s.mem table 1280) :
    List.foldlM Instr.run (prefixInput E completed extended doubled table i)
      ((SerialConstructor.kernel.bb2 p).body.take 10) s =
      (do
        let _ ← p.call2 (.cons (.value completed) (.cons (.value doubled)
          (.cons (.value (table.add (BitVec.ofNat 64 (160 * i.val)))) .nil)))
        let _ ← completedCalls p.call0 extended completed
        pure (prefixResult E completed extended doubled table i)) s := by
  have hcursor := (ConstructorMemory.cursor_arithmetic i).1
  have hgep := (ConstructorMemory.record_geps htable i).1
  simp [SerialConstructor.kernel.bb2, prefixInput, prefixResult,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    GepIndex.inboundsOffset, hcursor, hgep, completedCalls, emptyVals_eq,
    Regs.read_cons, Env.writeMany_nil]

/-- The actual multiplication body discharges all four conversion calls. -/
theorem prefix_run (p : SerialConstructor.Primitives)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (completed extended doubled table : Pointer)
    (i : Fin 7) (s u : GlobalState) (htable : SmallRange s.mem table 1280)
    (hadd : p.call2 (.cons (.value completed) (.cons (.value doubled)
      (.cons (.value (table.add (BitVec.ofNat 64 (160 * i.val)))) .nil))) s = .value (.nil, u))
    (huwf : u.WF) (hextended : SmallRange u.mem extended 160)
    (hcompleted : SmallRange u.mem completed 160) :
    List.foldlM Instr.run (prefixInput E completed extended doubled table i)
      ((SerialConstructor.kernel.bb2 (SerialCacheExecution.primitives p)).body.take 10) s =
      .value (prefixResult E completed extended doubled table i,
        completedState u extended completed) := by
  rw [prefix_body _ E completed extended doubled table i s htable]
  simp only [SerialCacheExecution.primitives, EffectM.bind_eq, hadd,
    PoisonOr.value_bind, completedCalls_kernel u extended completed huwf hextended hcompleted,
    EffectM.pure_eq]

theorem prefix_preserves (E : ⟪SerialConstructor.kernel.Γ⟫)
    (completed extended doubled table : Pointer) (i : Fin 7) :
    PrefixEq (prefixInput E completed extended doubled table i)
      (prefixResult E completed extended doubled table i) 141 := by
  unfold prefixResult
  exact ((PrefixEq.refl _ 141).write _ _ (by decide)).write _ _ (by decide)

def tailInput (E : ⟪SerialConstructor.kernel.Γ⟫) (table cached : Pointer) (i : Fin 7) :
    ⟪SerialConstructor.kernel.Γ⟫ :=
  E[%18 := .value 160#64, %27 := .value 7#64, %33 := .value cached,
    %36 := .value table, %141 := .value (BitVec.ofNat 64 (i.val + 1))]

def tailResult (E : ⟪SerialConstructor.kernel.Γ⟫) (table cached : Pointer) (i : Fin 7) :
    ⟪SerialConstructor.kernel.Γ⟫ :=
  (tailInput E table cached i)[
    %184 := .value (table.add (BitVec.ofNat 64 (160 * (i.val + 1)))),
    %185 := .value (if i.val = 6 then 1#1 else 0#1)]

def tailState (s : GlobalState) (table cached : Pointer) (i : Fin 7) : GlobalState :=
  {s with mem :=
    s.mem.storeAt (table.add (BitVec.ofNat 64 (160 * (i.val + 1)))) (s.mem.readAt cached 1280)}

/-- Exact last six instructions: successor address, copy, lifetimes and test. -/
theorem tail_body (p : SerialConstructor.Primitives)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (table cached : Pointer) (i : Fin 7)
    (s : GlobalState) (htable : SmallRange s.mem table 1280)
    (hcached : SmallRange s.mem cached 160) (hne : table.id ≠ cached.id) :
    List.foldlM Instr.run (tailInput E table cached i)
      ((SerialConstructor.kernel.bb2 p).body.drop 67) s =
      .value (tailResult E table cached i, tailState s table cached i) := by
  have hgep := (ConstructorMemory.record_geps htable i).2
  have hnext := (ConstructorMemory.record_bounds htable i).2
  have hcopy (env : ⟪SerialConstructor.kernel.Γ⟫) :=
    run_memcpy (n := 160) (env := env) (s := s)
      (show (160#64).toNat = 160 from rfl)
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne)) hnext.fits hcached.fits
  have hcmp := (ConstructorMemory.cursor_arithmetic i).2.1
  simp [SerialConstructor.kernel.bb2, tailInput, tailResult, tailState,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    GepIndex.inboundsOffset, hgep, hcopy, hcmp]

/-- The exact conditional jump terminates on the seventh successor. -/
theorem tail_exit (p : SerialConstructor.Primitives)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (table cached : Pointer) (i : Fin 7)
    (s : GlobalState) :
    (SerialConstructor.kernel.bb2 p).exit.run SerialConstructor.kernel.blockParams
      (tailResult E table cached i) s =
      .value ((if i.val = 6 then tailResult E table cached i
        else (tailResult E table cached i)[%140 := .value (BitVec.ofNat 64 (i.val + 1))],
        .inr (if i.val = 6 then 1 else 2)), s) := by
  fin_cases i <;> simp [SerialConstructor.kernel.bb2, Exit.run, Jump.run,
    SerialConstructor.kernel.blockParams, tailResult, tailInput, mlir_env, EffectM.pure_eq]
  all_goals rfl

theorem tail_preserves (E : ⟪SerialConstructor.kernel.Γ⟫)
    (table cached : Pointer) (i : Fin 7) :
    PrefixEq (tailInput E table cached i) (tailResult E table cached i) 184 := by
  unfold tailResult
  exact ((PrefixEq.refl _ 184).write _ _ (by decide)).write _ _ (by decide)

end Agave.Ed25519.Tables.SerialConstructorLoopWrapper
