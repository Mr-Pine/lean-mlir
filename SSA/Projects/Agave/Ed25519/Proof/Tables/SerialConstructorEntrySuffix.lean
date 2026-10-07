import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorRegisters
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorState
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialConversionCalls
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleExecution

/-! Exact original entry instructions 117–178. The only abstract effect is the
single point-double invocation; all eleven copies, four field multiplications,
and forty pointer destinations are executed here. -/
namespace Agave.Ed25519.Tables.SerialConstructorEntrySuffix
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase.RIR (PrefixEq fieldState fieldState_wf fieldState_buffer completedState)

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

abbrev Slots := Fin 7 → Pointer

def copyState (s : GlobalState) (out input : Pointer) (bytes : Nat) : GlobalState :=
  {s with mem := s.mem.storeAt out (s.mem.readAt input (8 * bytes))}

theorem copyState_buffer (h : Buffer s.mem q bytes) (out input : Pointer) (count : Nat) :
    Buffer (copyState s out input count).mem q bytes := h.storeAt _ _

theorem copyState_wf (hwf : s.WF) (out input : Pointer) (count : Nat) :
    (copyState s out input count).WF := hwf.storeAt

/-- Successive physical cache copies, in their original order. -/
def broadcastState (s : GlobalState) (table cache : Pointer) : Nat → GlobalState
  | 0 => s
  | n + 1 => copyState (broadcastState s table cache n)
      (table.add (BitVec.ofNat 64 (160 * n))) cache 160

theorem broadcastState_buffer (h : Buffer s.mem q bytes) (table cache : Pointer) (n : Nat) :
    Buffer (broadcastState s table cache n).mem q bytes := by
  induction n with
  | zero => exact h
  | succ n ih => exact copyState_buffer ih _ _ _

theorem broadcastState_wf (hwf : s.WF) (table cache : Pointer) (n : Nat) :
    (broadcastState s table cache n).WF := by
  induction n with
  | zero => exact hwf
  | succ n ih => exact copyState_wf ih _ _ _

def projectiveY (s : GlobalState) (slots : Slots) (table input : Pointer) : GlobalState :=
  copyState (broadcastState s table (slots 6) 8) ((slots 0).add 40#64) (input.add 40#64) 40

def projectiveZ (s : GlobalState) (slots : Slots) (table input : Pointer) : GlobalState :=
  copyState (projectiveY s slots table input) ((slots 0).add 80#64) (input.add 80#64) 40

def preparedState (s : GlobalState) (slots : Slots) (table input : Pointer) : GlobalState :=
  copyState (projectiveZ s slots table input) (slots 0) input 40

theorem preparedState_buffer (h : Buffer s.mem q bytes) (slots : Slots) (table input : Pointer) :
    Buffer (preparedState s slots table input).mem q bytes :=
  copyState_buffer (copyState_buffer (copyState_buffer
    (broadcastState_buffer h _ _ _) _ _ _) _ _ _) _ _ _

theorem preparedState_wf (hwf : s.WF) (slots : Slots) (table input : Pointer) :
    (preparedState s slots table input).WF :=
  copyState_wf (copyState_wf (copyState_wf
    (broadcastState_wf hwf _ _ _) _ _ _) _ _ _) _ _ _

def suffixInput (E : ⟪SerialConstructor.kernel.Γ⟫) (slots : Slots) (table input : Pointer) :
    ⟪SerialConstructor.kernel.Γ⟫ :=
  E[%1 := .value 40#64,
    %2 := .value 48#64,
    %3 := .value 56#64,
    %4 := .value 64#64,
    %5 := .value 72#64,
    %6 := .value 8#64,
    %7 := .value 16#64,
    %8 := .value 24#64,
    %9 := .value 32#64,
    %15 := .value 80#64,
    %16 := .value 120#64,
    %18 := .value 160#64,
    %19 := .value 320#64,
    %20 := .value 480#64,
    %21 := .value 640#64,
    %22 := .value 800#64,
    %23 := .value 960#64,
    %24 := .value 1120#64,
    %29 := .value (slots 0),
    %30 := .value (slots 1),
    %31 := .value (slots 2),
    %32 := .value (slots 3),
    %33 := .value (slots 4),
    %34 := .value (slots 5),
    %35 := .value (slots 6),
    %36 := .value table,
    %37 := .value (input.add 40#64),
    %87 := .value (input.add 80#64)]

def suffixResult (E : ⟪SerialConstructor.kernel.Γ⟫) (slots : Slots) (table input : Pointer) :
    ⟪SerialConstructor.kernel.Γ⟫ :=
  (suffixInput E slots table input)[
    %100 := .value (table.add 160#64),
    %101 := .value (table.add 320#64),
    %102 := .value (table.add 480#64),
    %103 := .value (table.add 640#64),
    %104 := .value (table.add 800#64),
    %105 := .value (table.add 960#64),
    %106 := .value (table.add 1120#64),
    %107 := .value ((slots 0).add 40#64),
    %108 := .value ((slots 0).add 80#64),
    %109 := .value ((slots 1).add 120#64),
    %110 := .value ((slots 1).add 40#64),
    %111 := .value ((slots 1).add 80#64),
    %112 := .value ((slots 5).add 40#64),
    %113 := .value ((slots 5).add 80#64),
    %114 := .value ((slots 5).add 120#64),
    %115 := .value ((slots 2).add 120#64),
    %116 := .value ((slots 2).add 40#64),
    %117 := .value ((slots 2).add 80#64),
    %118 := .value ((slots 3).add 40#64),
    %119 := .value ((slots 3).add 80#64),
    %120 := .value ((slots 3).add 120#64),
    %121 := .value ((slots 3).add 48#64),
    %122 := .value ((slots 3).add 56#64),
    %123 := .value ((slots 3).add 64#64),
    %124 := .value ((slots 3).add 72#64),
    %125 := .value ((slots 3).add 8#64),
    %126 := .value ((slots 3).add 16#64),
    %127 := .value ((slots 3).add 24#64),
    %128 := .value ((slots 3).add 32#64),
    %129 := .value ((slots 4).add 80#64),
    %130 := .value ((slots 4).add 120#64),
    %131 := .value ((slots 4).add 8#64),
    %132 := .value ((slots 4).add 16#64),
    %133 := .value ((slots 4).add 24#64),
    %134 := .value ((slots 4).add 32#64),
    %135 := .value ((slots 4).add 40#64),
    %136 := .value ((slots 4).add 48#64),
    %137 := .value ((slots 4).add 56#64),
    %138 := .value ((slots 4).add 64#64),
    %139 := .value ((slots 4).add 72#64)]

theorem suffixResult_prefix (E : ⟪SerialConstructor.kernel.Γ⟫) (slots : Slots)
    (table input : Pointer) :
    PrefixEq (suffixInput E slots table input) (suffixResult E slots table input) 100 := by
  unfold suffixResult
  iterate 40 apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

private theorem copy_run (E : ⟪Γ⟫) (s : GlobalState) (out input : Pointer) (bytes : Nat)
    (hb : bytes < 2^64) (ho : Buffer s.mem out bytes) (hi : Buffer s.mem input bytes)
    (hne : out.id ≠ input.id) :
    Operation.memcpy (.value out) (.value input) (.value (BitVec.ofNat 64 bytes)) E s =
      .value (E, copyState s out input bytes) := by
  exact run_memcpy (n := bytes) (env := E) (s := s)
    (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb])
    (Range.disjoint_of_id_ne hne) ho.fits hi.fits

/-- Execute the original suffix. The remaining premise names precisely one
callee, and no premise assumes success of any constructor instruction list. -/
theorem suffix_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (hfield : p.call0 = SerialFieldMul.kernel.call)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (slots : Slots) (table input : Pointer)
    (s u : GlobalState) (harg : E.args 1 = .value input)
    (hslots : ∀ i, Buffer s.mem (slots i) (if i = 0 then 120 else 160))
    (htable : Buffer s.mem table 1280) (hinput : Buffer s.mem input 160)
    (htc : table.id ≠ (slots 6).id) (hpi : (slots 0).id ≠ input.id)
    (hdouble : p.call1 (.cons (.value (slots 1)) (.cons (.value (slots 0)) .nil))
      (preparedState s slots table input) = .value (.nil, u))
    (huwf : u.WF) (huslots : ∀ i, Buffer u.mem (slots i) (if i = 0 then 120 else 160)) :
    List.foldlM Instr.run (suffixInput E slots table input)
      ((SerialConstructor.kernel.bb0 p g).body.drop 117) s =
      .value (suffixResult E slots table input, completedState u (slots 5) (slots 1)) := by
  have hcache : Buffer s.mem (slots 6) 160 := by simpa using hslots 6
  have hprojective : Buffer s.mem (slots 0) 120 := by simpa using hslots 0
  have hcopy (k : Fin 8) (env : ⟪SerialConstructor.kernel.Γ⟫) :
      Operation.memcpy (.value (table.add (BitVec.ofNat 64 (160*k.val))))
        (.value (slots 6)) (.value 160#64) env (broadcastState s table (slots 6) k.val) =
        .value (env, broadcastState s table (slots 6) (k.val+1)) := by
    exact copy_run env _ _ _ 160 (by decide)
      ((broadcastState_buffer htable _ _ _).slice _ _ (by have := k.isLt; omega))
      (broadcastState_buffer hcache _ _ _) (by simpa only [Pointer.add_id] using htc)
  have hc0 := hcopy ⟨0, by decide⟩
  have hc1 := hcopy ⟨1, by decide⟩
  have hc2 := hcopy ⟨2, by decide⟩
  have hc3 := hcopy ⟨3, by decide⟩
  have hc4 := hcopy ⟨4, by decide⟩
  have hc5 := hcopy ⟨5, by decide⟩
  have hc6 := hcopy ⟨6, by decide⟩
  have hc7 := hcopy ⟨7, by decide⟩
  simp only [Fin.val_mk, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, Pointer.add_zero] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  change ∀ env, Operation.memcpy (.value table) (.value (slots 6)) (.value 160#64) env s =
    .value (env, broadcastState s table (slots 6) 1) at hc0
  have hg1 := (broadcastState_buffer htable table (slots 6) 1).gep 160 (by decide)
  have hg2 := (broadcastState_buffer htable table (slots 6) 2).gep 320 (by decide)
  have hg3 := (broadcastState_buffer htable table (slots 6) 3).gep 480 (by decide)
  have hg4 := (broadcastState_buffer htable table (slots 6) 4).gep 640 (by decide)
  have hg5 := (broadcastState_buffer htable table (slots 6) 5).gep 800 (by decide)
  have hg6 := (broadcastState_buffer htable table (slots 6) 6).gep 960 (by decide)
  have hg7 := (broadcastState_buffer htable table (slots 6) 7).gep 1120 (by decide)
  have hcy (env : ⟪SerialConstructor.kernel.Γ⟫) :
      Operation.memcpy (.value ((slots 0).add 40#64)) (.value (input.add 40#64))
        (.value 40#64) env (broadcastState s table (slots 6) 8) =
        .value (env, projectiveY s slots table input) :=
    copy_run env _ _ _ 40 (by decide)
      ((broadcastState_buffer hprojective _ _ _).slice 40 40 (by decide))
      ((broadcastState_buffer hinput _ _ _).slice 40 40 (by decide))
      (by simpa only [Pointer.add_id] using hpi)
  have hcz (env : ⟪SerialConstructor.kernel.Γ⟫) :
      Operation.memcpy (.value ((slots 0).add 80#64)) (.value (input.add 80#64))
        (.value 40#64) env (projectiveY s slots table input) =
        .value (env, projectiveZ s slots table input) :=
    copy_run env _ _ _ 40 (by decide)
      ((copyState_buffer (broadcastState_buffer hprojective _ _ _) _ _ _).slice 80 40 (by decide))
      ((copyState_buffer (broadcastState_buffer hinput _ _ _) _ _ _).slice 80 40 (by decide))
      (by simpa only [Pointer.add_id] using hpi)
  have hcx (env : ⟪SerialConstructor.kernel.Γ⟫) :
      Operation.memcpy (.value (slots 0)) (.value input) (.value 40#64)
        env (projectiveZ s slots table input) = .value (env, preparedState s slots table input) :=
    copy_run env _ _ _ 40 (by decide)
      (by simpa only [Pointer.add_zero, projectiveZ, projectiveY] using
        (copyState_buffer (copyState_buffer (broadcastState_buffer hprojective _ _ _) _ _ _) _ _ _).slice 0 40 (by decide))
      (by simpa only [Pointer.add_zero, projectiveZ, projectiveY] using
        (copyState_buffer (copyState_buffer (broadcastState_buffer hinput _ _ _) _ _ _) _ _ _).slice 0 40 (by decide)) hpi
  have hgy := (broadcastState_buffer hprojective table (slots 6) 8).gep 40 (by decide)
  have hgz := (copyState_buffer (broadcastState_buffer hprojective table (slots 6) 8)
    ((slots 0).add 40#64) (input.add 40#64) 40).gep 80 (by decide)
  change Operation.gepInboundsLive (projectiveY s slots table input).mem _ _ = _ at hgz
  have hu1 : Buffer u.mem (slots 1) 160 := by simpa using huslots 1
  have hu5 : Buffer u.mem (slots 5) 160 := by simpa using huslots 5
  let u1 := fieldState u (slots 5) (slots 1) ((slots 1).add 120#64)
  let u2 := fieldState u1 ((slots 5).add 40#64) ((slots 1).add 40#64) ((slots 1).add 80#64)
  let u3 := fieldState u2 ((slots 5).add 80#64) ((slots 1).add 80#64) ((slots 1).add 120#64)
  have bu1 {q : Pointer} {bytes : Nat} (h : Buffer u.mem q bytes) : Buffer u1.mem q bytes :=
    fieldState_buffer h _ _ _
  have bu2 {q : Pointer} {bytes : Nat} (h : Buffer u.mem q bytes) : Buffer u2.mem q bytes :=
    fieldState_buffer (bu1 h) _ _ _
  have bu3 {q : Pointer} {bytes : Nat} (h : Buffer u.mem q bytes) : Buffer u3.mem q bytes :=
    fieldState_buffer (bu2 h) _ _ _
  have hu50 := hu5.slice 0 40 (by decide)
  have hu10 := hu1.slice 0 40 (by decide)
  have hu310 := (bu3 hu1).slice 0 40 (by decide)
  simp only [Pointer.add_zero] at hu50 hu10 hu310
  have hf1 := SerialFieldMul.kernel_call (slots 5) (slots 1) ((slots 1).add 120#64) u huwf
    hu50
    hu10
    (hu1.slice 120 40 (by decide))
  have hf2 := SerialFieldMul.kernel_call ((slots 5).add 40#64) ((slots 1).add 40#64)
    ((slots 1).add 80#64) u1 (fieldState_wf _ _ _ _ huwf)
    ((bu1 hu5).slice 40 40 (by decide)) ((bu1 hu1).slice 40 40 (by decide))
    ((bu1 hu1).slice 80 40 (by decide))
  have hf3 := SerialFieldMul.kernel_call ((slots 5).add 80#64) ((slots 1).add 80#64)
    ((slots 1).add 120#64) u2 (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ huwf))
    ((bu2 hu5).slice 80 40 (by decide)) ((bu2 hu1).slice 80 40 (by decide))
    ((bu2 hu1).slice 120 40 (by decide))
  have hf4 := SerialFieldMul.kernel_call ((slots 5).add 120#64) (slots 1)
    ((slots 1).add 40#64) u3
    (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ huwf)))
    ((bu3 hu5).slice 120 40 (by decide))
    hu310
    ((bu3 hu1).slice 40 40 (by decide))
  change SerialFieldMul.kernel.call _ u = .value (.nil, u1) at hf1
  change SerialFieldMul.kernel.call _ u1 = .value (.nil, u2) at hf2
  change SerialFieldMul.kernel.call _ u2 = .value (.nil, u3) at hf3
  change SerialFieldMul.kernel.call _ u3 =
    .value (.nil, completedState u (slots 5) (slots 1)) at hf4
  simp only [SerialFieldMul.kernel.args] at hf1 hf2 hf3 hf4
  have hg109 := hu1.gep 120 (by decide)
  have hg110 := (bu1 hu1).gep 40 (by decide)
  have hg111 := (bu1 hu1).gep 80 (by decide)
  have hg112 := (bu1 hu5).gep 40 (by decide)
  have hg113 := (bu2 hu5).gep 80 (by decide)
  have hg114 := (bu3 hu5).gep 120 (by decide)
  have hg115 := (DoubleBase.RIR.completedState_buffer (huslots 2) (slots 5) (slots 1)).gep 120 (by decide)
  have hg116 := (DoubleBase.RIR.completedState_buffer (huslots 2) (slots 5) (slots 1)).gep 40 (by decide)
  have hg117 := (DoubleBase.RIR.completedState_buffer (huslots 2) (slots 5) (slots 1)).gep 80 (by decide)
  have hg118 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 40 (by decide)
  have hg119 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 80 (by decide)
  have hg120 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 120 (by decide)
  have hg121 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 48 (by decide)
  have hg122 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 56 (by decide)
  have hg123 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 64 (by decide)
  have hg124 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 72 (by decide)
  have hg125 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 8 (by decide)
  have hg126 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 16 (by decide)
  have hg127 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 24 (by decide)
  have hg128 := (DoubleBase.RIR.completedState_buffer (huslots 3) (slots 5) (slots 1)).gep 32 (by decide)
  have hg129 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 80 (by decide)
  have hg130 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 120 (by decide)
  have hg131 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 8 (by decide)
  have hg132 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 16 (by decide)
  have hg133 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 24 (by decide)
  have hg134 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 32 (by decide)
  have hg135 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 40 (by decide)
  have hg136 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 48 (by decide)
  have hg137 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 56 (by decide)
  have hg138 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 64 (by decide)
  have hg139 := (DoubleBase.RIR.completedState_buffer (huslots 4) (slots 5) (slots 1)).gep 72 (by decide)
  simp only [Int.cast_ofNat_Int] at hg1 hg2 hg3 hg4 hg5 hg6 hg7 hgy hgz hg109 hg110 hg111 hg112 hg113 hg114 hg115 hg116 hg117 hg118 hg119 hg120 hg121 hg122 hg123 hg124 hg125 hg126 hg127 hg128 hg129 hg130 hg131 hg132 hg133 hg134 hg135 hg136 hg137 hg138 hg139
  simp [SerialConstructor.kernel.bb0, suffixInput, suffixResult,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    Env.writeMany_nil, harg, hfield, hdouble, hf1, hf2, hf3, hf4,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcy, hcz, hcx,
    hg1, hg2, hg3, hg4, hg5, hg6, hg7, hgy, hgz, hg109, hg110, hg111, hg112, hg113, hg114, hg115, hg116, hg117, hg118, hg119, hg120, hg121, hg122, hg123, hg124, hg125, hg126, hg127, hg128, hg129, hg130, hg131, hg132, hg133, hg134, hg135, hg136, hg137, hg138, hg139]

/-- Exact normal form of the real projective-double call after the copies. -/
def doubledState (s : GlobalState) (slots : Slots) (table input : Pointer) : GlobalState :=
  let prepared := preparedState s slots table input
  SerialPoint.Execution.pointPost prepared (slots 1)
    (SerialPoint.Execution.doubleWordTrace (SerialPoint.Execution.readPointWords prepared (slots 0))) 5

/-- Specialization to both imported arithmetic kernels. No successful helper
call or constructor-suffix execution remains as a premise. -/
theorem suffix_actual_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (hfield : p.call0 = SerialFieldMul.kernel.call)
    (hdouble : p.call1 =
      (SerialPoint.double Encoding.Decompress.Execution.Pow2k.program.call).call)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (slots : Slots) (table input : Pointer)
    (s : GlobalState) (hwf : s.WF) (harg : E.args 1 = .value input)
    (hslots : ∀ i, Buffer s.mem (slots i) (if i = 0 then 120 else 160))
    (htable : Buffer s.mem table 1280) (hinput : Buffer s.mem input 160)
    (htc : table.id ≠ (slots 6).id) (hpi : (slots 0).id ≠ input.id) :
    List.foldlM Instr.run (suffixInput E slots table input)
      ((SerialConstructor.kernel.bb0 p g).body.drop 117) s =
      .value (suffixResult E slots table input,
        completedState (doubledState s slots table input) (slots 5) (slots 1)) := by
  have hpwf := preparedState_wf hwf slots table input
  have hp0 : Buffer (preparedState s slots table input).mem (slots 0) 120 := by
    simpa using preparedState_buffer (hslots 0) slots table input
  have hp1 : Buffer (preparedState s slots table input).mem (slots 1) 160 := by
    simpa using preparedState_buffer (hslots 1) slots table input
  have hd := SerialPoint.Execution.double_call (slots 1) (slots 0)
    (preparedState s slots table input) hpwf hp1 hp0
  rw [← hdouble] at hd
  have huw : (doubledState s slots table input).WF :=
    SerialPoint.Execution.pointPost_wf _ hpwf _ _ _
  have hub (i : Fin 7) : Buffer (doubledState s slots table input).mem (slots i)
      (if i = 0 then 120 else 160) :=
    SerialPoint.Execution.smallRange_storePointWords
      (preparedState_buffer (hslots i) slots table input) _ _
  exact suffix_run p g hfield E slots table input s _ harg hslots htable hinput htc hpi
    hd huw hub


theorem copyState_writesOnly (s : GlobalState) (out input : Pointer) (bytes : Nat)
    (hwf : s.WF) : DoubleBase.SerialContracts.WritesOnly out bytes s (copyState s out input bytes) :=
  ⟨hwf.storeAt, le_refl _, SerialPoint.Execution.storeAt_allocationShape s.mem out _,
    fun _ _ hd => MemoryState.readAt_storeAt_disjoint hd.symm _⟩

theorem broadcastState_frame (s : GlobalState) (table cache : Pointer) (n : Nat)
    (hwf : s.WF) (ht : Buffer s.mem table 1280) (hn : n ≤ 8) :
    DoubleBase.SerialContracts.WritesOnly table 1280 s (broadcastState s table cache n) := by
  induction n with
  | zero => exact ⟨hwf, le_refl _, fun _ => rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    have hprev := ih (by omega)
    exact DoubleBase.RIR.writesOnly_trans hprev
      (DoubleBase.RIR.writesOnly_widen
        (copyState_writesOnly _ _ cache 160 hprev.wellFormed)
        (broadcastState_buffer ht table cache n) (by omega))

theorem preparedState_frame (s : GlobalState) (slots : Slots) (table input : Pointer)
    (hwf : s.WF) (ht : Buffer s.mem table 1280) (hp : Buffer s.mem (slots 0) 120) :
    SerialConstructorState.Frame slots table s (preparedState s slots table input) := by
  have hb := broadcastState_frame s table (slots 6) 8 hwf ht (by decide)
  have hy := copyState_writesOnly (broadcastState s table (slots 6) 8)
    ((slots 0).add 40#64) (input.add 40#64) 40 hb.wellFormed
  have hz := copyState_writesOnly (projectiveY s slots table input)
    ((slots 0).add 80#64) (input.add 80#64) 40 hy.wellFormed
  have hx := copyState_writesOnly (projectiveZ s slots table input)
    (slots 0) input 40 hz.wellFormed
  have hy' := DoubleBase.RIR.writesOnly_widen hy
    (broadcastState_buffer hp table (slots 6) 8) (by decide)
  have hz' := DoubleBase.RIR.writesOnly_widen hz
    (copyState_buffer (broadcastState_buffer hp table (slots 6) 8)
      ((slots 0).add 40#64) (input.add 40#64) 40) (by decide)
  exact ((SerialConstructorState.Frame.tableWrite hb rfl).trans
    (SerialConstructorState.Frame.slot 0 hy')).trans
    ((SerialConstructorState.Frame.slot 0 hz').trans (SerialConstructorState.Frame.slot 0 hx))

theorem broadcastState_readAt_ne (s : GlobalState) (table cache q : Pointer)
    (n bits : Nat) (hne : table.id ≠ q.id) :
    (broadcastState s table cache n).mem.readAt q bits = s.mem.readAt q bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold broadcastState copyState
    rw [MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne)), ih]

private theorem copyState_readLimbs_ne (s : GlobalState) (out input q : Pointer) (bytes : Nat)
    (hne : out.id ≠ q.id) :
    SerialFieldMul.readLimbs (copyState s out input bytes) q = SerialFieldMul.readLimbs s q := by
  funext i
  unfold SerialFieldMul.readLimbs copyState
  rw [MemoryState.readAt_storeAt_disjoint
    (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne))]

private theorem copyState_readLimbs_frame (s : GlobalState) (out input q : Pointer) (bytes : Nat)
    (hq : Buffer s.mem q 40)
    (hd : (Range.of q 320).Disjoint (Range.of out (8*bytes))) :
    SerialFieldMul.readLimbs (copyState s out input bytes) q = SerialFieldMul.readLimbs s q := by
  funext i
  unfold SerialFieldMul.readLimbs copyState
  exact MemoryState.readAt_storeAt_disjoint
    (DoubleBase.RIR.range_disjoint_subrange hq hd.symm (k := 8*i.val) (count := 8)
      (by have := i.isLt; omega)) _

/-- The three projective copies preserve precisely the original X, Y, Z limbs. -/
theorem preparedState_readProjective (s : GlobalState) (slots : Slots) (table input : Pointer)
    (hp : Buffer s.mem (slots 0) 120) (hi : Buffer s.mem input 160)
    (hti : table.id ≠ input.id) (hpi : (slots 0).id ≠ input.id) :
    DoubleBase.SerialContracts.readProjective (preparedState s slots table input) (slots 0) =
      DoubleBase.SerialContracts.readProjective s input := by
  let b := broadcastState s table (slots 6) 8
  let y := projectiveY s slots table input
  let z := projectiveZ s slots table input
  have hbP : Buffer b.mem (slots 0) 120 := broadcastState_buffer hp _ _ _
  have hbI : Buffer b.mem input 160 := broadcastState_buffer hi _ _ _
  have hyP : Buffer y.mem (slots 0) 120 := copyState_buffer hbP _ _ _
  have hyI : Buffer y.mem input 160 := copyState_buffer hbI _ _ _
  have hzP : Buffer z.mem (slots 0) 120 := copyState_buffer hyP _ _ _
  have hzI : Buffer z.mem input 160 := copyState_buffer hyI _ _ _
  have h0P := hzP.slice 0 40 (by decide)
  have h0I := hzI.slice 0 40 (by decide)
  simp only [Pointer.add_zero] at h0P h0I
  have hXY := copyState_readLimbs_ne b ((slots 0).add 40#64) (input.add 40#64) input 40
    (by simpa only [Pointer.add_id] using hpi)
  have hXZ := copyState_readLimbs_ne y ((slots 0).add 80#64) (input.add 80#64) input 40
    (by simpa only [Pointer.add_id] using hpi)
  have hZY := copyState_readLimbs_ne b ((slots 0).add 40#64) (input.add 40#64) (input.add 80#64) 40
    (by simpa only [Pointer.add_id] using hpi)
  have hx := SerialCacheExecution.copyField_words z (slots 0) input h0P h0I
  have hy := SerialCacheExecution.copyField_words b ((slots 0).add 40#64) (input.add 40#64)
    (hbP.slice 40 40 (by decide)) (hbI.slice 40 40 (by decide))
  have hz := SerialCacheExecution.copyField_words y ((slots 0).add 80#64) (input.add 80#64)
    (hyP.slice 80 40 (by decide)) (hyI.slice 80 40 (by decide))
  have hdis (a b : Fin 3) (hne : a ≠ b) :
      (Range.of ((slots 0).add (BitVec.ofNat 64 (40*a.val))) 320).Disjoint
        (Range.of ((slots 0).add (BitVec.ofNat 64 (40*b.val))) 320) := by
    apply SerialPoint.Execution.subranges_disjoint hp (ni := 40) (nj := 40)
      (by have := a.isLt; omega) (by have := b.isLt; omega)
    have hab : a.val ≠ b.val := fun h => hne (Fin.ext h)
    omega
  have hyz := copyState_readLimbs_frame y ((slots 0).add 80#64) (input.add 80#64)
    ((slots 0).add 40#64) 40 (hyP.slice 40 40 (by decide))
    (by simpa using hdis 1 2 (by decide))
  have hyx := copyState_readLimbs_frame z (slots 0) input ((slots 0).add 40#64) 40
    (hzP.slice 40 40 (by decide)) (by simpa using hdis 1 0 (by decide))
  have hzx := copyState_readLimbs_frame z (slots 0) input ((slots 0).add 80#64) 40
    (hzP.slice 80 40 (by decide)) (by simpa using hdis 2 0 (by decide))
  have hinput (off : BitVec 64) : SerialFieldMul.readLimbs b (input.add off) =
      SerialFieldMul.readLimbs s (input.add off) := by
    funext i
    exact broadcastState_readAt_ne s table (slots 6) _ 8 64
      (by simpa only [Pointer.add_id] using hti)
  have hinput0 := hinput 0#64
  simp only [Pointer.add_zero] at hinput0
  apply PointArithmetic.Extended.ext
  · exact congrArg SerialFieldMul.unsigned (hx.trans (hXZ.trans (hXY.trans hinput0)))
  · exact congrArg SerialFieldMul.unsigned (hyx.trans (hyz.trans (hy.trans (hinput 40#64))))
  · exact congrArg SerialFieldMul.unsigned (hzx.trans (hz.trans (hZY.trans (hinput 80#64))))
  · rfl

/-- Later broadcast writes are disjoint from the first physical cache record. -/
theorem broadcastState_readCached_zero (s : GlobalState) (table cache : Pointer)
    (hwf : s.WF) (ht : Buffer s.mem table 1280) (hc : Buffer s.mem cache 160) :
    DoubleBase.SerialContracts.readCached (broadcastState s table cache 8) table =
      DoubleBase.SerialContracts.readCached s cache := by
  have hr (n : Nat) (hn : 0 < n) (hle : n ≤ 8) :
      DoubleBase.SerialContracts.readCached (broadcastState s table cache n) table =
        DoubleBase.SerialContracts.readCached s cache := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hz : n = 0
      · subst n
        simp only [broadcastState, Nat.mul_zero, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
        exact SerialConstructorState.copyRecord_readCached s table cache
          (by have h := ht.slice 0 160 (by decide); simp only [Pointer.add_zero] at h; exact h) hc
      · have hprev := ih (by omega) (by omega)
        have hwrite := copyState_writesOnly (broadcastState s table cache n)
          (table.add (BitVec.ofNat 64 (160*n))) cache 160 (broadcastState_wf hwf _ _ _)
        have hbase := (broadcastState_buffer ht table cache n).slice 0 160 (by decide)
        simp only [Pointer.add_zero] at hbase
        have hd : (Range.of table 1280).Disjoint
            (Range.of (table.add (BitVec.ofNat 64 (160*n))) 1280) := by
          have h := SerialPoint.Execution.subranges_disjoint ht
            (i := 0) (ni := 160) (j := 160*n) (nj := 160)
            (by decide) (by omega) (Or.inl (by omega))
          simpa only [BitVec.ofNat_eq_ofNat, Pointer.add_zero] using h
        exact (SerialConstructorState.cached_read_frame hwrite hbase hd).trans hprev
  exact hr 8 (by decide) (by decide)

/-- The projective copies leave the first broadcast cache record unchanged. -/
theorem preparedState_readCached_zero (s : GlobalState) (slots : Slots) (table input : Pointer)
    (hwf : s.WF) (ht : Buffer s.mem table 1280) (hc : Buffer s.mem (slots 6) 160)
    (hpt : (slots 0).id ≠ table.id) :
    DoubleBase.SerialContracts.readCached (preparedState s slots table input) table =
      DoubleBase.SerialContracts.readCached s (slots 6) := by
  have hb := broadcastState_readCached_zero s table (slots 6) hwf ht hc
  have hy := copyState_writesOnly (broadcastState s table (slots 6) 8)
    ((slots 0).add 40#64) (input.add 40#64) 40 (broadcastState_wf hwf _ _ _)
  have hz := copyState_writesOnly (projectiveY s slots table input)
    ((slots 0).add 80#64) (input.add 80#64) 40 hy.wellFormed
  have hx := copyState_writesOnly (projectiveZ s slots table input)
    (slots 0) input 40 hz.wellFormed
  exact (SerialConstructorState.cached_read_ne hx hpt).trans
    ((SerialConstructorState.cached_read_ne hz (by simpa only [Pointer.add_id] using hpt)).trans
      ((SerialConstructorState.cached_read_ne hy (by simpa only [Pointer.add_id] using hpt)).trans hb))

end Agave.Ed25519.Tables.SerialConstructorEntrySuffix

open Lean in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.suffix_run,
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.suffix_actual_run,
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.suffixResult_prefix,
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.copyState_writesOnly,
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.broadcastState_frame,
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.preparedState_frame,
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.broadcastState_readAt_ne,
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.preparedState_readProjective,
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.broadcastState_readCached_zero,
    `Agave.Ed25519.Tables.SerialConstructorEntrySuffix.preparedState_readCached_zero]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"

#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.suffix_run
#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.suffix_actual_run
#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.suffixResult_prefix

#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.copyState_writesOnly
#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.broadcastState_frame
#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.preparedState_frame
#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.broadcastState_readAt_ne
#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.preparedState_readProjective
#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.broadcastState_readCached_zero

#print axioms Agave.Ed25519.Tables.SerialConstructorEntrySuffix.preparedState_readCached_zero
