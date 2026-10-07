import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendCoreBlocks

/-! Control-flow composition of the imported append, including the two early
returns. Every step uses an exact source basic-block execution theorem. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

variable (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))

theorem next_block (i j : Fin 11) (E F : Env program.Γ) (s t : GlobalState)
    (h : ((program core).blocks i).run program.blockParams E s =
      .value ((F, .inr j), t)) :
    (program core).runFrom E i s = (program core).runFrom F j t := by
  rw [Func.runFrom_eq]
  rw [h]
  rfl

theorem return_run (E : Env program.Γ) (s : GlobalState) (context : PoisonOr Pointer)
    (h : E.read (%arg0) = context) :
    (program core).runFrom E 10 s = .value (.cons context .nil, s) := by
  rw [Func.runFrom_eq]
  change (program.bb10.run program.blockParams E s >>= _) = _
  rw [return_block E s context h]
  rfl

def remainderEnv (E : Env program.Γ) (size : Word) : Env program.Γ :=
  E[%40 := .value (size &&& 127#64), %41 := .value (BitVec.ofBool (size &&& 127#64 == 0#64))]

def tailState (s : GlobalState) (context data : Pointer) (size : Word) : GlobalState :=
  if size &&& 127#64 = 0#64 then s else {s with mem := tailMemory s.mem context data size}

theorem tail_run (E : Env program.Γ) (s : GlobalState) (context data : Pointer)
    (size : Word) (h : CommonReady E context)
    (hd : E.read (%36) = .value data) (hs : E.read (%37) = .value size)
    (hc : SmallRange s.mem context 224) (hi : SmallRange s.mem data size.toNat)
    (hne : context.id ≠ data.id) :
    (program core).runFrom E 8 s =
      .value (.cons (.value context) .nil, tailState s context data size) := by
  have ha : E.args 0 = .value context := h.argContext
  let F := remainderEnv E size
  have hb := remainder_body E s size hs h.low h.zero
  change List.foldlM Instr.run E program.bb8.body s = .value (F, s) at hb
  have hstep : program.bb8.run program.blockParams E s =
      .value ((F, .inr (if size &&& 127#64 = 0#64 then 10 else 9)), s) := by
    simp only [BasicBlock.run, EffectM.bind_eq, hb, PoisonOr.value_bind]
    by_cases hz : size &&& 127#64 = 0#64 <;>
      simp [program.bb8, F, remainderEnv, Exit.run, Jump.run, Regs.read_nil,
        Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect, hz, ofBool_eq_one_iff]
  rw [next_block core 8 _ E F s s hstep]
  by_cases hz : size &&& 127#64 = 0#64
  · simp only [hz, ↓reduceIte, tailState]
    exact return_run core F s (.value context) (by simpa [F, remainderEnv, mlir_env] using h.argContext)
  · simp only [hz, ↓reduceIte, tailState]
    have hF : CommonReady F context := by
      constructor <;> simp [F, remainderEnv, mlir_env, ha, h.zero, h.full,
        h.one, h.shift, h.low, h.high, h.chain, h.count]
    have hdF : F.read (%36) = .value data := by simpa [F, remainderEnv, mlir_env] using hd
    have hsF : F.read (%37) = .value size := by simpa [F, remainderEnv, mlir_env] using hs
    have ht := tail_body F s context data size hF hdF hsF
      (by simp [F, remainderEnv, mlir_env]) hc hi hne
    have h9 : program.bb9.run program.blockParams F s =
        .value ((tailEnv F data size, .inr 10),
          {s with mem := tailMemory s.mem context data size}) := by
      simp only [BasicBlock.run, EffectM.bind_eq, ht, PoisonOr.value_bind]
      simp [program.bb9, Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
        EffectM.pure_eq, mlir_env, mlir_effect]
    rw [next_block core 9 10 F _ s _ h9]
    exact return_run core _ _ (.value context) (by
      simpa [tailEnv, F, remainderEnv, mlir_env] using h.argContext)

def fullEnv (E : Env program.Γ) (size : Word) : Env program.Γ :=
  E[%38 := .value (BitVec.ofBool (size.ult 128#64))]

theorem direct_short_run (E : Env program.Γ) (s : GlobalState) (context data : Pointer)
    (size : Word) (h : CommonReady E context)
    (hd : E.read (%36) = .value data) (hs : E.read (%37) = .value size)
    (hc : SmallRange s.mem context 224) (hi : SmallRange s.mem data size.toNat)
    (hne : context.id ≠ data.id) (hshort : size.toNat < 128) :
    (program core).runFrom E 6 s =
      .value (.cons (.value context) .nil, tailState s context data size) := by
  have ha : E.args 0 = .value context := h.argContext
  let F := fullEnv E size
  have hb := full_body E s size hs h.full
  change List.foldlM Instr.run E program.bb6.body s = .value (F, s) at hb
  have hstep : program.bb6.run program.blockParams E s = .value ((F, .inr 8), s) := by
    simp only [BasicBlock.run, EffectM.bind_eq, hb, PoisonOr.value_bind]
    simp [program.bb6, F, fullEnv, Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
      EffectM.pure_eq, mlir_env, mlir_effect, ofBool_eq_one_iff, BitVec.ult, hshort]
  rw [next_block core 6 8 E F s s hstep]
  apply tail_run core F s context data size _ _ _ hc hi hne
  · constructor <;> simp [F, fullEnv, mlir_env, ha, h.zero, h.full,
      h.one, h.shift, h.low, h.high, h.chain, h.count]
  · simpa [F, fullEnv, mlir_env] using hd
  · simpa [F, fullEnv, mlir_env] using hs

theorem direct_blocks_run (E : Env program.Γ) (s after : GlobalState) (context data : Pointer)
    (size : Word) (h : CommonReady E context)
    (hd : E.read (%36) = .value data) (hs : E.read (%37) = .value size)
    (hc : SmallRange after.mem context 224) (hi : SmallRange after.mem data size.toNat)
    (hne : context.id ≠ data.id) (hlong : 128 ≤ size.toNat)
    (hcall : core (.cons (.value (context.add 128#64)) (.cons (.value data)
      (.cons (.value (size >>> 7)) .nil))) s = .value (.nil, after)) :
    (program core).runFrom E 6 s =
      .value (.cons (.value context) .nil, tailState after context data size) := by
  have ha : E.args 0 = .value context := h.argContext
  let F := fullEnv E size
  have hb := full_body E s size hs h.full
  change List.foldlM Instr.run E program.bb6.body s = .value (F, s) at hb
  have hstep : program.bb6.run program.blockParams E s = .value ((F, .inr 7), s) := by
    simp only [BasicBlock.run, EffectM.bind_eq, hb, PoisonOr.value_bind]
    have hn : ¬size.toNat < 128 := by omega
    simp [program.bb6, F, fullEnv, Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
      EffectM.pure_eq, mlir_env, mlir_effect, ofBool_eq_one_iff, BitVec.ult, hn]
  rw [next_block core 6 7 E F s s hstep]
  have hF : CommonReady F context := by
    constructor <;> simp [F, fullEnv, mlir_env, ha, h.zero, h.full,
      h.one, h.shift, h.low, h.high, h.chain, h.count]
  have hdF : F.read (%36) = .value data := by simpa [F, fullEnv, mlir_env] using hd
  have hsF : F.read (%37) = .value size := by simpa [F, fullEnv, mlir_env] using hs
  have hbb := bulk_body core F s after context data size hF hdF hsF hcall
  have h7 : (program.bb7 core).run program.blockParams F s =
      .value ((F[%39 := .value (size >>> 7)], .inr 8), after) := by
    simp only [BasicBlock.run, EffectM.bind_eq, hbb, PoisonOr.value_bind]
    simp [program.bb7, Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
      EffectM.pure_eq, mlir_env, mlir_effect]
  rw [next_block core 7 8 F _ s after h7]
  apply tail_run core _ after context data size _ _ _ hc hi hne
  · constructor <;> simp [F, fullEnv, mlir_env, ha, h.zero, h.full,
      h.one, h.shift, h.low, h.high, h.chain, h.count]
  · simpa [F, fullEnv, mlir_env] using hd
  · simpa [F, fullEnv, mlir_env] using hs

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
