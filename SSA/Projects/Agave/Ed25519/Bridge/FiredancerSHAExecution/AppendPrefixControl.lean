import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendControl

/-! Exact buffered-prefix paths, including the source's early return when the
append fits wholly in the pending buffer. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

variable (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))

def shortState (s : GlobalState) (context data : Pointer) (used size : Word) : GlobalState :=
  {s with mem := countMemory (copyMemory s.mem (context.add used) data size) context (used + size)}

theorem buffer_short_run (E : Env program.Γ) (s : GlobalState) (context data : Pointer)
    (used size : Word) (h : CommonReady E context)
    (hd : E.read (%arg1) = .value data) (hs : E.read (%arg2) = .value size)
    (hu : E.read (%14) = .value used)
    (hc : SmallRange s.mem context 224) (hi : SmallRange s.mem data size.toNat)
    (hub : used.toNat < 128) (hshort : size.toNat < (128#64 - used).toNat)
    (hne : context.id ≠ data.id) :
    (program core).runFrom E 2 s =
      .value (.cons (.value context) .nil, shortState s context data used size) := by
  have ha : E.args 0 = .value context := h.argContext
  have hdata : E.args 1 = .value data := hd
  have hsize : E.args 2 = .value size := hs
  have hfill : (128#64 - used).toNat = 128 - used.toNat :=
    BitVec.toNat_sub_of_le (by change used.toNat ≤ 128; omega)
  let F := bufferEnv E context used size
  have hb := buffer_body E s context used size h hu hs hc hub
  change List.foldlM Instr.run E program.bb2.body s = .value (F, s) at hb
  have h2 : program.bb2.run program.blockParams E s = .value ((F, .inr 3), s) := by
    simp only [BasicBlock.run, EffectM.bind_eq, hb, PoisonOr.value_bind]
    have hb' : size.ult (128#64 - used) = true := by exact decide_eq_true hshort
    simp [program.bb2, F, bufferEnv, Exit.run, Jump.run, Regs.read_nil,
      Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect, hb']
  rw [next_block core 2 3 E F s s h2]
  let G := F[%30 := .value (used + size), %33 := .value (used + size),
    %34 := .value data, %35 := .value size]
  let copied := {s with mem := copyMemory s.mem (context.add used) data size}
  have h3body := short_body F s context data used size
    (by simp [F, bufferEnv, mlir_env])
    (by simpa [F, bufferEnv, mlir_env] using hd)
    (by simpa [F, bufferEnv, mlir_env] using hu)
    (by simpa [F, bufferEnv, mlir_env] using hs)
    hc hi (by omega) hne
  have h3 : program.bb3.run program.blockParams F s = .value ((G, .inr 5), copied) := by
    simp only [BasicBlock.run, EffectM.bind_eq, h3body, PoisonOr.value_bind]
    simp [program.bb3, G, copied, F, bufferEnv, Exit.run, Jump.run,
      Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
      EffectM.pure_eq, mlir_env, mlir_effect, hdata, hsize]
  rw [next_block core 3 5 F G s copied h3]
  have h5body := count_body G copied context (used + size)
    (by simpa [G, F, bufferEnv, mlir_env] using h.count)
    (by simp [G, mlir_env]) (hc.storeAt _ _)
  have h5 : program.bb5.run program.blockParams G copied =
      .value ((G, .inr 10), shortState s context data used size) := by
    simp only [BasicBlock.run, EffectM.bind_eq, h5body, PoisonOr.value_bind]
    have hb' : size.ult (128#64 - used) = true := by exact decide_eq_true hshort
    simp [program.bb5, G, F, bufferEnv, shortState, copied, Exit.run, Jump.run,
      Regs.read_nil, Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect, hb']
  rw [next_block core 5 10 G G copied _ h5]
  exact return_run core G _ (.value context) (by simp [G, F, bufferEnv, mlir_env, ha])

def resetState (s : GlobalState) (context : Pointer) : GlobalState :=
  {s with mem := countMemory s.mem context 0#64}

theorem buffer_fill_run (E : Env program.Γ) (s after : GlobalState) (context data : Pointer)
    (used size : Word) (h : CommonReady E context)
    (hd : E.read (%arg1) = .value data) (hs : E.read (%arg2) = .value size)
    (hu : E.read (%14) = .value used)
    (hc : SmallRange s.mem context 224) (hi : SmallRange s.mem data size.toNat)
    (hca : SmallRange after.mem context 224)
    (hub : used.toNat < 128) (hlong : (128#64 - used).toNat ≤ size.toNat)
    (hne : context.id ≠ data.id)
    (hcall : core (.cons (.value (context.add 128#64)) (.cons (.value context)
      (.cons (.value 1#64) .nil)))
      {s with mem := copyMemory s.mem (context.add used) data (128#64 - used)} =
        .value (.nil, after)) :
    ∃ F : Env program.Γ,
      CommonReady F context ∧
      F.read (%36) = .value (data.add (128#64 - used)) ∧
      F.read (%37) = .value (size - (128#64 - used)) ∧
      (program core).runFrom E 2 s = (program core).runFrom F 6 (resetState after context) := by
  have ha : E.args 0 = .value context := h.argContext
  let B := bufferEnv E context used size
  have hb := buffer_body E s context used size h hu hs hc hub
  change List.foldlM Instr.run E program.bb2.body s = .value (B, s) at hb
  have h2 : program.bb2.run program.blockParams E s = .value ((B, .inr 4), s) := by
    simp only [BasicBlock.run, EffectM.bind_eq, hb, PoisonOr.value_bind]
    have hb' : size.ult (128#64 - used) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    simp [program.bb2, B, bufferEnv, Exit.run, Jump.run, Regs.read_nil,
      Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect, hb']
  have hB : CommonReady B context := by
    constructor <;> simp [B, bufferEnv, mlir_env, ha, h.zero, h.full,
      h.one, h.shift, h.low, h.high, h.chain, h.count]
  have h4body := fill_body core B s after context data used size hB
    (by simpa [B, bufferEnv, mlir_env] using hd)
    (by simpa [B, bufferEnv, mlir_env] using hs)
    (by simp [B, bufferEnv, mlir_env]) (by simp [B, bufferEnv, mlir_env])
    hc hi hub hlong hne hcall
  let G := (filledEnv B data used size)[%33 := .value 0#64,
    %34 := .value (data.add (128#64 - used)), %35 := .value (size - (128#64 - used))]
  have h4 : (program.bb4 core).run program.blockParams B s = .value ((G, .inr 5), after) := by
    simp only [BasicBlock.run, EffectM.bind_eq, h4body, PoisonOr.value_bind]
    simp [program.bb4, G, filledEnv, B, bufferEnv, Exit.run, Jump.run,
      Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
      EffectM.pure_eq, mlir_env, mlir_effect, h.zero]
  let F := G[%36 := .value (data.add (128#64 - used)), %37 := .value (size - (128#64 - used))]
  have h5body := count_body G after context 0#64
    (by simpa [G, filledEnv, B, bufferEnv, mlir_env] using h.count)
    (by simp [G, mlir_env]) hca
  have h5 : program.bb5.run program.blockParams G after =
      .value ((F, .inr 6), resetState after context) := by
    simp only [BasicBlock.run, EffectM.bind_eq, h5body, PoisonOr.value_bind]
    have hb' : size.ult (128#64 - used) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    simp [program.bb5, F, G, filledEnv, B, bufferEnv, resetState, Exit.run, Jump.run,
      Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
      EffectM.pure_eq, mlir_env, mlir_effect, hb']
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp [F, G, filledEnv, B, bufferEnv, mlir_env, ha, h.zero, h.full,
      h.one, h.shift, h.low, h.high, h.chain, h.count]
  · simp [F, mlir_env]
  · simp [F, mlir_env]
  · rw [next_block core 2 4 E B s s h2, next_block core 4 5 B G s after h4,
      next_block core 5 6 G F after _ h5]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
