import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreFeedforward
import SSA.Projects.SLLVM.Cfg.Eval

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option allowUnsafeReducibility true in
attribute [local irreducible] core.cfgBlock_3 Blocks.run BlockCom.denote



/-- One actual block-walk transition through the imported feedforward body. -/
theorem feedforward_run
    (kp chain stack originalData data : Pointer) (originalCount count : Word)
    (original initial work : State) (before : GlobalState)
    (hc : SmallRange before.mem chain 64)
    (hn : 0 < count.toNat) (hb : count.toNat < 2^63) :
    StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
      (feedforwardTarget initial work data count)) before =
    StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
      (if count = 1#64 then doneTarget else
        outerTarget (feedForward initial work) (data.withOffset 128#64) (count - 1#64)))
      {before with mem := feedforwardMemory before.mem chain (feedForward initial work)} := by
  rw [Blocks.run_step]
  dsimp +instances only [feedforwardTarget, core.cfgBlocks, Blocks.get]
  have h := feedforward_step (α := HVector TyDenote.toType [])
    kp chain stack originalData data originalCount count original initial work before hc hn hb
    (fun jump => match jump with
      | .inl rets => pure rets
      | .inr next => core.cfgBlocks.run (ambient kp chain stack originalData originalCount original) next)
  dsimp +instances only [blockInput, feedforwardTarget, core.cfgBlocks] at h
  convert h using 1
  congr 1
  congr 1
  funext ⟨_, jump⟩
  cases jump <;> rfl

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
