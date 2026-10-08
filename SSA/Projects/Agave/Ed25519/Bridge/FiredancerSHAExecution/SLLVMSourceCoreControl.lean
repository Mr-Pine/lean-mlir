import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreFirst
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreLater
import SSA.Projects.SLLVM.Cfg.Eval

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-- The actual outer-loop block starts the ring lifetime and enters round zero. -/
theorem outer_body
    (kp chain stack originalData data : Pointer) (originalCount count : Word)
    (original initial : State) (s : GlobalState)
    (k : HVector TyDenote.toType [] ⊕ SuccArgs core.cfgSigs → SLLVM.m α) :
    StateT.run (core.cfgBlock_0.denote
      (blockInput (outerTarget initial data count)
        (ambient kp chain stack originalData originalCount original)) >>= fun (_, jump) => k jump) s =
    StateT.run (k (.inr (firstTarget initial initial data count 0))) s := by
  dsimp only [blockInput, outerTarget]
  denote_expose
  peel_lifetime
  simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote, blockInput,
    outerTarget, firstTarget, ambient, HVector.reverse, HVector.reverseAux,
    simp_denote, simp_sllvm]

/-- The actual terminal block returns no values and performs no memory effect. -/
theorem done_body (V : Ctxt.Valuation core.cfgCtx) (s : GlobalState)
    (k : HVector TyDenote.toType [] ⊕ SuccArgs core.cfgSigs → SLLVM.m α) :
    StateT.run (core.cfgBlock_4.denote (blockInput doneTarget V) >>=
      fun (_, jump) => k jump) s = StateT.run (k (.inl .nil)) s := by
  denote_expose
  simp only [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]
  rfl

/-- One actual block-walk transition from the outer header. -/
theorem outer_run
    (kp chain stack originalData data : Pointer) (originalCount count : Word)
    (original initial : State) (s : GlobalState) :
    StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
      (outerTarget initial data count)) s =
    StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
      (firstTarget initial initial data count 0)) s := by
  rw [Blocks.run_step]
  exact outer_body kp chain stack originalData data originalCount count original initial s
    (fun jump => match jump with
      | .inl rets => pure rets
      | .inr next => core.cfgBlocks.run (ambient kp chain stack originalData originalCount original) next)

/-- The actual block walk terminates at the source's return block. -/
theorem done_run (V : Ctxt.Valuation core.cfgCtx) (s : GlobalState) :
    StateT.run (core.cfgBlocks.run V doneTarget) s = .value (.nil, s) := by
  rw [Blocks.run_step]
  exact done_body V s (fun jump => match jump with
    | .inl rets => pure rets
    | .inr next => core.cfgBlocks.run V next)

set_option allowUnsafeReducibility true
attribute [local irreducible] core.cfgBlock_1 core.cfgBlock_2 Blocks.run

/-- One actual block-walk transition through a first-sixteen-round body. -/
theorem first_run
    (kp chain stack originalData data : Pointer) (originalCount count : Word)
    (original initial work : State) (i : Nat) (native constant : Word)
    (s : GlobalState) (hi : i < 16)
    (hd : SmallRange s.mem data 128) (hs : SmallRange s.mem stack 128)
    (hk : SmallRange s.mem kp 640) (hne : stack.id ≠ kp.id)
    (hnative : readBits s.mem (data.withOffset (BitVec.ofNat 64 (8*i))) 64 = native)
    (hconstant : readBits s.mem (kp.withOffset (BitVec.ofNat 64 (8*i))) 64 = constant) :
    StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
      (firstTarget initial work data count i)) s =
    StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
      (firstNext initial work data count i native constant))
      {s with mem := firstMemory s.mem stack i native} := by
  unfold firstTarget
  rw [Blocks.run_step]
  dsimp only [core.cfgBlocks, Blocks.get]
  have h := first_body (α := HVector TyDenote.toType []) kp chain stack originalData data originalCount count original initial work
    i native constant s hi hd hs hk hne hnative hconstant
    (fun jump => match jump with
      | .inl rets => pure rets
      | .inr next => core.cfgBlocks.run (ambient kp chain stack originalData originalCount original) next)
  unfold blockInput firstTarget core.cfgBlocks at h
  convert h using 1
  congr 1
  congr 1
  funext ⟨_, jump⟩
  cases jump <;> rfl

/-- One actual block-walk transition through a circular-schedule round. -/
theorem later_run
    (kp chain stack originalData data : Pointer) (originalCount count : Word)
    (original initial work : State)
    (q : Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.Ring) (i : Nat)
    (constant : Word) (s : GlobalState) (hi : i < 80)
    (hs : SmallRange s.mem stack 128) (hk : SmallRange s.mem kp 640)
    (hne : stack.id ≠ kp.id)
    (hread : ∀ j, j < 16 → readBits s.mem
      (stack.withOffset (BitVec.ofNat 64 (8*j))) 64 = q j)
    (hconstant : readBits s.mem (kp.withOffset (BitVec.ofNat 64 (8*i))) 64 = constant) :
    StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
      (laterTarget initial work data count i)) s =
    StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
      (laterNext initial work data count q i constant))
      {s with mem := laterMemory s.mem stack q i} := by
  unfold laterTarget
  rw [Blocks.run_step]
  dsimp only [core.cfgBlocks, Blocks.get]
  have h := later_body (α := HVector TyDenote.toType []) kp chain stack originalData data originalCount count original initial work
    q i constant s hi hs hk hne hread hconstant
    (fun jump => match jump with
      | .inl rets => pure rets
      | .inr next => core.cfgBlocks.run (ambient kp chain stack originalData originalCount original) next)
  unfold blockInput laterTarget core.cfgBlocks at h
  convert h using 1
  congr 1
  congr 1
  funext ⟨_, jump⟩
  cases jump <;> rfl

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
