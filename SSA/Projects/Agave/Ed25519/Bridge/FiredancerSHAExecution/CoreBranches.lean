import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreFirst
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreLater

/-! Exact control-flow edges for the two scalar SHA-512 round loops. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

@[simp] theorem params2 : program.blockParams 2 =
    .cons (%54) (.cons (%55) (.cons (%56) (.cons (%57) (.cons (%58)
      (.cons (%59) (.cons (%60) (.cons (%61) (.cons (%62) .nil)))))))) := rfl
@[simp] theorem params3 : program.blockParams 3 =
    .cons (%97) (.cons (%98) (.cons (%99) (.cons (%100) (.cons (%101)
      (.cons (%102) (.cons (%103) (.cons (%104) (.cons (%105) .nil)))))))) := rfl
@[simp] theorem params4 : program.blockParams 4 = .nil := rfl

def firstNextEnv (E : Env program.Γ) (r : Nat) (s : State) : Env program.Γ :=
  E[%54 := .value s.a, %55 := .value s.b, %56 := .value s.c,
    %57 := .value s.d, %58 := .value s.e, %59 := .value s.f,
    %60 := .value (BitVec.ofNat 64 r), %61 := .value s.h, %62 := .value s.g]

def laterNextEnv (E : Env program.Γ) (r : Nat) (s : State) : Env program.Γ :=
  E[%97 := .value s.a, %98 := .value s.b, %99 := .value s.c,
    %100 := .value s.d, %101 := .value s.e, %102 := .value s.f,
    %103 := .value (BitVec.ofNat 64 r), %104 := .value s.h, %105 := .value s.g]

structure FinalReady (E : Env program.Γ) (s : State) : Prop where
  a : E.read (%160) = .value s.a
  b : E.read (%97) = .value s.b
  c : E.read (%98) = .value s.c
  d : E.read (%99) = .value s.d
  e : E.read (%159) = .value s.e
  f : E.read (%101) = .value s.f
  g : E.read (%102) = .value s.g
  h : E.read (%105) = .value s.h

theorem firstNext_ready (E : Env program.Γ) (r : Nat) (s : State) :
    FirstStateReady (firstNextEnv E r s) s := by
  constructor <;> simp [firstNextEnv, mlir_env]

theorem laterNext_ready (E : Env program.Γ) (r : Nat) (s : State) :
    LaterStateReady (laterNextEnv E r s) s := by
  constructor <;> simp [laterNextEnv, mlir_env]

theorem first_backedge (E : Env program.Γ) (state : GlobalState) (stack data kp : Pointer)
    (r : Nat) (s : State) (native constant : Word)
    (hstate : FirstStateReady E s) (hin : InputReady E stack data r) (hc : Constants E kp)
    (h16 : E.read (%2) = .value 16#64) (h1 : E.read (%18) = .value 1#64) (hr : r < 15)
    (hs : SmallRange state.mem stack 128) (hd : SmallRange state.mem data 128)
    (hk : SmallRange state.mem kp 640) (hne : stack.id ≠ kp.id)
    (hread : state.mem.readAt (data.add (BitVec.ofNat 64 (8 * r))) 64 = native)
    (hkread : state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * r))) 64 = constant) :
    program.bb2.run program.blockParams E state =
      .value ((firstNextEnv (firstBodyEnv E stack data kp r s native constant)
        (r + 1) (firstRound s (swapBytes native) constant), .inr 2),
        {state with mem := inputMemory state.mem stack r native}) := by
  have ht : (BitVec.ofNat 64 (r + 1) == 16#64) = false := by
    rw [first_exit_test r (by omega)]; simp [show r + 1 ≠ 16 by omega]
  simp only [BasicBlock.run, EffectM.bind_eq,
    first_body_full E state stack data kp r s native constant hstate hin hc h16 h1
      (by omega) hs hd hk hne hread hkread, PoisonOr.value_bind]
  simp [program.bb2, Exit.run, Jump.run, firstBodyEnv, firstNextEnv, firstEnv,
    inputEnv, firstRound, bigSigma0, bigSigma1, ht,
    hstate.a, hstate.b, hstate.c, hstate.e, hstate.f, hstate.g,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem first_exit (E : Env program.Γ) (state : GlobalState) (stack data kp : Pointer)
    (s : State) (native constant : Word)
    (hstate : FirstStateReady E s) (hin : InputReady E stack data 15) (hc : Constants E kp)
    (h16 : E.read (%2) = .value 16#64) (h1 : E.read (%18) = .value 1#64)
    (hs : SmallRange state.mem stack 128) (hd : SmallRange state.mem data 128)
    (hk : SmallRange state.mem kp 640) (hne : stack.id ≠ kp.id)
    (hread : state.mem.readAt (data.add 120#64) 64 = native)
    (hkread : state.mem.readAt (kp.add 120#64) 64 = constant) :
    program.bb2.run program.blockParams E state =
      .value ((laterNextEnv (firstBodyEnv E stack data kp 15 s native constant)
        16 (firstRound s (swapBytes native) constant), .inr 3),
        {state with mem := inputMemory state.mem stack 15 native}) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    first_body_full E state stack data kp 15 s native constant hstate hin hc h16 h1
      (by decide) hs hd hk hne hread hkread, PoisonOr.value_bind]
  simp [program.bb2, Exit.run, Jump.run, firstBodyEnv, laterNextEnv, firstEnv,
    inputEnv, firstRound, bigSigma0, bigSigma1, h16,
    hstate.a, hstate.b, hstate.c, hstate.e, hstate.f, hstate.g,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem later_backedge (E : Env program.Γ) (state : GlobalState) (stack kp : Pointer)
    (q : Ring) (r : Nat) (s : State) (constant : Word)
    (hstate : LaterStateReady E s) (hsc : ScheduleReady E stack r) (hc : Constants E kp)
    (h80 : E.read (%26) = .value 80#64) (hr : r < 79)
    (hs : SmallRange state.mem stack 128) (hk : SmallRange state.mem kp 640)
    (hne : stack.id ≠ kp.id)
    (hread : ∀ j, j < 16 → state.mem.readAt (stack.add (BitVec.ofNat 64 (8 * j))) 64 = q j)
    (hkread : state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * r))) 64 = constant) :
    program.bb3.run program.blockParams E state =
      .value ((laterNextEnv (laterBodyEnv E stack kp q r s constant)
        (r + 1) (laterRound s (ringWord q r) constant), .inr 3),
        {state with mem := scheduleMemory state.mem stack q r}) := by
  have ht : (BitVec.ofNat 64 (r + 1) == 80#64) = false := by
    rw [later_exit_test r (by omega)]; simp [show r + 1 ≠ 80 by omega]
  simp only [BasicBlock.run, EffectM.bind_eq,
    later_body_full E state stack kp q r s constant hstate hsc hc h80
      (by omega) hs hk hne hread hkread, PoisonOr.value_bind]
  simp [program.bb3, Exit.run, Jump.run, laterBodyEnv, laterNextEnv, laterEnv,
    scheduleEnv, laterRound, bigSigma0, bigSigma1, ht,
    hstate.a, hstate.b, hstate.c, hstate.e, hstate.f, hstate.g,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem later_exit (E : Env program.Γ) (state : GlobalState) (stack kp : Pointer)
    (q : Ring) (s : State) (constant : Word)
    (hstate : LaterStateReady E s) (hsc : ScheduleReady E stack 79) (hc : Constants E kp)
    (h80 : E.read (%26) = .value 80#64)
    (hs : SmallRange state.mem stack 128) (hk : SmallRange state.mem kp 640)
    (hne : stack.id ≠ kp.id)
    (hread : ∀ j, j < 16 → state.mem.readAt (stack.add (BitVec.ofNat 64 (8 * j))) 64 = q j)
    (hkread : state.mem.readAt (kp.add 632#64) 64 = constant) :
    program.bb3.run program.blockParams E state =
      .value ((laterBodyEnv E stack kp q 79 s constant, .inr 4),
        {state with mem := scheduleMemory state.mem stack q 79}) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    later_body_full E state stack kp q 79 s constant hstate hsc hc h80
      (by decide) hs hk hne hread hkread, PoisonOr.value_bind]
  simp [program.bb3, Exit.run, Jump.run, laterBodyEnv,
    Regs.read_nil, Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect]

theorem later_final_ready (E : Env program.Γ) (stack kp : Pointer) (q : Ring)
    (r : Nat) (s : State) (constant : Word) (h : LaterStateReady E s) :
    FinalReady (laterBodyEnv E stack kp q r s constant)
      (laterRound s (ringWord q r) constant) := by
  constructor <;> simp [laterBodyEnv, laterEnv, scheduleEnv, laterRound,
    bigSigma0, bigSigma1, mlir_env, h.a, h.b, h.c, h.e, h.f, h.g]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
