import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreOne
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreOuterMemory

/-! The imported multi-block backedge, including the pointer/count update and
all register facts needed to enter the next eighty-round compression. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem outer_more_test (n : Nat) (hn : 1 < n) (hb : n < 2^63) :
    (BitVec.ofNat 64 (n - 1) == 0#64) = false := by
  simp only [beq_iff_eq, Bool.eq_false_iff]
  intro he
  have heq : BitVec.ofNat 64 (n - 1) = 0#64 := by simpa using he
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hnat
  have hmod : (n - 1) % 2^64 = n - 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hnat
  norm_num at hnat
  omega

theorem feedforward_backedge (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (n : Nat) (initial final : State)
    (ho : OuterStateReady E initial) (hf : FinalReady E final)
    (hp : OuterPointersReady E chain data n)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hn : 1 < n) (hb : n < 2^63) :
    program.bb4.run program.blockParams E state =
      .value ((outerNextEnv (feedforwardEnv E (feedForward initial final) data n)
        (feedForward initial final) (data.add 128#64) (n - 1), .inr 1),
        {state with mem := feedforwardMemory state.mem chain (feedForward initial final)}) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    feedforward_body E state chain data n initial final ho hf hp hc hd (by omega) hb,
    PoisonOr.value_bind]
  simp [program.bb4, Exit.run, Jump.run, feedforwardEnv, outerNextEnv,
    outer_more_test n hn hb, Regs.read_cons, Regs.read_nil,
    Env.writeMany_cons, Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect]

theorem outer_next_pointers (E : Env program.Γ) (chain data : Pointer) (n : Nat)
    (s : State) (hp : OuterPointersReady E chain data n) :
    OuterPointersReady (outerNextEnv (feedforwardEnv E s data n) s (data.add 128#64) (n-1))
      chain (data.add 128#64) (n-1) := by
  rcases hp with ⟨h0,h8,h16,h24,h32,h40,h48,h56,hdata,hcount,hzero,hminus,hsize⟩
  have harg : E.args 0 = .value chain := h0
  constructor <;> simp_all [outerNextEnv, feedforwardEnv, mlir_env]

theorem outer_next_firstReady (E F : Env program.Γ) (stack data kp : Pointer)
    (r n : Nat) (old next : State) (hf : LoopFrame E F)
    (h : FirstLoopReady E stack data kp r old) :
    FirstLoopReady
      (firstNextEnv (outerNextEnv (feedforwardEnv F next data n)
        next (data.add 128#64) (n-1)) 0 next) stack (data.add 128#64) kp 0 next := by
  refine ⟨firstNext_ready _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.input.stack
    · simp [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env]
    · simp [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env]
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.input.zero
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.input.shift
  · constructor
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.constants.zero
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.constants.rot14
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.constants.rot18
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.constants.rot41
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.constants.notMask
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.constants.kp
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.constants.rot28
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.constants.rot34
    · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val _ (by decide) rfl).trans h.constants.rot39
  · constructor
    · simp [laterNextEnv, mlir_env]
    · have hh := h.futureSchedule.stack
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 28 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c7
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 7 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c8
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 8 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c9
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 9 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c18
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 18 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c19
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 19 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c20
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 20 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c21
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 21 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c22
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 22 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c23
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 23 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c24
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 24 (by decide) rfl).trans hh
    · have hh := h.futureSchedule.c25
      simp only [laterNextEnv, mlir_env] at hh
      simpa [laterNextEnv, firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
        (hf.read_val 25 (by decide) rfl).trans hh
  · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
      (hf.read_val _ (by decide) rfl).trans h.limit16
  · simpa [firstNextEnv, outerNextEnv, feedforwardEnv, mlir_env] using
      (hf.read_val _ (by decide) rfl).trans h.limit80

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
