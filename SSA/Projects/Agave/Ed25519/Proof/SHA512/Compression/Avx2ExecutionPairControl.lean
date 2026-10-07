import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairStore
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairSecond

/-! The exact bb5 terminator and its simultaneous backedge parameter map. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

@[simp] theorem pair_params3 : program.blockParams 3 = .nil := rfl
@[simp] theorem pair_params5 : program.blockParams 5 =
    .cons (%173) (.cons (%174) (.cons (%175) (.cons (%176) (.cons (%177)
      (.cons (%178) (.cons (%179) (.cons (%180) (.cons (%181) (.cons (%182)
      (.cons (%183) (.cons (%184) (.cons (%185) (.cons (%186) (.cons (%187)
      (.cons (%188) (.cons (%189) (.cons (%190) .nil))))))))))))))))) := rfl

def pairNextEnv (E : Env program.Γ) : Env program.Γ :=
  E[%173 := E.read (%270), %174 := E.read (%191),
    %175 := E.read (%180), %176 := E.read (%175),
    %177 := E.read (%182), %178 := E.read (%177),
    %179 := E.read (%216), %180 := E.read (%181),
    %181 := E.read (%178), %182 := E.read (%179),
    %183 := E.read (%186), %184 := E.read (%268),
    %185 := E.read (%184), %186 := E.read (%243),
    %187 := E.read (%267), %188 := E.read (%242),
    %189 := E.read (%187), %190 := E.read (%188)]

theorem pair_terminator_backedge (E : Env program.Γ) (mem : GlobalState)
    (h : E.read (%271) = .value 0#1) :
    program.bb5.exit.run program.blockParams E mem =
      .value ((pairNextEnv E, .inr 5), mem) := by
  simp [program.bb5, Exit.run, Jump.run, h, pairNextEnv,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem pair_terminator_exit (E : Env program.Γ) (mem : GlobalState)
    (h : E.read (%271) = .value 1#1) :
    program.bb5.exit.run program.blockParams E mem =
      .value ((E, .inr 3), mem) := by
  simp [program.bb5, Exit.run, Jump.run, h,
    Regs.read_nil, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

/-- The scalar permutation is the state produced by the two scalar rounds. -/
theorem pairNextEnv_scalar (E : Env program.Γ) (s : Spec.State)
    (h : PairSecondFinalReady E s) :
    (pairNextEnv E).read (%187) = .value s.a ∧
    (pairNextEnv E).read (%188) = .value s.b ∧
    (pairNextEnv E).read (%189) = .value s.c ∧
    (pairNextEnv E).read (%190) = .value s.d ∧
    (pairNextEnv E).read (%184) = .value s.e ∧
    (pairNextEnv E).read (%186) = .value s.f ∧
    (pairNextEnv E).read (%185) = .value s.g ∧
    (pairNextEnv E).read (%183) = .value s.h := by
  simp [pairNextEnv, mlir_env, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h]

/-- The vector permutation moves the sixteen-word window forward by two. -/
theorem pairNextEnv_window (E : Env program.Γ) (q : Window)
    (h : PairWindowReady E q)
    (hnew : E.read (%216) = pairVec (avxWindowPair q).1 (avxWindowPair q).2) :
    PairWindowReady (pairNextEnv E) (avxWindowStep q) := by
  constructor <;> simp [pairNextEnv, avxWindowStep, mlir_env,
    h.p1, h.p2, h.p3, h.p4, h.p5, h.p6, h.p7, hnew]

end Agave.Ed25519.SHA512.Execution.Avx2
