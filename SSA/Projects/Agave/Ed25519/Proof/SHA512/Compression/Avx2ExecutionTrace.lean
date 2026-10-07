import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionTail

/-! Finite traces of actual RIR block executions. Each edge records the exact
resulting environment, successor block and global state. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR

/-- A finite sequence of successful block transitions, stopping before its
endpoint block executes. Return edges are handled by the endpoint continuation. -/
inductive ExecTrace (f : Func) : Nat → Env f.Γ → Fin f.n → GlobalState →
    Env f.Γ → Fin f.n → GlobalState → Prop
  | zero (E : Env f.Γ) (i : Fin f.n) (mem : GlobalState) :
      ExecTrace f 0 E i mem E i mem
  | step {n : Nat} {E E₁ E' : Env f.Γ} {i i₁ i' : Fin f.n}
      {mem mem₁ mem' : GlobalState}
      (edge : (f.blocks i).run f.blockParams E mem = .value ((E₁, .inr i₁), mem₁))
      (rest : ExecTrace f n E₁ i₁ mem₁ E' i' mem') :
      ExecTrace f (n + 1) E i mem E' i' mem'

/-- One exact block equation supplies a one-edge trace. -/
theorem ExecTrace.single {f : Func} {E E' : Env f.Γ} {i i' : Fin f.n}
    {mem mem' : GlobalState}
    (edge : (f.blocks i).run f.blockParams E mem = .value ((E', .inr i'), mem')) :
    ExecTrace f 1 E i mem E' i' mem' :=
  .step edge (.zero E' i' mem')

/-- Concatenate traces, preserving their exact block count. -/
theorem ExecTrace.trans {f : Func} {n m : Nat} {E₀ E₁ E₂ : Env f.Γ}
    {i₀ i₁ i₂ : Fin f.n} {mem₀ mem₁ mem₂ : GlobalState}
    (h₀ : ExecTrace f n E₀ i₀ mem₀ E₁ i₁ mem₁)
    (h₁ : ExecTrace f m E₁ i₁ mem₁ E₂ i₂ mem₂) :
    ExecTrace f (n + m) E₀ i₀ mem₀ E₂ i₂ mem₂ := by
  induction h₀ with
  | zero => simpa only [Nat.zero_add] using h₁
  | @step n E E₁ E' i i₁ i' mem mem₁ mem' edge rest ih =>
    simpa only [Nat.add_assoc, Nat.add_comm 1 m] using ExecTrace.step edge (ih h₁)

/-- A trace can precede any continuation at its final block. -/
theorem ExecTrace.runFrom {f : Func} {n : Nat} {E E' : Env f.Γ}
    {i i' : Fin f.n} {mem mem' : GlobalState}
    (h : ExecTrace f n E i mem E' i' mem') :
    f.runFrom E i mem = f.runFrom E' i' mem' := by
  induction h with
  | zero => rfl
  | step edge rest ih =>
    rw [Func.runFrom_eq, edge]
    exact ih

/-- Bounded evaluation consumes exactly one unit of fuel per recorded edge. -/
theorem ExecTrace.evalFrom {f : Func} {n : Nat} {E E' : Env f.Γ}
    {i i' : Fin f.n} {mem mem' : GlobalState}
    (h : ExecTrace f n E i mem E' i' mem') (fuel : Nat) :
    f.evalFrom (n + fuel) E i mem = f.evalFrom fuel E' i' mem' := by
  induction h with
  | zero => simp only [Nat.zero_add]
  | @step n E E₁ E' i i₁ i' mem mem₁ mem' edge rest ih =>
    rw [show n + 1 + fuel = (n + fuel) + 1 by omega]
    simp only [Func.evalFrom, EffectM.bind_eq, edge, PoisonOr.value_bind]
    exact ih

/-- The existing sixteen-round tail trace embeds into the generic trace. -/
theorem TailTrace.execTrace {mem : GlobalState} {n : Nat} {E E' : Env program.Γ}
    (h : TailTrace mem n E E') (g : Globals) :
    ExecTrace (program g) n E 6 mem E' 7 mem := by
  induction h with
  | last edge => exact ExecTrace.single edge
  | more edge rest ih => exact ExecTrace.step edge ih

end Agave.Ed25519.SHA512.Execution.Avx2
