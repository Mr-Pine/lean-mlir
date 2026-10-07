import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CancellationWords

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def cancellationBlock0 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 272).take 7}

def cancellationEnv0 (E : Env program.Γ) (sum : BitVec 128) : Env program.Γ :=
  E[%223 := .value (sum.setWidth 64)][%224 := .value (sum.setWidth 64 * 1439961107955227#64)][%225 := .value (cancellationDigit sum)][%226 := .value ((cancellationDigit sum).setWidth 128)][%227 := .value ((cancellationDigit sum).setWidth 128 * 671914833335277#128)][%228 := .value ((cancellationDigit sum).setWidth 128 * 671914833335277#128 + sum)][%229 := .value (cancellationCarry sum)]

attribute [-simp] BitVec.msb_and BitVec.setWidth_and in
theorem cancellation_chunk0 (E : Env program.Γ) (s : GlobalState)
    (sum : BitVec 128) (hbound : sum.toNat < 2 ^ 120)
    (hsum : E.read (%178) = .value sum)
    (hfactor : E.read (%29) = .value 1439961107955227#64)
    (hmask : E.read (%23) = .value 4503599627370495#64)
    (horder : E.read (%30) = .value 671914833335277#128)
    (hshift : E.read (%31) = .value 52#128) :
    cancellationBlock0.runBodyFrom E 0 s = .value (cancellationEnv0 E sum, s) := by
  have hn := product_limb_nonneg (cancellationDigit sum) (cancellationDigit_bound sum)
  obtain ⟨hmu, hms, _⟩ := product_constant_flags (cancellationDigit sum)
    671914833335277#128 (cancellationDigit_bound sum) (by decide)
  obtain ⟨hau, has, _⟩ := product_add_flags
    ((cancellationDigit sum).setWidth 128 * 671914833335277#128) sum
    (cancellation_sum_bound sum hbound)
  dsimp only [cancellationDigit] at hn hmu hms hau has
  suffices ∀ (E' : Env program.Γ), E' = E →
      cancellationBlock0.runBodyFrom E' 0 s = .value (cancellationEnv0 E sum, s) by
    exact this E rfl
  intro E' hE
  step_pure [hsum, hfactor, hmask, horder, hshift]
  step_pure [hsum, hfactor, hmask, horder, hshift]
  step_pure [hsum, hfactor, hmask, horder, hshift]
  step_pure [hsum, hfactor, hmask, horder, hshift, hn]
  step_pure [hsum, hfactor, hmask, horder, hshift, hmu, hms]
  step_pure [hsum, hfactor, hmask, horder, hshift, hau, has]
  step_pure [hsum, hfactor, hmask, horder, hshift]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
