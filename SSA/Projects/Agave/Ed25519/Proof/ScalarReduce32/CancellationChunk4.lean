import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CancellationWords

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def cancellationBlock4 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 320).take 7}

def cancellationEnv4 (E : Env program.Γ) (sum : BitVec 128) : Env program.Γ :=
  E[%271 := .value (sum.setWidth 64)][%272 := .value (sum.setWidth 64 * 1439961107955227#64)][%273 := .value (cancellationDigit sum)][%274 := .value ((cancellationDigit sum).setWidth 128)][%275 := .value ((cancellationDigit sum).setWidth 128 * 671914833335277#128)][%276 := .value ((cancellationDigit sum).setWidth 128 * 671914833335277#128 + sum)][%277 := .value (cancellationCarry sum)]

attribute [-simp] BitVec.msb_and BitVec.setWidth_and in
theorem cancellation_chunk4 (E : Env program.Γ) (s : GlobalState)
    (sum : BitVec 128) (hbound : sum.toNat < 2 ^ 120)
    (hsum : E.read (%270) = .value sum)
    (hfactor : E.read (%29) = .value 1439961107955227#64)
    (hmask : E.read (%23) = .value 4503599627370495#64)
    (horder : E.read (%30) = .value 671914833335277#128)
    (hshift : E.read (%31) = .value 52#128) :
    cancellationBlock4.runBodyFrom E 0 s = .value (cancellationEnv4 E sum, s) := by
  have hn := product_limb_nonneg (cancellationDigit sum) (cancellationDigit_bound sum)
  obtain ⟨hmu, hms, _⟩ := product_constant_flags (cancellationDigit sum)
    671914833335277#128 (cancellationDigit_bound sum) (by decide)
  obtain ⟨hau, has, _⟩ := product_add_flags
    ((cancellationDigit sum).setWidth 128 * 671914833335277#128) sum
    (cancellation_sum_bound sum hbound)
  dsimp only [cancellationDigit] at hn hmu hms hau has
  suffices ∀ (E' : Env program.Γ), E' = E →
      cancellationBlock4.runBodyFrom E' 0 s = .value (cancellationEnv4 E sum, s) by
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
