import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Startup

/-! Exact call boundaries inside the wide-reduction basic block. These lemmas
execute the selected imported call instruction and continue at its real suffix.
Their primitive-call premise is local; it is not a wrapper correctness premise. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR

theorem low_montgomery_call (p : Primitives) (g : Globals)
    (E : Env program.Γ) (before after : GlobalState) (out lo r : Pointer)
    (hout : E.read (%73) = .value out)
    (hlo : E.read (%75) = .value lo)
    (hr : E.read (%39) = .value r)
    (hcall : p.montgomeryMul
      (.cons (.value out) (.cons (.value lo) (.cons (.value r) .nil))) before =
      .value (.nil, after)) :
    (program.entry p g).runBodyFrom E 320 before =
      (program.entry p g).runBodyFrom E 321 after := by
  apply BasicBlock.runBodyFrom_step_of_run (hpos := by change 320 < 607; decide)
  change (do
    let values ← p.montgomeryMul
      (.cons (E.read (%73)) (.cons (E.read (%75)) (.cons (E.read (%39)) .nil)))
    pure (E.writeMany .nil values)) before = .value (E, after)
  simp [hout, hlo, hr, hcall, Env.writeMany_nil]

theorem high_montgomery_call (p : Primitives) (g : Globals)
    (E : Env program.Γ) (before after : GlobalState) (out hi rr : Pointer)
    (hout : E.read (%72) = .value out)
    (hhi : E.read (%74) = .value hi)
    (hrr : E.read (%40) = .value rr)
    (hcall : p.montgomeryMul
      (.cons (.value out) (.cons (.value hi) (.cons (.value rr) .nil))) before =
      .value (.nil, after)) :
    (program.entry p g).runBodyFrom E 324 before =
      (program.entry p g).runBodyFrom E 325 after := by
  apply BasicBlock.runBodyFrom_step_of_run (hpos := by change 324 < 607; decide)
  change (do
    let values ← p.montgomeryMul
      (.cons (E.read (%72)) (.cons (E.read (%74)) (.cons (E.read (%40)) .nil)))
    pure (E.writeMany .nil values)) before = .value (E, after)
  simp [hout, hhi, hrr, hcall, Env.writeMany_nil]

theorem conditional_subtraction_black_box_call (p : Primitives) (g : Globals)
    (E : Env program.Γ) (before after : GlobalState) (byte : BitVec 8)
    (hbyte : E.read (%330) = .value byte)
    (hcall : p.blackBoxByte (.cons (.value byte) .nil) before =
      .value (.cons (.value byte) .nil, after)) :
    (program.entry p g).runBodyFrom E 376 before =
      (program.entry p g).runBodyFrom (E[%331 := .value byte]) 377 after := by
  apply BasicBlock.runBodyFrom_step_of_run (hpos := by change 376 < 607; decide)
  change (do
    let values ← p.blackBoxByte (.cons (E.read (%330)) .nil)
    pure (E.writeMany (.cons (%331) .nil) values)) before =
      .value (E[%331 := .value byte], after)
  simp [hbyte, hcall, Env.writeMany_cons, Env.writeMany_nil]

end Agave.Ed25519.Verifier.Execution.ScalarWide

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR

theorem conditional_subtraction_black_box_call (p : Primitives)
    (E : Env program.Γ) (before after : GlobalState) (byte : BitVec 8)
    (hbyte : E.read (%205) = .value byte)
    (hcall : p.blackBoxByte (.cons (.value byte) .nil) before =
      .value (.cons (.value byte) .nil, after)) :
    (program.entry p).runBodyFrom E 226 before =
      (program.entry p).runBodyFrom (E[%206 := .value byte]) 227 after := by
  apply BasicBlock.runBodyFrom_step_of_run (hpos := by change 226 < 286; decide)
  change (do
    let values ← p.blackBoxByte (.cons (E.read (%205)) .nil)
    pure (E.writeMany (.cons (%206) .nil) values)) before =
      .value (E[%206 := .value byte], after)
  simp [hbyte, hcall, Env.writeMany_cons, Env.writeMany_nil]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
