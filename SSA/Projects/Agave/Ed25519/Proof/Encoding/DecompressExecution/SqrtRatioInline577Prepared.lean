import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline117Circuit
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Maps
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Constants

/-! The renaming's prepared-environment conditions follow from the explicit
constants and the five exact loads, rather than an execution premise. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
open LeanMLIR.RIR SerialFieldMul SerializerRename
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000

theorem first_prepared (E : Env program.Γ) (x : Words)
    (hc : Constants E) :
    prepared (firstRenaming.project (firstLoadEnv E x)) x =
      firstRenaming.project (firstLoadEnv E x) := by
  have h0 : (firstRenaming.project (firstLoadEnv E x)).read (%0) = .value 8#64 := by
    change (firstLoadEnv E x).read (%3) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c3
  have h1 : (firstRenaming.project (firstLoadEnv E x)).read (%1) = .value 16#64 := by
    change (firstLoadEnv E x).read (%4) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c4
  have h2 : (firstRenaming.project (firstLoadEnv E x)).read (%2) = .value 24#64 := by
    change (firstLoadEnv E x).read (%5) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c5
  have h3 : (firstRenaming.project (firstLoadEnv E x)).read (%3) = .value 32#64 := by
    change (firstLoadEnv E x).read (%6) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c6
  have h4 : (firstRenaming.project (firstLoadEnv E x)).read (%4) = .value 51#64 := by
    change (firstLoadEnv E x).read (%7) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c7
  have h5 : (firstRenaming.project (firstLoadEnv E x)).read (%5) = .value 2251799813685247#64 := by
    change (firstLoadEnv E x).read (%8) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c8
  have h6 : (firstRenaming.project (firstLoadEnv E x)).read (%6) = .value 19#64 := by
    change (firstLoadEnv E x).read (%9) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c9
  have h7 : (firstRenaming.project (firstLoadEnv E x)).read (%7) = .value 1#64 := by
    change (firstLoadEnv E x).read (%10) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c10
  have h8 : (firstRenaming.project (firstLoadEnv E x)).read (%8) = .value 2#64 := by
    change (firstLoadEnv E x).read (%11) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c11
  have h9 : (firstRenaming.project (firstLoadEnv E x)).read (%9) = .value 3#64 := by
    change (firstLoadEnv E x).read (%12) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c12
  have h10 : (firstRenaming.project (firstLoadEnv E x)).read (%10) = .value 4#64 := by
    change (firstLoadEnv E x).read (%13) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c13
  have h11 : (firstRenaming.project (firstLoadEnv E x)).read (%11) = .value 40#64 := by
    change (firstLoadEnv E x).read (%1) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c1
  have h12 : (firstRenaming.project (firstLoadEnv E x)).read (%12) = .value 5#64 := by
    change (firstLoadEnv E x).read (%14) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c14
  have h13 : (firstRenaming.project (firstLoadEnv E x)).read (%13) = .value 48#64 := by
    change (firstLoadEnv E x).read (%15) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c15
  have h14 : (firstRenaming.project (firstLoadEnv E x)).read (%14) = .value 7#64 := by
    change (firstLoadEnv E x).read (%16) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c16
  have h15 : (firstRenaming.project (firstLoadEnv E x)).read (%15) = .value 6#64 := by
    change (firstLoadEnv E x).read (%17) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c17
  have h16 : (firstRenaming.project (firstLoadEnv E x)).read (%16) = .value 13#64 := by
    change (firstLoadEnv E x).read (%18) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c18
  have h17 : (firstRenaming.project (firstLoadEnv E x)).read (%17) = .value 21#64 := by
    change (firstLoadEnv E x).read (%19) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c19
  have h18 : (firstRenaming.project (firstLoadEnv E x)).read (%18) = .value 9#64 := by
    change (firstLoadEnv E x).read (%20) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c20
  have h19 : (firstRenaming.project (firstLoadEnv E x)).read (%19) = .value 29#64 := by
    change (firstLoadEnv E x).read (%21) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c21
  have h20 : (firstRenaming.project (firstLoadEnv E x)).read (%20) = .value 10#64 := by
    change (firstLoadEnv E x).read (%22) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c22
  have h21 : (firstRenaming.project (firstLoadEnv E x)).read (%21) = .value 37#64 := by
    change (firstLoadEnv E x).read (%23) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c23
  have h22 : (firstRenaming.project (firstLoadEnv E x)).read (%22) = .value 11#64 := by
    change (firstLoadEnv E x).read (%24) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c24
  have h23 : (firstRenaming.project (firstLoadEnv E x)).read (%23) = .value 45#64 := by
    change (firstLoadEnv E x).read (%25) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c25
  have h24 : (firstRenaming.project (firstLoadEnv E x)).read (%24) = .value 12#64 := by
    change (firstLoadEnv E x).read (%26) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c26
  have h25 : (firstRenaming.project (firstLoadEnv E x)).read (%25) = .value 14#64 := by
    change (firstLoadEnv E x).read (%27) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c27
  have h26 : (firstRenaming.project (firstLoadEnv E x)).read (%26) = .value 18#64 := by
    change (firstLoadEnv E x).read (%28) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c28
  have h27 : (firstRenaming.project (firstLoadEnv E x)).read (%27) = .value 15#64 := by
    change (firstLoadEnv E x).read (%29) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c29
  have h28 : (firstRenaming.project (firstLoadEnv E x)).read (%28) = .value 26#64 := by
    change (firstLoadEnv E x).read (%30) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c30
  have h29 : (firstRenaming.project (firstLoadEnv E x)).read (%29) = .value 34#64 := by
    change (firstLoadEnv E x).read (%31) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c31
  have h30 : (firstRenaming.project (firstLoadEnv E x)).read (%30) = .value 17#64 := by
    change (firstLoadEnv E x).read (%32) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c32
  have h31 : (firstRenaming.project (firstLoadEnv E x)).read (%31) = .value 42#64 := by
    change (firstLoadEnv E x).read (%33) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c33
  have h32 : (firstRenaming.project (firstLoadEnv E x)).read (%32) = .value 50#64 := by
    change (firstLoadEnv E x).read (%34) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c34
  have h33 : (firstRenaming.project (firstLoadEnv E x)).read (%33) = .value 20#64 := by
    change (firstLoadEnv E x).read (%35) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c35
  have h34 : (firstRenaming.project (firstLoadEnv E x)).read (%34) = .value 23#64 := by
    change (firstLoadEnv E x).read (%36) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c36
  have h35 : (firstRenaming.project (firstLoadEnv E x)).read (%35) = .value 22#64 := by
    change (firstLoadEnv E x).read (%37) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c37
  have h36 : (firstRenaming.project (firstLoadEnv E x)).read (%36) = .value 31#64 := by
    change (firstLoadEnv E x).read (%38) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c38
  have h37 : (firstRenaming.project (firstLoadEnv E x)).read (%37) = .value 39#64 := by
    change (firstLoadEnv E x).read (%39) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c39
  have h38 : (firstRenaming.project (firstLoadEnv E x)).read (%38) = .value 47#64 := by
    change (firstLoadEnv E x).read (%40) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c40
  have h39 : (firstRenaming.project (firstLoadEnv E x)).read (%39) = .value 25#64 := by
    change (firstLoadEnv E x).read (%41) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c41
  have h40 : (firstRenaming.project (firstLoadEnv E x)).read (%40) = .value 27#64 := by
    change (firstLoadEnv E x).read (%42) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c42
  have h41 : (firstRenaming.project (firstLoadEnv E x)).read (%41) = .value 28#64 := by
    change (firstLoadEnv E x).read (%43) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c43
  have h42 : (firstRenaming.project (firstLoadEnv E x)).read (%42) = .value 36#64 := by
    change (firstLoadEnv E x).read (%44) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c44
  have h43 : (firstRenaming.project (firstLoadEnv E x)).read (%43) = .value 30#64 := by
    change (firstLoadEnv E x).read (%45) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c45
  have h44 : (firstRenaming.project (firstLoadEnv E x)).read (%44) = .value 44#64 := by
    change (firstLoadEnv E x).read (%46) = _
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hc.c46
  have h45 : (firstRenaming.project (firstLoadEnv E x)).read (%45) = .value (x 0) := by
    change (firstLoadEnv E x).read (%431) = _
    simp (disch := decide) only [firstLoadEnv,mlir_env]
  have h47 : (firstRenaming.project (firstLoadEnv E x)).read (%47) = .value (x 1) := by
    change (firstLoadEnv E x).read (%432) = _
    simp (disch := decide) only [firstLoadEnv,mlir_env]
  have h49 : (firstRenaming.project (firstLoadEnv E x)).read (%49) = .value (x 2) := by
    change (firstLoadEnv E x).read (%433) = _
    simp (disch := decide) only [firstLoadEnv,mlir_env]
  have h51 : (firstRenaming.project (firstLoadEnv E x)).read (%51) = .value (x 3) := by
    change (firstLoadEnv E x).read (%434) = _
    simp (disch := decide) only [firstLoadEnv,mlir_env]
  have h53 : (firstRenaming.project (firstLoadEnv E x)).read (%53) = .value (x 4) := by
    change (firstLoadEnv E x).read (%435) = _
    simp (disch := decide) only [firstLoadEnv,mlir_env]
  unfold prepared
  rw [
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%0) h0,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%1) h1,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%2) h2,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%3) h3,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%4) h4,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%5) h5,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%6) h6,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%7) h7,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%8) h8,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%9) h9,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%10) h10,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%11) h11,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%12) h12,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%13) h13,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%14) h14,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%15) h15,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%16) h16,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%17) h17,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%18) h18,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%19) h19,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%20) h20,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%21) h21,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%22) h22,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%23) h23,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%24) h24,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%25) h25,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%26) h26,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%27) h27,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%28) h28,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%29) h29,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%30) h30,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%31) h31,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%32) h32,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%33) h33,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%34) h34,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%35) h35,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%36) h36,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%37) h37,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%38) h38,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%39) h39,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%40) h40,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%41) h41,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%42) h42,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%43) h43,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%44) h44,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%45) h45,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%47) h47,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%49) h49,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%51) h51,
    Env.write_of_read (firstRenaming.project (firstLoadEnv E x)) (%53) h53]

theorem first_source_args (E : Env program.Γ) (x : Words) (r b : Pointer)
    (hr : E.read (%63) = .value r) (hb : E.read (%75) = .value b) :
    (firstRenaming.project (firstLoadEnv E x)).args =
      (ToBytes.program.args (.value r) (.value b)).get := by
  funext i
  fin_cases i
  · change (firstLoadEnv E x).read (%63) = .value r
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hr
  · change (firstLoadEnv E x).read (%75) = .value b
    simpa (disch := decide) only [firstLoadEnv,mlir_env] using hb

theorem second_prepared (E : Env program.Γ) (a : Pointer) (x : Words)
    (hc : Constants E) :
    prepared (secondRenaming.project (secondLoadEnv E a x)) x =
      secondRenaming.project (secondLoadEnv E a x) := by
  have h0 : (secondRenaming.project (secondLoadEnv E a x)).read (%0) = .value 8#64 := by
    change (secondLoadEnv E a x).read (%3) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c3
  have h1 : (secondRenaming.project (secondLoadEnv E a x)).read (%1) = .value 16#64 := by
    change (secondLoadEnv E a x).read (%4) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c4
  have h2 : (secondRenaming.project (secondLoadEnv E a x)).read (%2) = .value 24#64 := by
    change (secondLoadEnv E a x).read (%5) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c5
  have h3 : (secondRenaming.project (secondLoadEnv E a x)).read (%3) = .value 32#64 := by
    change (secondLoadEnv E a x).read (%6) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c6
  have h4 : (secondRenaming.project (secondLoadEnv E a x)).read (%4) = .value 51#64 := by
    change (secondLoadEnv E a x).read (%7) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c7
  have h5 : (secondRenaming.project (secondLoadEnv E a x)).read (%5) = .value 2251799813685247#64 := by
    change (secondLoadEnv E a x).read (%8) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c8
  have h6 : (secondRenaming.project (secondLoadEnv E a x)).read (%6) = .value 19#64 := by
    change (secondLoadEnv E a x).read (%9) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c9
  have h7 : (secondRenaming.project (secondLoadEnv E a x)).read (%7) = .value 1#64 := by
    change (secondLoadEnv E a x).read (%10) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c10
  have h8 : (secondRenaming.project (secondLoadEnv E a x)).read (%8) = .value 2#64 := by
    change (secondLoadEnv E a x).read (%11) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c11
  have h9 : (secondRenaming.project (secondLoadEnv E a x)).read (%9) = .value 3#64 := by
    change (secondLoadEnv E a x).read (%12) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c12
  have h10 : (secondRenaming.project (secondLoadEnv E a x)).read (%10) = .value 4#64 := by
    change (secondLoadEnv E a x).read (%13) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c13
  have h11 : (secondRenaming.project (secondLoadEnv E a x)).read (%11) = .value 40#64 := by
    change (secondLoadEnv E a x).read (%1) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c1
  have h12 : (secondRenaming.project (secondLoadEnv E a x)).read (%12) = .value 5#64 := by
    change (secondLoadEnv E a x).read (%14) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c14
  have h13 : (secondRenaming.project (secondLoadEnv E a x)).read (%13) = .value 48#64 := by
    change (secondLoadEnv E a x).read (%15) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c15
  have h14 : (secondRenaming.project (secondLoadEnv E a x)).read (%14) = .value 7#64 := by
    change (secondLoadEnv E a x).read (%16) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c16
  have h15 : (secondRenaming.project (secondLoadEnv E a x)).read (%15) = .value 6#64 := by
    change (secondLoadEnv E a x).read (%17) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c17
  have h16 : (secondRenaming.project (secondLoadEnv E a x)).read (%16) = .value 13#64 := by
    change (secondLoadEnv E a x).read (%18) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c18
  have h17 : (secondRenaming.project (secondLoadEnv E a x)).read (%17) = .value 21#64 := by
    change (secondLoadEnv E a x).read (%19) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c19
  have h18 : (secondRenaming.project (secondLoadEnv E a x)).read (%18) = .value 9#64 := by
    change (secondLoadEnv E a x).read (%20) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c20
  have h19 : (secondRenaming.project (secondLoadEnv E a x)).read (%19) = .value 29#64 := by
    change (secondLoadEnv E a x).read (%21) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c21
  have h20 : (secondRenaming.project (secondLoadEnv E a x)).read (%20) = .value 10#64 := by
    change (secondLoadEnv E a x).read (%22) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c22
  have h21 : (secondRenaming.project (secondLoadEnv E a x)).read (%21) = .value 37#64 := by
    change (secondLoadEnv E a x).read (%23) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c23
  have h22 : (secondRenaming.project (secondLoadEnv E a x)).read (%22) = .value 11#64 := by
    change (secondLoadEnv E a x).read (%24) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c24
  have h23 : (secondRenaming.project (secondLoadEnv E a x)).read (%23) = .value 45#64 := by
    change (secondLoadEnv E a x).read (%25) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c25
  have h24 : (secondRenaming.project (secondLoadEnv E a x)).read (%24) = .value 12#64 := by
    change (secondLoadEnv E a x).read (%26) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c26
  have h25 : (secondRenaming.project (secondLoadEnv E a x)).read (%25) = .value 14#64 := by
    change (secondLoadEnv E a x).read (%27) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c27
  have h26 : (secondRenaming.project (secondLoadEnv E a x)).read (%26) = .value 18#64 := by
    change (secondLoadEnv E a x).read (%28) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c28
  have h27 : (secondRenaming.project (secondLoadEnv E a x)).read (%27) = .value 15#64 := by
    change (secondLoadEnv E a x).read (%29) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c29
  have h28 : (secondRenaming.project (secondLoadEnv E a x)).read (%28) = .value 26#64 := by
    change (secondLoadEnv E a x).read (%30) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c30
  have h29 : (secondRenaming.project (secondLoadEnv E a x)).read (%29) = .value 34#64 := by
    change (secondLoadEnv E a x).read (%31) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c31
  have h30 : (secondRenaming.project (secondLoadEnv E a x)).read (%30) = .value 17#64 := by
    change (secondLoadEnv E a x).read (%32) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c32
  have h31 : (secondRenaming.project (secondLoadEnv E a x)).read (%31) = .value 42#64 := by
    change (secondLoadEnv E a x).read (%33) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c33
  have h32 : (secondRenaming.project (secondLoadEnv E a x)).read (%32) = .value 50#64 := by
    change (secondLoadEnv E a x).read (%34) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c34
  have h33 : (secondRenaming.project (secondLoadEnv E a x)).read (%33) = .value 20#64 := by
    change (secondLoadEnv E a x).read (%35) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c35
  have h34 : (secondRenaming.project (secondLoadEnv E a x)).read (%34) = .value 23#64 := by
    change (secondLoadEnv E a x).read (%36) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c36
  have h35 : (secondRenaming.project (secondLoadEnv E a x)).read (%35) = .value 22#64 := by
    change (secondLoadEnv E a x).read (%37) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c37
  have h36 : (secondRenaming.project (secondLoadEnv E a x)).read (%36) = .value 31#64 := by
    change (secondLoadEnv E a x).read (%38) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c38
  have h37 : (secondRenaming.project (secondLoadEnv E a x)).read (%37) = .value 39#64 := by
    change (secondLoadEnv E a x).read (%39) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c39
  have h38 : (secondRenaming.project (secondLoadEnv E a x)).read (%38) = .value 47#64 := by
    change (secondLoadEnv E a x).read (%40) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c40
  have h39 : (secondRenaming.project (secondLoadEnv E a x)).read (%39) = .value 25#64 := by
    change (secondLoadEnv E a x).read (%41) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c41
  have h40 : (secondRenaming.project (secondLoadEnv E a x)).read (%40) = .value 27#64 := by
    change (secondLoadEnv E a x).read (%42) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c42
  have h41 : (secondRenaming.project (secondLoadEnv E a x)).read (%41) = .value 28#64 := by
    change (secondLoadEnv E a x).read (%43) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c43
  have h42 : (secondRenaming.project (secondLoadEnv E a x)).read (%42) = .value 36#64 := by
    change (secondLoadEnv E a x).read (%44) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c44
  have h43 : (secondRenaming.project (secondLoadEnv E a x)).read (%43) = .value 30#64 := by
    change (secondLoadEnv E a x).read (%45) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c45
  have h44 : (secondRenaming.project (secondLoadEnv E a x)).read (%44) = .value 44#64 := by
    change (secondLoadEnv E a x).read (%46) = _
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hc.c46
  have h45 : (secondRenaming.project (secondLoadEnv E a x)).read (%45) = .value (x 0) := by
    change (secondLoadEnv E a x).read (%579) = _
    simp (disch := decide) only [secondLoadEnv,mlir_env]
  have h47 : (secondRenaming.project (secondLoadEnv E a x)).read (%47) = .value (x 1) := by
    change (secondLoadEnv E a x).read (%581) = _
    simp (disch := decide) only [secondLoadEnv,mlir_env]
  have h49 : (secondRenaming.project (secondLoadEnv E a x)).read (%49) = .value (x 2) := by
    change (secondLoadEnv E a x).read (%583) = _
    simp (disch := decide) only [secondLoadEnv,mlir_env]
  have h51 : (secondRenaming.project (secondLoadEnv E a x)).read (%51) = .value (x 3) := by
    change (secondLoadEnv E a x).read (%585) = _
    simp (disch := decide) only [secondLoadEnv,mlir_env]
  have h53 : (secondRenaming.project (secondLoadEnv E a x)).read (%53) = .value (x 4) := by
    change (secondLoadEnv E a x).read (%587) = _
    simp (disch := decide) only [secondLoadEnv,mlir_env]
  unfold prepared
  rw [
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%0) h0,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%1) h1,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%2) h2,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%3) h3,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%4) h4,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%5) h5,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%6) h6,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%7) h7,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%8) h8,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%9) h9,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%10) h10,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%11) h11,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%12) h12,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%13) h13,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%14) h14,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%15) h15,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%16) h16,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%17) h17,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%18) h18,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%19) h19,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%20) h20,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%21) h21,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%22) h22,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%23) h23,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%24) h24,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%25) h25,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%26) h26,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%27) h27,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%28) h28,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%29) h29,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%30) h30,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%31) h31,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%32) h32,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%33) h33,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%34) h34,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%35) h35,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%36) h36,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%37) h37,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%38) h38,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%39) h39,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%40) h40,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%41) h41,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%42) h42,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%43) h43,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%44) h44,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%45) h45,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%47) h47,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%49) h49,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%51) h51,
    Env.write_of_read (secondRenaming.project (secondLoadEnv E a x)) (%53) h53]

theorem second_source_args (E : Env program.Γ) (a : Pointer) (x : Words) (r b : Pointer)
    (hr : E.read (%62) = .value r) (hb : E.read (%73) = .value b) :
    (secondRenaming.project (secondLoadEnv E a x)).args =
      (ToBytes.program.args (.value r) (.value b)).get := by
  funext i
  fin_cases i
  · change (secondLoadEnv E a x).read (%62) = .value r
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hr
  · change (secondLoadEnv E a x).read (%73) = .value b
    simpa (disch := decide) only [secondLoadEnv,mlir_env] using hb

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
