import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorConstants

/-! Readback of every setup register consumed by the constructor body.
Each literal is checked by reduction of the actual constant instruction results. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Constants
open LeanMLIR.RIR
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem read_0 (E : ⟪kernel.Γ⟫) :
    (result E).read (%0) = .value 1#32 := by rfl

theorem read_1 (E : ⟪kernel.Γ⟫) :
    (result E).read (%1) = .value 8#64 := by rfl

theorem read_2 (E : ⟪kernel.Γ⟫) :
    (result E).read (%2) = .value 16#64 := by rfl

theorem read_3 (E : ⟪kernel.Γ⟫) :
    (result E).read (%3) = .value 24#64 := by rfl

theorem read_4 (E : ⟪kernel.Γ⟫) :
    (result E).read (%4) = .value 32#64 := by rfl

theorem read_5 (E : ⟪kernel.Γ⟫) :
    (result E).read (%5) = .value 40#64 := by rfl

theorem read_6 (E : ⟪kernel.Γ⟫) :
    (result E).read (%6) = .value 48#64 := by rfl

theorem read_7 (E : ⟪kernel.Γ⟫) :
    (result E).read (%7) = .value 56#64 := by rfl

theorem read_8 (E : ⟪kernel.Γ⟫) :
    (result E).read (%8) = .value 64#64 := by rfl

theorem read_9 (E : ⟪kernel.Γ⟫) :
    (result E).read (%9) = .value 72#64 := by rfl

theorem read_10 (E : ⟪kernel.Γ⟫) :
    (result E).read (%10) = .value 80#64 := by rfl

theorem read_11 (E : ⟪kernel.Γ⟫) :
    (result E).read (%11) = .value 88#64 := by rfl

theorem read_12 (E : ⟪kernel.Γ⟫) :
    (result E).read (%12) = .value 96#64 := by rfl

theorem read_13 (E : ⟪kernel.Γ⟫) :
    (result E).read (%13) = .value 104#64 := by rfl

theorem read_14 (E : ⟪kernel.Γ⟫) :
    (result E).read (%14) = .value 112#64 := by rfl

theorem read_15 (E : ⟪kernel.Γ⟫) :
    (result E).read (%15) = .value 120#64 := by rfl

theorem read_16 (E : ⟪kernel.Γ⟫) :
    (result E).read (%16) = .value 128#64 := by rfl

theorem read_17 (E : ⟪kernel.Γ⟫) :
    (result E).read (%17) = .value 136#64 := by rfl

theorem read_18 (E : ⟪kernel.Γ⟫) :
    (result E).read (%18) = .value 144#64 := by rfl

theorem read_19 (E : ⟪kernel.Γ⟫) :
    (result E).read (%19) = .value 152#64 := by rfl

theorem read_20 (E : ⟪kernel.Γ⟫) :
    (result E).read (%20) = #v[.poison, .poison, .poison, .poison] := by rfl

theorem read_21 (E : ⟪kernel.Γ⟫) :
    (result E).read (%21) = .value 0#64 := by rfl

theorem read_22 (E : ⟪kernel.Γ⟫) :
    (result E).read (%22) = .value 1#64 := by rfl

theorem read_23 (E : ⟪kernel.Γ⟫) :
    (result E).read (%23) = .value 2#64 := by rfl

theorem read_24 (E : ⟪kernel.Γ⟫) :
    (result E).read (%24) = .value 3#64 := by rfl

theorem read_25 (E : ⟪kernel.Γ⟫) :
    (result E).read (%25) = #v[.value 67108863#32, .value 67108863#32, .value 67108863#32, .value 67108863#32] := by rfl

theorem read_26 (E : ⟪kernel.Γ⟫) :
    (result E).read (%26) = #v[.poison, .poison, .poison, .poison] := by rfl

theorem read_27 (E : ⟪kernel.Γ⟫) :
    (result E).read (%27) = #v[.value 26#64, .value 26#64, .value 26#64, .value 26#64] := by rfl

theorem read_28 (E : ⟪kernel.Γ⟫) :
    (result E).read (%28) = #v[.value 26#32, .value 26#32, .value 25#32, .value 25#32, .value 26#32, .value 26#32, .value 25#32, .value 25#32] := by rfl

theorem read_29 (E : ⟪kernel.Γ⟫) :
    (result E).read (%29) = #v[.value 67108863#32, .value 67108863#32, .value 33554431#32, .value 33554431#32, .value 67108863#32, .value 67108863#32, .value 33554431#32, .value 33554431#32] := by rfl

theorem read_30 (E : ⟪kernel.Γ⟫) :
    (result E).read (%30) = #v[.value 0#32, .value 0#32, .value 127#32, .value 127#32, .value 0#32, .value 0#32, .value 127#32, .value 127#32] := by rfl

theorem read_31 (E : ⟪kernel.Γ⟫) :
    (result E).read (%31) = #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison] := by rfl

theorem read_32 (E : ⟪kernel.Γ⟫) :
    (result E).read (%32) = #v[.value 19#64, .value 19#64, .value 19#64, .value 19#64] := by rfl

theorem read_52 (E : ⟪kernel.Γ⟫) :
    (result E).read (%52) = #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison] := by rfl

theorem read_70 (E : ⟪kernel.Γ⟫) :
    (result E).read (%70) = #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison] := by rfl

theorem read_71 (E : ⟪kernel.Γ⟫) :
    (result E).read (%71) = .value 0#32 := by rfl

theorem read_88 (E : ⟪kernel.Γ⟫) :
    (result E).read (%88) = #v[.value 0#32, .value 0#32, .poison, .poison, .value 0#32, .value 0#32, .poison, .poison] := by rfl

theorem read_105 (E : ⟪kernel.Γ⟫) :
    (result E).read (%105) = #v[.poison, .poison, .value 0#32, .value 0#32, .poison, .poison, .value 0#32, .value 0#32] := by rfl

theorem read_106 (E : ⟪kernel.Γ⟫) :
    (result E).read (%106) = #v[.value 121666#64, .value 121666#64, .value 243332#64, .value 243330#64] := by rfl

theorem read_107 (E : ⟪kernel.Γ⟫) :
    (result E).read (%107) = #v[.value 67108862#64, .value 67108862#64, .value 67108862#64, .value 67108862#64] := by rfl

theorem read_108 (E : ⟪kernel.Γ⟫) :
    (result E).read (%108) = #v[.value 25#64, .value 25#64, .value 25#64, .value 25#64] := by rfl

theorem read_109 (E : ⟪kernel.Γ⟫) :
    (result E).read (%109) = #v[.value 33554431#64, .value 33554431#64, .value 33554431#64, .value 33554431#64] := by rfl

theorem read_127 (E : ⟪kernel.Γ⟫) :
    (result E).read (%127) = #v[.value 67108863#32, .poison, .value 67108863#32, .poison, .value 67108863#32, .poison, .value 67108863#32, .poison] := by rfl

theorem read_145 (E : ⟪kernel.Γ⟫) :
    (result E).read (%145) = #v[.value 33554431#32, .poison, .value 33554431#32, .poison, .value 33554431#32, .poison, .value 33554431#32, .poison] := by rfl

theorem read_146 (E : ⟪kernel.Γ⟫) :
    (result E).read (%146) = #v[.value 1073741520#32, .value 1073741520#32, .value 536870896#32, .value 536870896#32, .value 1073741520#32, .value 1073741520#32, .value 536870896#32, .value 536870896#32] := by rfl

theorem read_147 (E : ⟪kernel.Γ⟫) :
    (result E).read (%147) = #v[.value 1073741808#32, .value 1073741808#32, .value 536870896#32, .value 536870896#32, .value 1073741808#32, .value 1073741808#32, .value 536870896#32, .value 536870896#32] := by rfl

theorem read_148 (E : ⟪kernel.Γ⟫) :
    (result E).read (%148) = .value 5#64 := by rfl

theorem read_165 (E : ⟪kernel.Γ⟫) :
    (result E).read (%165) = #v[.poison, .poison, .poison, .poison, .poison, .value 67108863#32, .poison, .value 33554431#32] := by rfl

theorem read_183 (E : ⟪kernel.Γ⟫) :
    (result E).read (%183) = #v[.poison, .poison, .poison, .poison, .poison, .value 0#32, .poison, .value 15#32] := by rfl

theorem read_194 (E : ⟪kernel.Γ⟫) :
    (result E).read (%194) = #v[.poison, .poison, .poison, .value 19#64] := by rfl

theorem read_195 (E : ⟪kernel.Γ⟫) :
    (result E).read (%195) = .value 160#64 := by rfl

theorem read_196 (E : ⟪kernel.Γ⟫) :
    (result E).read (%196) = .value 192#64 := by rfl

theorem read_197 (E : ⟪kernel.Γ⟫) :
    (result E).read (%197) = .value 224#64 := by rfl

theorem read_198 (E : ⟪kernel.Γ⟫) :
    (result E).read (%198) = .value 256#64 := by rfl

theorem read_199 (E : ⟪kernel.Γ⟫) :
    (result E).read (%199) = .value 288#64 := by rfl

theorem read_200 (E : ⟪kernel.Γ⟫) :
    (result E).read (%200) = .value 320#64 := by rfl

theorem read_201 (E : ⟪kernel.Γ⟫) :
    (result E).read (%201) = .value 352#64 := by rfl

theorem read_202 (E : ⟪kernel.Γ⟫) :
    (result E).read (%202) = .value 384#64 := by rfl

theorem read_203 (E : ⟪kernel.Γ⟫) :
    (result E).read (%203) = .value 416#64 := by rfl

theorem read_204 (E : ⟪kernel.Γ⟫) :
    (result E).read (%204) = .value 448#64 := by rfl

theorem read_205 (E : ⟪kernel.Γ⟫) :
    (result E).read (%205) = .value 480#64 := by rfl

theorem read_206 (E : ⟪kernel.Γ⟫) :
    (result E).read (%206) = .value 512#64 := by rfl

theorem read_207 (E : ⟪kernel.Γ⟫) :
    (result E).read (%207) = .value 544#64 := by rfl

theorem read_208 (E : ⟪kernel.Γ⟫) :
    (result E).read (%208) = .value 576#64 := by rfl

theorem read_209 (E : ⟪kernel.Γ⟫) :
    (result E).read (%209) = .value 608#64 := by rfl

theorem read_210 (E : ⟪kernel.Γ⟫) :
    (result E).read (%210) = .value 640#64 := by rfl

theorem read_211 (E : ⟪kernel.Γ⟫) :
    (result E).read (%211) = .value 672#64 := by rfl

theorem read_212 (E : ⟪kernel.Γ⟫) :
    (result E).read (%212) = .value 704#64 := by rfl

theorem read_213 (E : ⟪kernel.Γ⟫) :
    (result E).read (%213) = .value 736#64 := by rfl

theorem read_214 (E : ⟪kernel.Γ⟫) :
    (result E).read (%214) = .value 768#64 := by rfl

theorem read_215 (E : ⟪kernel.Γ⟫) :
    (result E).read (%215) = .value 800#64 := by rfl

theorem read_216 (E : ⟪kernel.Γ⟫) :
    (result E).read (%216) = .value 832#64 := by rfl

theorem read_217 (E : ⟪kernel.Γ⟫) :
    (result E).read (%217) = .value 864#64 := by rfl

theorem read_218 (E : ⟪kernel.Γ⟫) :
    (result E).read (%218) = .value 896#64 := by rfl

theorem read_219 (E : ⟪kernel.Γ⟫) :
    (result E).read (%219) = .value 928#64 := by rfl

theorem read_220 (E : ⟪kernel.Γ⟫) :
    (result E).read (%220) = .value 960#64 := by rfl

theorem read_221 (E : ⟪kernel.Γ⟫) :
    (result E).read (%221) = .value 992#64 := by rfl

theorem read_222 (E : ⟪kernel.Γ⟫) :
    (result E).read (%222) = .value 1024#64 := by rfl

theorem read_223 (E : ⟪kernel.Γ⟫) :
    (result E).read (%223) = .value 1056#64 := by rfl

theorem read_224 (E : ⟪kernel.Γ⟫) :
    (result E).read (%224) = .value 1088#64 := by rfl

theorem read_225 (E : ⟪kernel.Γ⟫) :
    (result E).read (%225) = .value 1120#64 := by rfl

theorem read_226 (E : ⟪kernel.Γ⟫) :
    (result E).read (%226) = .value 1152#64 := by rfl

theorem read_227 (E : ⟪kernel.Γ⟫) :
    (result E).read (%227) = .value 1184#64 := by rfl

theorem read_228 (E : ⟪kernel.Γ⟫) :
    (result E).read (%228) = .value 1216#64 := by rfl

theorem read_229 (E : ⟪kernel.Γ⟫) :
    (result E).read (%229) = .value 1248#64 := by rfl

theorem read_230 (E : ⟪kernel.Γ⟫) :
    (result E).read (%230) = #v[.value 1#32, .value 1#32, .value 1#32, .value 1#32, .value 1#32, .value 1#32, .value 1#32, .value 1#32] := by rfl

theorem read_247 (E : ⟪kernel.Γ⟫) :
    (result E).read (%247) = #v[.value 0#32, .value 0#32, .value 0#32, .value 0#32, .poison, .poison, .poison, .poison] := by rfl

theorem read_264 (E : ⟪kernel.Γ⟫) :
    (result E).read (%264) = #v[.poison, .value 0#32, .poison, .value 0#32, .value 0#32, .poison, .value 0#32, .poison] := by rfl

theorem read_281 (E : ⟪kernel.Γ⟫) :
    (result E).read (%281) = #v[.poison, .value 134217690#32, .poison, .value 67108862#32, .value 134217690#32, .poison, .value 67108862#32, .poison] := by rfl

theorem read_298 (E : ⟪kernel.Γ⟫) :
    (result E).read (%298) = #v[.poison, .value 134217726#32, .poison, .value 67108862#32, .value 134217726#32, .poison, .value 67108862#32, .poison] := by rfl

theorem read_315 (E : ⟪kernel.Γ⟫) :
    (result E).read (%315) = #v[.value 0#32, .poison, .value 0#32, .poison, .poison, .value 0#32, .poison, .value 0#32] := by rfl

theorem read_332 (E : ⟪kernel.Γ⟫) :
    (result E).read (%332) = #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .value 134217690#32, .poison, .value 67108862#32, .poison] := by rfl

theorem read_349 (E : ⟪kernel.Γ⟫) :
    (result E).read (%349) = #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .value 134217726#32, .poison, .value 67108862#32, .poison] := by rfl

theorem read_350 (E : ⟪kernel.Γ⟫) :
    (result E).read (%350) = .value 7#64 := by rfl

theorem read_351 (E : ⟪kernel.Γ⟫) :
    (result E).read (%351) = .value 1280#64 := by rfl

theorem register_frame (E : ⟪kernel.Γ⟫) :
    DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E (result E) := by
  let E0 := phase0 E
  let E1 := phase1 E0
  let E2 := phase2 E1
  let E3 := phase3 E2
  let E4 := phase4 E3
  let E5 := phase5 E4
  let E6 := phase6 E5
  let E7 := phase7 E6
  let E8 := phase8 E7
  let E9 := phase9 E8
  let E10 := phase10 E9
  have h0 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E0 :=
    (phase0_frame E).weaken (by decide) (by decide)
  have h1 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E1 :=
    h0.trans ((phase1_frame E0).weaken (by decide) (by decide))
  have h2 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E2 :=
    h1.trans ((phase2_frame E1).weaken (by decide) (by decide))
  have h3 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E3 :=
    h2.trans ((phase3_frame E2).weaken (by decide) (by decide))
  have h4 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E4 :=
    h3.trans ((phase4_frame E3).weaken (by decide) (by decide))
  have h5 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E5 :=
    h4.trans ((phase5_frame E4).weaken (by decide) (by decide))
  have h6 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E6 :=
    h5.trans ((phase6_frame E5).weaken (by decide) (by decide))
  have h7 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E7 :=
    h6.trans ((phase7_frame E6).weaken (by decide) (by decide))
  have h8 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E8 :=
    h7.trans ((phase8_frame E7).weaken (by decide) (by decide))
  have h9 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E9 :=
    h8.trans ((phase9_frame E8).weaken (by decide) (by decide))
  have h10 : DoubleBase.ExecutionAvx2.RegisterFrame 0 352 E E10 :=
    h9.trans ((phase10_frame E9).weaken (by decide) (by decide))
  exact h10

end Agave.Ed25519.Tables.Avx2Constructor.Constants
