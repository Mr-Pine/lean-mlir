import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixSignCarry

/-! Remaining exact negative candidate and scalar/vector sign selections. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul SerialPoint
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def negativeThree (x : Words) : BitVec 64 :=
  (negativeBias x 3 &&& 2251799813685247#64) + (negativeBias x 2 >>> 51)
def negativeFour (x : Words) : BitVec 64 :=
  (negativeBias x 4 &&& 2251799813685247#64) + (negativeBias x 3 >>> 51)
def negativeZero (x : Words) : BitVec 64 :=
  (negativeBias x 4 >>> 51) * 19#64 + negativeLow x

def signFirstState (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words) : GlobalState :=
  {s with mem := s.mem.storeAt (r.add 8#64) (BitVec.packLanes #v[signChoose byte (x 1) (negativeOne x), signChoose byte (x 2) (negativeTwo x)])}

def signHighEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signSelectedEnv E r byte x)[%120 := Ty.wrap #v[x 3, x 4]]

def signHighBiasEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signHighEnv E r byte x)[%121 := Ty.wrap #v[negativeBias x 3, negativeBias x 4],
    %122 := .value (negativeBias x 4), %123 := .value (negativeBias x 4 >>> 51)]

def signHighPrepEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signHighBiasEnv E r byte x)[%124 := Ty.wrap #v[negativeBias x 3 &&& 2251799813685247#64, negativeBias x 4 &&& 2251799813685247#64],
    %125 := .value ((negativeBias x 4 >>> 51) * 19#64)]

def signHighShuffleEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signHighPrepEnv E r byte x)[%126 := Ty.wrap #v[negativeBias x 2, negativeBias x 3],
    %127 := Ty.wrap #v[negativeBias x 2 >>> 51, negativeBias x 3 >>> 51]]

def signLowFoldEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signHighShuffleEnv E r byte x)[%128 := .value (negativeZero x)]

def signHighCarryEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signLowFoldEnv E r byte x)[%129 := Ty.wrap #v[negativeThree x, negativeFour x]]

def signLowSelectedEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signHighCarryEnv E r byte x)[%130 := .value (negativeZero x ^^^ x 0),
    %131 := .value ((negativeZero x ^^^ x 0) &&& signMask byte),
    %132 := .value (signChoose byte (x 0) (negativeZero x))]

def signAllSelectedEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signLowSelectedEnv E r byte x)[%133 := Ty.wrap #v[negativeThree x ^^^ x 3, negativeFour x ^^^ x 4],
    %134 := Ty.wrap #v[(negativeThree x ^^^ x 3) &&& signMask byte, (negativeFour x ^^^ x 4) &&& signMask byte],
    %135 := Ty.wrap #v[signChoose byte (x 3) (negativeThree x), signChoose byte (x 4) (negativeFour x)]]

def signLowState (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words) : GlobalState :=
  {s with mem := s.mem.storeAt r (signChoose byte (x 0) (negativeZero x))}

def signLastState (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words) : GlobalState :=
  {s with mem := s.mem.storeAt (r.add 24#64) (BitVec.packLanes #v[signChoose byte (x 3) (negativeThree x), signChoose byte (x 4) (negativeFour x)])}

theorem sign_highbias_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 30 3 (signHighEnv E r byte x) s =
      .value (signHighBiasEnv E r byte x, s) := by
  have e120 : (signHighEnv E r byte x).read (%120) = Ty.wrap #v[x 3,x 4] := rfl
  have e12 : (signHighEnv E r byte x).read (%12) = Ty.wrap (Vector.replicate 2 36028797018963952#64) := by
    simpa (disch := decide) only [signLowSelectedEnv,signHighCarryEnv,signLowFoldEnv,signHighShuffleEnv,signHighPrepEnv,signHighBiasEnv,signHighEnv,signSelectedEnv,signBroadcastEnv,signCarryEnv,signMaskEnv,signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c12
  have e6 : (signHighEnv E r byte x).read (%6) = .value 1#64 := by
    simpa (disch := decide) only [signLowSelectedEnv,signHighCarryEnv,signLowFoldEnv,signHighShuffleEnv,signHighPrepEnv,signHighBiasEnv,signHighEnv,signSelectedEnv,signBroadcastEnv,signCarryEnv,signMaskEnv,signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c6
  have e16 : (signHighEnv E r byte x).read (%16) = .value 51#64 := by
    simpa (disch := decide) only [signLowSelectedEnv,signHighCarryEnv,signLowFoldEnv,signHighShuffleEnv,signHighPrepEnv,signHighBiasEnv,signHighEnv,signSelectedEnv,signBroadcastEnv,signCarryEnv,signMaskEnv,signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c16
  change List.foldlM Instr.run (signHighEnv E r byte x)
    (((program.bb1 p).body.drop 30).take 3) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,TernOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e120,e12,e6,e16, signHighBiasEnv,negativeBias,vector_two]

theorem sign_highprep_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 33 2 (signHighBiasEnv E r byte x) s =
      .value (signHighPrepEnv E r byte x, s) := by
  have e121 : (signHighBiasEnv E r byte x).read (%121) = Ty.wrap #v[negativeBias x 3,negativeBias x 4] := rfl
  have e123 : (signHighBiasEnv E r byte x).read (%123) = .value (negativeBias x 4 >>> 51) := rfl
  have e15 : (signHighBiasEnv E r byte x).read (%15) = Ty.wrap (Vector.replicate 2 2251799813685247#64) := by
    simpa (disch := decide) only [signLowSelectedEnv,signHighCarryEnv,signLowFoldEnv,signHighShuffleEnv,signHighPrepEnv,signHighBiasEnv,signHighEnv,signSelectedEnv,signBroadcastEnv,signCarryEnv,signMaskEnv,signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c15
  have e5 : (signHighBiasEnv E r byte x).read (%5) = .value 19#64 := by
    simpa (disch := decide) only [signLowSelectedEnv,signHighCarryEnv,signLowFoldEnv,signHighShuffleEnv,signHighPrepEnv,signHighBiasEnv,signHighEnv,signSelectedEnv,signBroadcastEnv,signCarryEnv,signMaskEnv,signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c5
  change List.foldlM Instr.run (signHighBiasEnv E r byte x)
    (((program.bb1 p).body.drop 33).take 2) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,TernOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e121,e123,e15,e5, signHighPrepEnv,SerialPoint.weak_mul_nooverflow,vector_two]

theorem sign_highshuffle_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 35 2 (signHighPrepEnv E r byte x) s =
      .value (signHighShuffleEnv E r byte x, s) := by
  have e110 : (signHighPrepEnv E r byte x).read (%110) = Ty.wrap #v[negativeBias x 1,negativeBias x 2] := rfl
  have e121 : (signHighPrepEnv E r byte x).read (%121) = Ty.wrap #v[negativeBias x 3,negativeBias x 4] := rfl
  have e13 : (signHighPrepEnv E r byte x).read (%13) = Ty.wrap (Vector.replicate 2 51#64) := by
    simpa (disch := decide) only [signLowSelectedEnv,signHighCarryEnv,signLowFoldEnv,signHighShuffleEnv,signHighPrepEnv,signHighBiasEnv,signHighEnv,signSelectedEnv,signBroadcastEnv,signCarryEnv,signMaskEnv,signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c13
  change List.foldlM Instr.run (signHighPrepEnv E r byte x)
    (((program.bb1 p).body.drop 35).take 2) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,TernOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e110,e121,e13, signHighShuffleEnv,negativeBias,vector_two]

theorem sign_lowfold_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 37 1 (signHighShuffleEnv E r byte x) s =
      .value (signLowFoldEnv E r byte x, s) := by
  have e125 : (signHighShuffleEnv E r byte x).read (%125) =
      .value ((negativeBias x 4 >>> 51) * 19#64) := rfl
  have e112 : (signHighShuffleEnv E r byte x).read (%112) = .value (negativeLow x) := rfl
  change List.foldlM Instr.run (signHighShuffleEnv E r byte x)
    (((program.bb1 p).body.drop 37).take 1) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp only [List.foldlM_cons,List.foldlM_nil,Instr.run,e125,e112,
    BinOp.compute,negativeLow,fold_operation,EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,
    signLowFoldEnv,negativeZero]

theorem sign_highcarry_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 38 1 (signLowFoldEnv E r byte x) s =
      .value (signHighCarryEnv E r byte x, s) := by
  have e124 : (signLowFoldEnv E r byte x).read (%124) =
      Ty.wrap #v[negativeBias x 3 &&& 2251799813685247#64, negativeBias x 4 &&& 2251799813685247#64] := rfl
  have e127 : (signLowFoldEnv E r byte x).read (%127) =
      Ty.wrap #v[negativeBias x 2 >>> 51, negativeBias x 3 >>> 51] := rfl
  change List.foldlM Instr.run (signLowFoldEnv E r byte x)
    (((program.bb1 p).body.drop 38).take 1) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp only [List.foldlM_cons,List.foldlM_nil,Instr.run,e124,e127,
    carry_vector_operation,EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,
    signHighCarryEnv,negativeThree,negativeFour]

theorem sign_lowselected_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 39 3 (signHighCarryEnv E r byte x) s =
      .value (signLowSelectedEnv E r byte x, s) := by
  have e128 : (signHighCarryEnv E r byte x).read (%128) = .value (negativeZero x) := rfl
  have e105 : (signHighCarryEnv E r byte x).read (%105) = .value (x 0) := rfl
  have e104 : (signHighCarryEnv E r byte x).read (%104) = .value (signMask byte) := rfl
  change List.foldlM Instr.run (signHighCarryEnv E r byte x)
    (((program.bb1 p).body.drop 39).take 3) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,TernOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e128,e105,e104, signLowSelectedEnv,signChoose,vector_two]

theorem sign_allselected_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 43 3 (signLowSelectedEnv E r byte x) s =
      .value (signAllSelectedEnv E r byte x, s) := by
  have e129 : (signLowSelectedEnv E r byte x).read (%129) = Ty.wrap #v[negativeThree x,negativeFour x] := rfl
  have e120 : (signLowSelectedEnv E r byte x).read (%120) = Ty.wrap #v[x 3,x 4] := rfl
  have e117 : (signLowSelectedEnv E r byte x).read (%117) = Ty.wrap #v[signMask byte,signMask byte] := rfl
  change List.foldlM Instr.run (signLowSelectedEnv E r byte x)
    (((program.bb1 p).body.drop 43).take 3) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,TernOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e129,e120,e117, signAllSelectedEnv,signChoose,vector_two]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
