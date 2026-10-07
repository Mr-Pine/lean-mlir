import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixSignLoad

/-! Exact conditional-negation vector slices, with flagged carries proved. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def negativeBias (x : Words) : Words := ![36028797018963664#64 - x 0,
  36028797018963952#64 - x 1, 36028797018963952#64 - x 2,
  36028797018963952#64 - x 3, 36028797018963952#64 - x 4]
def negativeLow (x : Words) : BitVec 64 :=
  (2251799813684944#64 - x 0) &&& 2251799813685247#64
def negativeOne (x : Words) : BitVec 64 :=
  (negativeBias x 1 &&& 2251799813685247#64) + (negativeBias x 0 >>> 51)
def negativeTwo (x : Words) : BitVec 64 :=
  (negativeBias x 2 &&& 2251799813685247#64) + (negativeBias x 1 >>> 51)
def signMask (byte : BitVec 8) : BitVec 64 := if byte[7] then (-1#64) else 0#64
def signChoose (byte : BitVec 8) (original replacement : BitVec 64) : BitVec 64 :=
  ((replacement ^^^ original) &&& signMask byte) ^^^ original

def signBiasEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signLoadEnv E r byte x)[%108 := .value (2251799813684944#64 - x 0),
    %109 := Ty.wrap #v[negativeBias x 0, negativeBias x 1],
    %110 := Ty.wrap #v[negativeBias x 1, negativeBias x 2]]

def signShiftEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signBiasEnv E r byte x)[%111 := Ty.wrap #v[negativeBias x 0 >>> 51, negativeBias x 1 >>> 51]]

def signMaskEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signShiftEnv E r byte x)[%112 := .value (negativeLow x),
    %113 := Ty.wrap #v[negativeBias x 1 &&& 2251799813685247#64, negativeBias x 2 &&& 2251799813685247#64]]

def signCarryEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signMaskEnv E r byte x)[%114 := Ty.wrap #v[negativeOne x, negativeTwo x]]

def signBroadcastEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signCarryEnv E r byte x)[%115 := Ty.wrap #v[negativeOne x ^^^ x 1, negativeTwo x ^^^ x 2],
    %116 := #v[.value (signMask byte), .poison],
    %117 := Ty.wrap #v[signMask byte, signMask byte]]

def signSelectedEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  (signBroadcastEnv E r byte x)[%118 := Ty.wrap #v[(negativeOne x ^^^ x 1) &&& signMask byte, (negativeTwo x ^^^ x 2) &&& signMask byte],
    %119 := Ty.wrap #v[signChoose byte (x 1) (negativeOne x), signChoose byte (x 2) (negativeTwo x)]]

theorem sign_bias_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 16 3 (signLoadEnv E r byte x) s =
      .value (signBiasEnv E r byte x, s) := by
  obtain ⟨e39,e100,e1,e5,e6,e7,e8,e12,e13,e14,e15,e16,e23,e24,e25⟩ := he
  change List.foldlM Instr.run (signLoadEnv E r byte x)
    (((program.bb1 p).body.drop 16).take 3) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e1,e5,e6,e7,e8,e12,e13,e14,e15,e16,e23,e24,e25,
    signBiasEnv, signLoadEnv,negativeBias,negativeLow,signMask,signChoose,vector_two]

theorem sign_shift_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 19 1 (signBiasEnv E r byte x) s =
      .value (signShiftEnv E r byte x, s) := by
  have e109 : (signBiasEnv E r byte x).read (%109) = Ty.wrap #v[negativeBias x 0, negativeBias x 1] := rfl
  have e13 : (signBiasEnv E r byte x).read (%13) = Ty.wrap (Vector.replicate 2 51#64) := by
    simpa (disch := decide) only [signBiasEnv,signLoadEnv,mlir_env] using he.c13
  change List.foldlM Instr.run (signBiasEnv E r byte x)
    (((program.bb1 p).body.drop 19).take 1) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide) [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e109,e13,signShiftEnv,vector_two]

theorem sign_mask_last_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 20 2 (signShiftEnv E r byte x) s =
      .value (signMaskEnv E r byte x, s) := by
  have e108 : (signShiftEnv E r byte x).read (%108) = .value (2251799813684944#64 - x 0) := rfl
  have e110 : (signShiftEnv E r byte x).read (%110) = Ty.wrap #v[negativeBias x 1,negativeBias x 2] := rfl
  have e15 : (signShiftEnv E r byte x).read (%15) = Ty.wrap (Vector.replicate 2 2251799813685247#64) := by
    simpa (disch := decide) only [signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c15
  have e1 : (signShiftEnv E r byte x).read (%1) = .value 2251799813685247#64 := by
    simpa (disch := decide) only [signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c1
  change List.foldlM Instr.run (signShiftEnv E r byte x)
    (((program.bb1 p).body.drop 20).take 2) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide) [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e108,e110,e15,e1,signMaskEnv,negativeLow,vector_two]

theorem sign_mask_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 19 3 (signBiasEnv E r byte x) s =
      .value (signMaskEnv E r byte x, s) := by
  rw [show 3 = 1 + 2 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_shift_segment p g E s r byte x he,
    PoisonOr.value_bind]
  exact sign_mask_last_segment p g E s r byte x he

theorem sign_carry_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 22 1 (signMaskEnv E r byte x) s =
      .value (signCarryEnv E r byte x, s) := by
  have e113 : (signMaskEnv E r byte x).read (%113) =
      Ty.wrap #v[negativeBias x 1 &&& 2251799813685247#64, negativeBias x 2 &&& 2251799813685247#64] := rfl
  have e111 : (signMaskEnv E r byte x).read (%111) =
      Ty.wrap #v[negativeBias x 0 >>> 51, negativeBias x 1 >>> 51] := rfl
  change List.foldlM Instr.run (signMaskEnv E r byte x)
    (((program.bb1 p).body.drop 22).take 1) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp only [List.foldlM_cons,List.foldlM_nil,Instr.run,e113,e111,
    carry_vector_operation,EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,
    signCarryEnv,negativeOne,negativeTwo]

theorem sign_broadcast_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 23 3 (signCarryEnv E r byte x) s =
      .value (signBroadcastEnv E r byte x, s) := by
  have e114 : (signCarryEnv E r byte x).read (%114) = Ty.wrap #v[negativeOne x,negativeTwo x] := rfl
  have e107 : (signCarryEnv E r byte x).read (%107) = Ty.wrap #v[x 1,x 2] := rfl
  have e104 : (signCarryEnv E r byte x).read (%104) = .value (signMask byte) := rfl
  have e25 : (signCarryEnv E r byte x).read (%25) = Ty.poisoned (.vec 2 64) := by
    simpa (disch := decide) only [signBroadcastEnv,signCarryEnv,signMaskEnv,signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c25
  have e14 : (signCarryEnv E r byte x).read (%14) = .value 0#64 := by
    simpa (disch := decide) only [signBroadcastEnv,signCarryEnv,signMaskEnv,signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.c14
  change List.foldlM Instr.run (signCarryEnv E r byte x)
    (((program.bb1 p).body.drop 23).take 3) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,TernOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e114,e107,e104,e25,e14, signBroadcastEnv,signMask,vector_two]

theorem sign_selected_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 26 2 (signBroadcastEnv E r byte x) s =
      .value (signSelectedEnv E r byte x, s) := by
  have e115 : (signBroadcastEnv E r byte x).read (%115) = Ty.wrap #v[negativeOne x ^^^ x 1, negativeTwo x ^^^ x 2] := rfl
  have e117 : (signBroadcastEnv E r byte x).read (%117) = Ty.wrap #v[signMask byte,signMask byte] := rfl
  have e107 : (signBroadcastEnv E r byte x).read (%107) = Ty.wrap #v[x 1,x 2] := rfl
  change List.foldlM Instr.run (signBroadcastEnv E r byte x)
    (((program.bb1 p).body.drop 26).take 2) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,TernOp.compute,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_operation,
    e115,e117,e107, signSelectedEnv,signChoose,vector_two]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
