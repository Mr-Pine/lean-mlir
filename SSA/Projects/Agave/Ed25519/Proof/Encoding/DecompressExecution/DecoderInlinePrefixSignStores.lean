import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixSignTail

/-! The three exact sign-selection stores and the intervening high-limb load. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem sign_first_store_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (hr : SmallRange s.mem r 40) :
    Cutpoint.segment (program p g) 1 28 1 (signSelectedEnv E r byte x) s =
      .value (signSelectedEnv E r byte x, signFirstState s r byte x) := by
  have e101 : (signSelectedEnv E r byte x).read (%101) = .value (r.add 8#64) := rfl
  have e119 : (signSelectedEnv E r byte x).read (%119) =
    Ty.wrap #v[signChoose byte (x 1) (negativeOne x), signChoose byte (x 2) (negativeTwo x)] := rfl
  have hf := hr.fits_add (k := 8) (count := 16) (by decide)
  change List.foldlM Instr.run (signSelectedEnv E r byte x)
    (((program.bb1 p).body.drop 28).take 1) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,Operation.store,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_effect,
    e101,e119,hf,throwUBIf,signFirstState]

theorem sign_high_load_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (hr : SmallRange s.mem r 40)
    (hx3 : s.mem.readAt (r.add 24#64) 64 = x 3)
    (hx4 : s.mem.readAt (r.add 32#64) 64 = x 4) :
    Cutpoint.segment (program p g) 1 29 1 (signSelectedEnv E r byte x) s =
      .value (signHighEnv E r byte x, s) := by
  have e102 : (signSelectedEnv E r byte x).read (%102) = .value (r.add 24#64) := rfl
  have hf := hr.fits_add (k := 24) (count := 16) (by decide)
  have hv := smallRange_add hr (k := 24) (count := 16) (by decide)
  change List.foldlM Instr.run (signSelectedEnv E r byte x)
    (((program.bb1 p).body.drop 29).take 1) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,Operation.load,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_effect,
    e102,hf,hv,load_two_words,vector_two,Pointer.add_add,hx3,hx4,throwUBIf,signHighEnv]

theorem sign_low_store_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (hr : SmallRange s.mem r 40) (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 42 1 (signLowSelectedEnv E r byte x) s =
      .value (signLowSelectedEnv E r byte x, signLowState s r byte x) := by
  have e39 : (signLowSelectedEnv E r byte x).read (%39) = .value r := by
    simpa (disch := decide) only [signLowSelectedEnv,signHighCarryEnv,signLowFoldEnv,
      signHighShuffleEnv,signHighPrepEnv,signHighBiasEnv,signHighEnv,signSelectedEnv,
      signBroadcastEnv,signCarryEnv,signMaskEnv,signShiftEnv,signBiasEnv,signLoadEnv,mlir_env] using he.r39
  have e132 : (signLowSelectedEnv E r byte x).read (%132) =
    .value (signChoose byte (x 0) (negativeZero x)) := rfl
  have hf := Fits.mono (by decide : 64 ≤ 320) hr.fits
  change List.foldlM Instr.run (signLowSelectedEnv E r byte x)
    (((program.bb1 p).body.drop 42).take 1) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,Operation.store,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_effect,
    e39,e132,hf,throwUBIf,signLowState]

theorem sign_last_store_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (x : Words)
    (hr : SmallRange s.mem r 40) :
    Cutpoint.segment (program p g) 1 46 1 (signAllSelectedEnv E r byte x) s =
      .value (signAllSelectedEnv E r byte x, signLastState s r byte x) := by
  have e102 : (signAllSelectedEnv E r byte x).read (%102) = .value (r.add 24#64) := rfl
  have e135 : (signAllSelectedEnv E r byte x).read (%135) =
    Ty.wrap #v[signChoose byte (x 3) (negativeThree x), signChoose byte (x 4) (negativeFour x)] := rfl
  have hf := hr.fits_add (k := 24) (count := 16) (by decide)
  change List.foldlM Instr.run (signAllSelectedEnv E r byte x)
    (((program.bb1 p).body.drop 46).take 1) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,Operation.store,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_effect,
    e102,e135,hf,throwUBIf,signLastState]

theorem sign_first_high_read (s : GlobalState) (r : Pointer) (byte : BitVec 8)
    (x : Words) (hr : SmallRange s.mem r 40) (k : Nat) (hk : 24 ≤ k ∧ k + 8 ≤ 40) :
    (signFirstState s r byte x).mem.readAt (r.add (BitVec.ofNat 64 k)) 64 =
      s.mem.readAt (r.add (BitVec.ofNat 64 k)) 64 := by
  have h8 := Pointer.offsetInBits_add (hr.no_wrap (k := 8) (by decide))
  have hk' := Pointer.offsetInBits_add (hr.no_wrap (k := k) (by omega))
  have hkn : k < 18446744073709551616 := by omega
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.mod_eq_of_lt hkn] at h8 hk'
  have hd : (Range.of (r.add 8#64) 128).Disjoint
      (Range.of (r.add (BitVec.ofNat 64 k)) 64) := by
    simp only [Range.Disjoint, Range.of, Pointer.add_id, h8, hk']
    omega
  exact MemoryState.readAt_storeAt_disjoint hd _

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
