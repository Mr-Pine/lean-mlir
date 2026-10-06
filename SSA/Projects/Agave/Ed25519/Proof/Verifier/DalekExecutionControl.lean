import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ControlFlow
import SSA.Projects.RIR.Run.Tactic

/-!
Local control-flow lemmas for the exact extracted `verify_dalek` body.
These lemmas use the generated blocks, not a second hand-written verifier.
External-call hypotheses describe one invocation of one named primitive.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

@[simp] theorem params_0 : program.blockParams 0 = .nil := rfl
@[simp] theorem params_1 : program.blockParams 1 = .nil := rfl
@[simp] theorem params_2 : program.blockParams 2 = .nil := rfl
@[simp] theorem params_3 : program.blockParams 3 = .nil := rfl
@[simp] theorem params_4 : program.blockParams 4 = .nil := rfl
@[simp] theorem params_5 : program.blockParams 5 = .nil := rfl
@[simp] theorem params_6 : program.blockParams 6 = .nil := rfl
@[simp] theorem params_7 : program.blockParams 7 = .nil := rfl
@[simp] theorem params_8 : program.blockParams 8 = .nil := rfl
@[simp] theorem params_9 : program.blockParams 9 = .nil := rfl
@[simp] theorem params_10 : program.blockParams 10 = .nil := rfl
@[simp] theorem params_11 : program.blockParams 11 = .nil := rfl
@[simp] theorem params_12 : program.blockParams 12 = .cons (%70) .nil := rfl
@[simp] theorem params_13 : program.blockParams 13 = .cons (%71) .nil := rfl
@[simp] theorem block_0 (p : Primitives) (g : Globals) :
    (program p g).blocks 0 = program.bb0 p g := rfl
@[simp] theorem block_1 (p : Primitives) (g : Globals) :
    (program p g).blocks 1 = program.bb1 p := rfl
@[simp] theorem block_2 (p : Primitives) (g : Globals) :
    (program p g).blocks 2 = program.bb2 p := rfl
@[simp] theorem block_3 (p : Primitives) (g : Globals) :
    (program p g).blocks 3 = program.bb3 := rfl
@[simp] theorem block_4 (p : Primitives) (g : Globals) :
    (program p g).blocks 4 = program.bb4 p := rfl
@[simp] theorem block_5 (p : Primitives) (g : Globals) :
    (program p g).blocks 5 = program.bb5 := rfl
@[simp] theorem block_6 (p : Primitives) (g : Globals) :
    (program p g).blocks 6 = program.bb6 p := rfl
@[simp] theorem block_7 (p : Primitives) (g : Globals) :
    (program p g).blocks 7 = program.bb7 := rfl
@[simp] theorem block_8 (p : Primitives) (g : Globals) :
    (program p g).blocks 8 = program.bb8 p := rfl
@[simp] theorem block_9 (p : Primitives) (g : Globals) :
    (program p g).blocks 9 = program.bb9 p := rfl
@[simp] theorem block_10 (p : Primitives) (g : Globals) :
    (program p g).blocks 10 = program.bb10 p := rfl
@[simp] theorem block_11 (p : Primitives) (g : Globals) :
    (program p g).blocks 11 = program.bb11 := rfl
@[simp] theorem block_12 (p : Primitives) (g : Globals) :
    (program p g).blocks 12 = program.bb12 := rfl
@[simp] theorem block_13 (p : Primitives) (g : Globals) :
    (program p g).blocks 13 = program.bb13 := rfl

/-- The concrete pinned `Result<(), SignatureError>` success/error bytes. -/
def code (accepted : Bool) : BitVec 8 := if accepted then 255 else 2

/-- The final lifetime marker has no observable effect in RIR. -/
theorem return_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (result : BitVec 8) (hr : E.read (%71) = .value result) :
    (program p g).runFrom E 13 s = .value (.cons (.value result) .nil, s) := by
  have hb : program.bb13.run program.blockParams E s =
      .value ((E, .inl (.cons (.value result) .nil)), s) := by
    simp [BasicBlock.run, program.bb13, List.foldlM_cons, List.foldlM_nil,
      Instr.run, EffectM.pure_eq, EffectM.bind_eq, Exit.run, Regs.read_cons,
      Regs.read_nil, hr]
  rw [Func.runFrom_eq, block_13, hb]
  rfl

/-- Every checked rejection and the comparison result pass unchanged through
both cleanup blocks. -/
theorem cleanup_blocks (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (result : BitVec 8) (hr : E.read (%70) = .value result) :
    (program p g).runFrom E 12 s = .value (.cons (.value result) .nil, s) := by
  have hb : program.bb12.run program.blockParams E s =
      .value ((E[%71 := .value result], .inr 13), s) := by
    simp [BasicBlock.run, program.bb12, List.foldlM_cons, List.foldlM_nil,
      Instr.run, EffectM.pure_eq, EffectM.bind_eq, Exit.run, Jump.run,
      Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil, hr]
  rw [Func.runFrom_eq, block_12, hb]
  change (program p g).runFrom (E[%71 := .value result]) 13 s = _
  apply return_block
  simp [mlir_env]

/-- Scalar-parsing failure returns the error byte after cleanup. -/
theorem scalar_rejection (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (hr : E.read (%8) = .value 2#8) :
    (program p g).runFrom E 11 s = .value (.cons (.value 2#8) .nil, s) := by
  have hb : program.bb11.run program.blockParams E s =
      .value ((E[%70 := .value 2#8], .inr 12), s) := by
    simp [BasicBlock.run, program.bb11, List.foldlM_cons, List.foldlM_nil,
      Instr.run, EffectM.pure_eq, EffectM.bind_eq, Exit.run, Jump.run,
      Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil, hr]
  rw [Func.runFrom_eq, block_11, hb]
  change (program p g).runFrom (E[%70 := .value 2#8]) 12 s = _
  apply cleanup_blocks
  simp [mlir_env]

/-- Failed decompression returns the same error byte. -/
theorem decompression_rejection (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (hr : E.read (%8) = .value 2#8) :
    (program p g).runFrom E 3 s = .value (.cons (.value 2#8) .nil, s) := by
  have hb : program.bb3.run program.blockParams E s =
      .value ((E[%70 := .value 2#8], .inr 12), s) := by
    simp [BasicBlock.run, program.bb3, List.foldlM_cons, List.foldlM_nil,
      Instr.run, EffectM.pure_eq, EffectM.bind_eq, Exit.run, Jump.run,
      Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil, hr]
  rw [Func.runFrom_eq, block_3, hb]
  change (program p g).runFrom (E[%70 := .value 2#8]) 12 s = _
  apply cleanup_blocks
  simp [mlir_env]

/-- Execute the final compression and `bcmp` calls, followed by the actual
comparison/select and both cleanup blocks. The two hypotheses each describe
one primitive invocation, including its state transition. -/
theorem compression_tail (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s t u : GlobalState) (out point signature : Pointer) (comparison : BitVec 32)
    (hout : E.read (%26) = .value out) (hpoint : E.read (%25) = .value point)
    (hsig : E.read (%arg1) = .value signature)
    (hlen : E.read (%1) = .value 32#64)
    (hzero : E.read (%19) = .value 0#32)
    (hok : E.read (%13) = .value 255#8)
    (herr : E.read (%8) = .value 2#8)
    (hc : p.compressPoint (args2 out point) s = .value (.nil, t))
    (hb : p.compareBytes (.cons (.value out) (.cons (.value signature)
      (.cons (.value 32#64) .nil))) t = .value (.cons (.value comparison) .nil, u)) :
    (program p g).runFrom E 10 s =
      .value (.cons (.value (code (decide (comparison = 0#32)))) .nil, u) := by
  dsimp only [args2] at hc
  change E.args 1 = .value signature at hsig
  let result := code (decide (comparison = 0#32))
  let E' := E[%67 := .value comparison,
    %68 := .value (BitVec.ofBool (comparison == 0#32)), %69 := .value result,
    %70 := .value result]
  have hblock : (program.bb10 p).run program.blockParams E s =
      .value ((E', .inr 12), u) := by
    by_cases heq : comparison = 0#32 <;>
      simp [BasicBlock.run, program.bb10,
        E', result, code, List.foldlM_cons, List.foldlM_nil, Instr.run,
        BinOp.compute, TernOp.compute, Operation.icmp, Operation.select,
        EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
        mlir_env, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
        Env.writeMany_cons, Env.writeMany_nil, args2,
        hout, hpoint, hsig, hlen, hzero, hok, herr, hc, hb, heq]
    all_goals
      try rw [hb]
      simp [E', result, code, mlir_env, Env.writeMany_cons, Env.writeMany_nil,
        PoisonOr.value_bind, Operation.icmp, Operation.select, hzero, hok, herr, heq,
        ofBool_eq_one_iff]
  rw [Func.runFrom_eq, block_10, hblock]
  simp only [PoisonOr.value_bind, Func.continue]
  apply cleanup_blocks
  simp [E', result, mlir_env]

/-- A backend call returns directly to the common compression block. This
executes the serial call site of the generated verifier. -/
theorem serial_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s t : GlobalState) (out hptr aptr sptr : Pointer)
    (hout : E.read (%25) = .value out) (hh : E.read (%32) = .value hptr)
    (ha : E.read (%33) = .value aptr) (hs : E.read (%27) = .value sptr)
    (hc : p.serialDoubleBase (args4 out hptr aptr sptr) s = .value (.nil, t)) :
    (program p g).runFrom E 8 s = (program p g).runFrom E 10 t := by
  dsimp only [args4] at hc
  have hblock : (program.bb8 p).run program.blockParams E s =
      .value ((E, .inr 10), t) := by
    simp [BasicBlock.run, program.bb8,
      List.foldlM_cons, List.foldlM_nil, Instr.run,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
      mlir_env, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil, args4, hout, hh, ha, hs, hc]
  rw [Func.runFrom_eq, block_8, hblock]
  rfl

/-- The vector call site uses the same argument order and continuation. -/
theorem avx2_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s t : GlobalState) (out hptr aptr sptr : Pointer)
    (hout : E.read (%25) = .value out) (hh : E.read (%32) = .value hptr)
    (ha : E.read (%33) = .value aptr) (hs : E.read (%27) = .value sptr)
    (hc : p.avx2DoubleBase (args4 out hptr aptr sptr) s = .value (.nil, t)) :
    (program p g).runFrom E 9 s = (program p g).runFrom E 10 t := by
  dsimp only [args4] at hc
  have hblock : (program.bb9 p).run program.blockParams E s =
      .value ((E, .inr 10), t) := by
    simp [BasicBlock.run, program.bb9,
      List.foldlM_cons, List.foldlM_nil, Instr.run,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
      mlir_env, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil, args4, hout, hh, ha, hs, hc]
  rw [Func.runFrom_eq, block_9, hblock]
  rfl

/-- The CPUID initializer's returned bit is stored in `%64` but does not
control dispatch. Dispatch reads the state produced by the call. -/
theorem initialize_cache_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s t : GlobalState) (returned : BitVec 1)
    (hc : p.initializeAvx2Cache .nil s = .value (.cons (.value returned) .nil, t)) :
    (program p g).runFrom E 6 s =
      (program p g).runFrom (E[%64 := .value returned]) 7 t := by
  have hblock : (program.bb6 p).run program.blockParams E s =
      .value ((E[%64 := .value returned], .inr 7), t) := by
    simp [BasicBlock.run, program.bb6,
      List.foldlM_cons, List.foldlM_nil, Instr.run,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
      mlir_env, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil, hc]
  rw [Func.runFrom_eq, block_6, hblock]
  rfl

/-- Exact second atomic cache load and runtime dispatch. Every non-one byte
selects the serial branch; validity of a cached state is a separate invariant. -/
theorem dispatch_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (cache : Pointer) (value : BitVec 8)
    (hcache : E.read (%18) = .value cache) (hone : E.read (%14) = .value 1#8)
    (hfits : Fits s.mem cache 8) (hread : s.mem.readAt cache 8 = value) :
    (program p g).runFrom E 7 s =
      (program p g).runFrom
        (E[%65 := .value value, %66 := .value (BitVec.ofBool (value == 1))])
        (if value = 1 then 9 else 8) s := by
  have hblock : program.bb7.run program.blockParams E s =
      .value (((E[%65 := .value value, %66 := .value (BitVec.ofBool (value == 1))]),
        .inr (if value = 1 then 9 else 8)), s) := by
    by_cases heq : value = 1#8 <;>
      simp [BasicBlock.run, program.bb7,
        List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
        BinOp.compute, Operation.icmp, EffectM.bind_eq, EffectM.pure_eq,
        mlir_effect, mlir_env, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
        Env.writeMany_cons, Env.writeMany_nil, hcache, hone, hfits, hread,
        heq, throwUBIf, ofBool_eq_one_iff]
  rw [Func.runFrom_eq, block_7, hblock]
  rfl

/-- The two local primitive contracts imply the compressed-byte comparison
result of the actual extracted suffix, for arbitrary R bytes. -/
theorem compression_tail_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (compress : Result → Bytes32)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (E : Env program.Γ) (state : GlobalState) (out point signature : Pointer)
    (result : Result) (r : Bytes32) (encoded : PointBytes)
    (hout : E.read (%26) = .value out) (hpoint : E.read (%25) = .value point)
    (hsig : E.read (%arg1) = .value signature)
    (hlen : E.read (%1) = .value 32#64)
    (hzero : E.read (%19) = .value 0#32)
    (hok : E.read (%13) = .value 255#8)
    (herr : E.read (%8) = .value 2#8)
    (hwf : state.WF) (houtput : SmallRange state.mem out 32)
    (hresult : ReadBytes state point 160 encoded) (hencoded : layout.result result encoded)
    (hr : ReadBytes state signature 32 r)
    (hdpoint : (Range.of out 256).Disjoint (Range.of point 1280))
    (hdr : (Range.of signature 256).Disjoint (Range.of out 256)) :
    ∃ after, (program p g).runFrom E 10 state =
      .value (.cons (.value (code (decide (compress result = r)))) .nil, after) := by
  obtain ⟨after, hc, hf, hv⟩ := hcompress out point state result encoded hwf houtput hresult hencoded hdpoint
  have hr' : ReadBytes after signature 32 r :=
    ⟨hf.live signature 32 hr.1, (hf.read signature 256 hdr).trans hr.2⟩
  obtain ⟨last, comparison, hb, _, heq⟩ := hcompare out signature after (compress result) r
    hf.wellFormed hv hr'
  change comparison = 0#32 ↔ compress result = r at heq
  refine ⟨last, ?_⟩
  rw [compression_tail p g E state after last out point signature comparison
    hout hpoint hsig hlen hzero hok herr hc hb]
  simp only [heq]

/-- The option tag loaded after the external decompressor is tested by the
actual flagged truncation. Both tag values execute without poison. -/
theorem decompress_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s t : GlobalState) (out signature : Pointer) (success : Bool)
    (hout : E.read (%28) = .value out) (hsig : E.read (%arg1) = .value signature)
    (hc : p.decompress (args2 out signature) s = .value (.nil, t))
    (hfits : Fits t.mem out 64)
    (hread : t.mem.readAt out 64 = if success then 1 else 0) :
    (program p g).runFrom E 1 s =
      (program p g).runFrom
        (E[%39 := .value (if success then 1 else 0),
          %40 := .value (BitVec.ofBool success)])
        (if success then 2 else 3) t := by
  dsimp only [args2] at hc
  change E.args 1 = .value signature at hsig
  have hblock : (program.bb1 p).run program.blockParams E s =
      .value (((E[%39 := .value (if success then 1 else 0),
        %40 := .value (BitVec.ofBool success)]), .inr (if success then 2 else 3)), t) := by
    cases success <;>
      simp [BasicBlock.run, program.bb1,
        List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
        UnOp.compute, Operation.trunc, EffectM.bind_eq, EffectM.pure_eq,
        mlir_effect, mlir_env, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
        Env.writeMany_cons, Env.writeMany_nil, args2, hout, hsig, hc, hfits, hread,
        throwUBIf]
  rw [Func.runFrom_eq, block_1, hblock]
  rfl

/-- Decompression's `none` branch rejects every undecodable R encoding,
without requiring any condition on the scalar bytes. -/
theorem decompress_none_of_contract {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar) (hdecompress : DecompressContract p.decompress layout shared)
    (E : Env program.Γ) (state : GlobalState) (out signature : Pointer) (r : Bytes32)
    (hout : E.read (%28) = .value out) (hsig : E.read (%arg1) = .value signature)
    (herr : E.read (%8) = .value 2#8) (hwf : state.WF)
    (ho : SmallRange state.mem out 168) (hr : ReadBytes state signature 32 r)
    (hd : (Range.of out 1344).Disjoint (Range.of signature 256))
    (hnone : shared.decompress r = none) :
    ∃ after, (program p g).runFrom E 1 state =
      .value (.cons (.value 2#8) .nil, after) := by
  obtain ⟨after, hc, hframe, htag⟩ := hdecompress out signature state r hwf ho hr hd
  simp only [hnone] at htag
  have hfits : Fits after.mem out 64 :=
    Fits.mono (by decide) (hframe.live out 168 ho).fits
  refine ⟨after, ?_⟩
  rw [decompress_block p g E state after out signature false hout hsig hc hfits htag]
  apply decompression_rejection
  simp [mlir_env, herr]

end Agave.Ed25519.Verifier.Execution.Dalek
