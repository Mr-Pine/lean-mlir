import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixSignEntry

/-! Success-block sign mask and initial root loads, exact instructions9--15. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure SignRegisters (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) : Prop where
  r39 : E.read (%39) = .value r
  sign100 : E.read (%100) = .value (byte >>> 7)
  c1 : E.read (%1) = .value 2251799813685247#64
  c5 : E.read (%5) = .value 19#64
  c6 : E.read (%6) = .value 1#64
  c7 : E.read (%7) = .value 24#64
  c8 : E.read (%8) = .value 8#64
  c12 : E.read (%12) = Ty.wrap (Vector.replicate 2 36028797018963952#64)
  c13 : E.read (%13) = Ty.wrap (Vector.replicate 2 51#64)
  c14 : E.read (%14) = .value 0#64
  c15 : E.read (%15) = Ty.wrap (Vector.replicate 2 2251799813685247#64)
  c16 : E.read (%16) = .value 51#64
  c23 : E.read (%23) = .value 2251799813684944#64
  c24 : E.read (%24) = Ty.wrap #v[36028797018963664#64, 36028797018963952#64]
  c25 : E.read (%25) = Ty.poisoned (.vec 2 64)

theorem sign_registers (g : Globals) (s t : GlobalState) (out input : Pointer) (byte : BitVec 8) :
    SignRegisters (signEnv g s t out input byte) (slot9 s) byte := by
  constructor <;> rfl

def signLoadEnv (E : Env program.Γ) (r : Pointer) (byte : BitVec 8) (x : Words) : Env program.Γ :=
  E[%101 := .value (r.add 8#64), %102 := .value (r.add 24#64),
    %103 := .value ((byte >>> 7).setWidth 64),
    %104 := .value (if byte[7] then (-1#64) else 0#64),
    %105 := .value (x 0), %106 := Ty.wrap #v[x 0, x 1], %107 := Ty.wrap #v[x 1, x 2]]

theorem sign_load_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (hr : SmallRange s.mem r 40)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 9 7 E s =
      .value (signLoadEnv E r byte (readLimbs s r), s) := by
  obtain ⟨e39,e100,e1,e5,e6,e7,e8,e12,e13,e14,e15,e16,e23,e24,e25⟩ := he
  have hmask : Operation.sub {nsw := true} (.value 0#64)
      (.value (byte.setWidth 64 >>> 7)) =
      .value (if byte[7] then (-1#64) else 0#64) := by
    simpa using sign_mask_operation byte
  have gr8 := hr.gep (k := 8) (by decide)
  have gr24 := hr.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at gr8 gr24
  have fscalar := Fits.mono (by decide : 64 ≤ 320) hr.fits
  have fr0 := hr.fits_add (k := 0) (count := 16) (by decide)
  have fr8 := hr.fits_add (k := 8) (count := 16) (by decide)
  have vr0 := smallRange_add hr (k := 0) (count := 16) (by decide)
  have vr8 := smallRange_add hr (k := 8) (count := 16) (by decide)
  simp only [Pointer.add_zero] at fr0 vr0
  change List.foldlM Instr.run E (((program.bb1 p).body.drop 9).take 7) s = _
  dsimp only [program.bb1, List.drop, List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,UnOp.compute,
    Operation.load,Operation.gepInboundsIndex,GepIndex.inboundsOffset,Operation.GepSignedRange,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_effect,
    e39,e100,e7,e8,e14,gr8,gr24,fscalar,fr0,fr8,vr0,vr8,load_two_words,
    Operation.zext,sign_mask_operation,hmask,throwUBIf,signLoadEnv,readLimbs,vector_two]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
