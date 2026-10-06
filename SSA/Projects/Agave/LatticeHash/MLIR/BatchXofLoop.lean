/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofOutput
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundAdapters8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundData
import SSA.Projects.Agave.LatticeHash.MLIR.RoundCore
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundSteps8

namespace AgaveLatticeHash.MLIR.BatchXofLoop
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open BatchReduction
abbrev RowTy : SLLVM.Ty := .arith (.vector 8 (.bitvec 32))
abbrev ExtraTypes : List SLLVM.Ty :=
  [RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy,
   RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, .ptr, SLLVM.Ty.bitvec 64]

/-- Values retained across all seven rounds of one root output block. -/
def extras (cv : CV Words8) (len flags : Words8) (outHigh : Pointer)
    (counter : Nat) : HVector TyDenote.toType ExtraTypes :=
  [(flags.map PoisonOr.value), (len.map PoisonOr.value),
   (cv 0).map PoisonOr.value, (cv 1).map PoisonOr.value,
   (cv 2).map PoisonOr.value, (cv 3).map PoisonOr.value,
   (cv 4).map PoisonOr.value, (cv 5).map PoisonOr.value,
   (cv 6).map PoisonOr.value, (cv 7).map PoisonOr.value,
   (cv 0).map PoisonOr.value, (cv 1).map PoisonOr.value,
   (cv 2).map PoisonOr.value, (cv 3).map PoisonOr.value,
   (cv 4).map PoisonOr.value, (cv 5).map PoisonOr.value,
   (cv 6).map PoisonOr.value, (cv 7).map PoisonOr.value,
   PoisonOr.value outHigh, PoisonOr.value (BitVec.ofNat 64 counter)]ₕ

def rootTarget (cv : CV Words8) (len flags : Words8) (outHigh : Pointer)
    (counter : Nat) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨22, rfl, [PoisonOr.value (BitVec.ofNat 64 counter),
   (flags.map PoisonOr.value), (len.map PoisonOr.value),
   (cv 0).map PoisonOr.value, (cv 1).map PoisonOr.value,
   (cv 2).map PoisonOr.value, (cv 3).map PoisonOr.value,
   (cv 4).map PoisonOr.value, (cv 5).map PoisonOr.value,
   (cv 6).map PoisonOr.value, (cv 7).map PoisonOr.value,
   (cv 0).map PoisonOr.value, (cv 1).map PoisonOr.value,
   (cv 2).map PoisonOr.value, (cv 3).map PoisonOr.value,
   (cv 4).map PoisonOr.value, (cv 5).map PoisonOr.value,
   (cv 6).map PoisonOr.value, (cv 7).map PoisonOr.value,
   PoisonOr.value outHigh]ₕ⟩

def roundTarget (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64)
    (v : State Words8) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨23, rfl, (CompressionRound.headerAt8 r v).args.append e⟩

def outputTarget (e : HVector TyDenote.toType ExtraTypes)
    (v : State Words8) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨24, rfl, e.append (CompressionRound.exitAt8 v).args⟩

noncomputable def rootVal (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (outHigh : Pointer) (counter : Nat) :
    BatchXof.Input22.Valuation :=
  Ctxt.Valuation.ofHVector (rootTarget cv len flags outHigh counter).args.reverse ++ B
noncomputable def roundVal (B : agave_batch_8.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64) (v : State Words8) :
    BatchRounds.Input8_23.Valuation :=
  Ctxt.Valuation.ofHVector (roundTarget e r v).args.reverse ++ B
noncomputable def outputVal (B : agave_batch_8.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (v : State Words8) : BatchOutput.Input8.Valuation :=
  Ctxt.Valuation.ofHVector (outputTarget e v).args.reverse ++ B

abbrev CarryCtx := Ctxt.ofList ExtraTypes.reverse ++ agave_batch_8.cfgCtx

def sourceAmbientVars : HVector CarryCtx.Var agave_compress_pre_8.cfgCtx.toList :=
  (⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨73, rfl⟩ ::ₕ
   ⟨49, rfl⟩ ::ₕ
   ⟨50, rfl⟩ ::ₕ
   ⟨51, rfl⟩ ::ₕ
   ⟨52, rfl⟩ ::ₕ
   ⟨53, rfl⟩ ::ₕ
   ⟨54, rfl⟩ ::ₕ
   ⟨55, rfl⟩ ::ₕ
   ⟨56, rfl⟩ ::ₕ
   ⟨57, rfl⟩ ::ₕ
   ⟨58, rfl⟩ ::ₕ
   ⟨59, rfl⟩ ::ₕ
   ⟨60, rfl⟩ ::ₕ
   ⟨61, rfl⟩ ::ₕ
   ⟨62, rfl⟩ ::ₕ
   ⟨63, rfl⟩ ::ₕ
   ⟨71, rfl⟩ ::ₕ
   ⟨64, rfl⟩ ::ₕ
   ⟨78, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨106, rfl⟩ ::ₕ
   ⟨107, rfl⟩ ::ₕ
   ⟨108, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨43, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ .nil)

def sourceAmbientMap : agave_compress_pre_8.cfgCtx.Hom CarryCtx :=
  fun _ x => sourceAmbientVars[x]

noncomputable def sourceVal (B : agave_batch_8.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) : agave_compress_pre_8.cfgCtx.Valuation :=
  (Ctxt.Valuation.ofHVector e.reverse ++ B).comap sourceAmbientMap

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- The typed round-body renaming respects the complete source input
valuation, with a fixed ambient context throughout the seven rounds. -/
theorem round_renaming (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (outHigh : Pointer) (counter : Nat)
    (r : BitVec 64) (v : State Words8) :
    (roundVal B (extras cv len flags outHigh counter) r v).comap BatchRounds.rename8_23 =
      Ctxt.Valuation.ofHVector (CompressionRound.headerAt8 r v).args.reverse ++
        sourceVal B (extras cv len flags outHigh counter) := by
  funext ty x
  have hx := x.val_lt
  rcases x with ⟨i, hi⟩
  change i < 86 at hx
  interval_cases i <;> cases hi <;> rfl

/-- Immutable constants used to initialize every root-output compression. -/
structure InitEnv (B : agave_batch_8.cfgCtx.Valuation) : Prop where
  zero64 : B ⟨65, rfl⟩ = PoisonOr.value 0#64
  zero32 : B ⟨61, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0#32)
  iv0 : B ⟨48, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0x6A09E667#32)
  iv1 : B ⟨47, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0xBB67AE85#32)
  iv2 : B ⟨46, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0x3C6EF372#32)
  iv3 : B ⟨45, rfl⟩ = Vector.replicate 8 (PoisonOr.value 0xA54FF53A#32)

def rootInitial (cv : CV Words8) (len flags : Words8) (counter : Nat) : State Words8 :=
  initState cv (Vector.replicate 8) (Vector.replicate 8 (BitVec.ofNat 32 counter))
    (Vector.replicate 8 0#32) len flags

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- The actual initialization successor is precisely the BLAKE3 initial
state, with the retained CV, root metadata, and this output block's counter. -/
theorem next22_initial (B : agave_batch_8.cfgCtx.Valuation) (hB : InitEnv B)
    (cv : CV Words8) (len flags : Words8) (outHigh : Pointer) (counter : Nat) :
    BatchXof.next22 (rootVal B cv len flags outHigh counter) counter =
      roundTarget (extras cv len flags outHigh counter) 0 (rootInitial cv len flags counter) := by
  have hz : (rootVal B cv len flags outHigh counter) ⟨85, rfl⟩ =
      PoisonOr.value 0#64 := hB.zero64
  have hh : (rootVal B cv len flags outHigh counter) ⟨81, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0#32) := hB.zero32
  have hi0 : (rootVal B cv len flags outHigh counter) ⟨68, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0x6A09E667#32) := hB.iv0
  have hi1 : (rootVal B cv len flags outHigh counter) ⟨67, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0xBB67AE85#32) := hB.iv1
  have hi2 : (rootVal B cv len flags outHigh counter) ⟨66, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0x3C6EF372#32) := hB.iv2
  have hi3 : (rootVal B cv len flags outHigh counter) ⟨65, rfl⟩ =
      Vector.replicate 8 (PoisonOr.value 0xA54FF53A#32) := hB.iv3
  unfold BatchXof.next22
  rw [hz, hh, hi0, hi1, hi2, hi3]
  congr 1
  apply HVector.ext
  intro i
  fin_cases i <;> first | rfl | exact Vector.map_replicate.symm

theorem output_env (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (outHigh : Pointer) (counter : Nat)
    (v : State Words8) :
    BatchXofOutput.Env (outputVal B (extras cv len flags outHigh counter) v) v cv := by
  constructor
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl

theorem output_backedge (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (outHigh : Pointer) (counter : Nat)
    (v : State Words8) :
    BatchOutput.next8 (outputVal B (extras cv len flags outHigh counter) v)
      (.value (BitVec.ofNat 64 (counter+1))) = rootTarget cv len flags outHigh (counter+1) := rfl

theorem adapt_header (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (outHigh : Pointer) (counter : Nat)
    (r r' : BitVec 64) (v v' : State Words8) :
    BatchRoundBranches.adapt8_23
      (roundVal B (extras cv len flags outHigh counter) r v)
      (CompressionRound.headerAt8 r' v') =
      roundTarget (extras cv len flags outHigh counter) r' v' := rfl

theorem adapt_exit (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (outHigh : Pointer) (counter : Nat)
    (r : BitVec 64) (v v' : State Words8) :
    BatchRoundBranches.adapt8_23
      (roundVal B (extras cv len flags outHigh counter) r v)
      (CompressionRound.exitAt8 v') =
      outputTarget (extras cv len flags outHigh counter) v' := rfl

noncomputable def continueBatch (B : agave_batch_8.cfgCtx.Valuation) :
    (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) →
      EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty))
  | .inl ret => pure ret
  | .inr t => agave_batch_8.blocks.run B t

/-- The round constants and source pointers do not depend on the XOF counter. -/
theorem sourceRound_env (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (outHigh msg sched : Pointer)
    (h : CompressionRound.RoundEnv8 (sourceVal B (extras cv len flags outHigh 0)) msg sched)
    (counter : Nat) :
    CompressionRound.RoundEnv8 (sourceVal B (extras cv len flags outHigh counter)) msg sched := by
  constructor
  · exact h.msg
  · exact h.sched
  · exact h.one
  · exact h.seven
  · exact h.off8
  · exact h.off16
  · exact h.off24
  · exact h.off32
  · exact h.off40
  · exact h.off48
  · exact h.off56
  · exact h.off64
  · exact h.off72
  · exact h.off80
  · exact h.off88
  · exact h.off96
  · exact h.off104
  · exact h.off112
  · exact h.off120
  · exact h.rot16
  · exact h.rot20
  · exact h.rot24
  · exact h.rot25

theorem run_step_continue (B : agave_batch_8.cfgCtx.Valuation)
    (t : SuccArgs agave_batch_8.cfgSigs) :
    agave_batch_8.blocks.run B t =
      ((agave_batch_8.blocks.get t.idx t.hidx).2.denote
        (Ctxt.Valuation.ofHVector t.args.reverse ++ B) >>= fun z => continueBatch B z.2) := by
  rw [Blocks.run_step]
  congr 1
  funext z
  rcases z with ⟨a, b⟩
  cases b <;> rfl

/-- One actual batch round, including the schedule and message memory reads,
advances the state while preserving every retained root-output value. -/
theorem round_run (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (outHigh msg sched : Pointer) (counter : Nat)
    (hA : CompressionRound.RoundEnv8 (sourceVal B (extras cv len flags outHigh counter)) msg sched)
    (s : GlobalState) (r : Fin 7) (v m : State Words8)
    (hsi : ∀ i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64)
    (hsv : ∀ i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (CompressionRound.messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (CompressionRound.messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_8.blocks.run B
      (roundTarget (extras cv len flags outHigh counter) (BitVec.ofNat 64 r.val) v)) s =
      StateT.run (agave_batch_8.blocks.run B
        (if r.val = 6 then outputTarget (extras cv len flags outHigh counter) (roundFn gVectors v m r)
         else roundTarget (extras cv len flags outHigh counter) (BitVec.ofNat 64 (r.val+1))
           (roundFn gVectors v m r))) s := by
  rw [run_step_continue]
  denote_reduce_get
  change StateT.run (agave_batch_8.cfgBlock_23.denote
    (roundVal B (extras cv len flags outHigh counter) (BitVec.ofNat 64 r.val) v) >>=
      fun z => continueBatch B z.2) s = _
  rw [BatchRoundBranches.block8_23_round (continueBatch B)
    (roundVal B (extras cv len flags outHigh counter) (BitVec.ofNat 64 r.val) v)
    (sourceVal B (extras cv len flags outHigh counter)) msg sched hA s r v m
    (round_renaming B cv len flags outHigh counter (BitVec.ofNat 64 r.val) v)
    hsi hsv hmi hmv]
  by_cases hr : r.val = 6 <;>
    simp only [hr, reduceIte, adapt_exit, adapt_header, continueBatch]

set_option maxRecDepth 4096 in
/-- Seven executions of the actual inlined round block reach the output
block with the exact BLAKE3 compression state and unchanged memory. -/
theorem seven_rounds_run (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (outHigh msg sched : Pointer) (counter : Nat)
    (hA : CompressionRound.RoundEnv8 (sourceVal B (extras cv len flags outHigh counter)) msg sched)
    (s : GlobalState) (initial m : State Words8)
    (hsi : ∀ r i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (CompressionRound.messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (CompressionRound.messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_8.blocks.run B
      (roundTarget (extras cv len flags outHigh counter) 0 initial)) s =
      StateT.run (agave_batch_8.blocks.run B
        (outputTarget (extras cv len flags outHigh counter) (sevenRounds gVectors initial m))) s := by
  let s1 := roundFn gVectors initial m 0
  let s2 := roundFn gVectors s1 m 1
  let s3 := roundFn gVectors s2 m 2
  let s4 := roundFn gVectors s3 m 3
  let s5 := roundFn gVectors s4 m 4
  let s6 := roundFn gVectors s5 m 5
  let s7 := roundFn gVectors s6 m 6
  calc
    _ = StateT.run (agave_batch_8.blocks.run B
      (roundTarget (extras cv len flags outHigh counter) 1 s1)) s :=
      round_run B cv len flags outHigh msg sched counter hA s 0 initial m (hsi 0) (hsv 0) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
      (roundTarget (extras cv len flags outHigh counter) 2 s2)) s :=
      round_run B cv len flags outHigh msg sched counter hA s 1 s1 m (hsi 1) (hsv 1) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
      (roundTarget (extras cv len flags outHigh counter) 3 s3)) s :=
      round_run B cv len flags outHigh msg sched counter hA s 2 s2 m (hsi 2) (hsv 2) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
      (roundTarget (extras cv len flags outHigh counter) 4 s4)) s :=
      round_run B cv len flags outHigh msg sched counter hA s 3 s3 m (hsi 3) (hsv 3) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
      (roundTarget (extras cv len flags outHigh counter) 5 s5)) s :=
      round_run B cv len flags outHigh msg sched counter hA s 4 s4 m (hsi 4) (hsv 4) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
      (roundTarget (extras cv len flags outHigh counter) 6 s6)) s :=
      round_run B cv len flags outHigh msg sched counter hA s 5 s5 m (hsi 5) (hsv 5) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
      (outputTarget (extras cv len flags outHigh counter) s7)) s :=
      round_run B cv len flags outHigh msg sched counter hA s 6 s6 m (hsi 6) (hsv 6) hmi hmv
    _ = _ := rfl

/-- Scalar constants and output base captured by the actual batch entry. -/
structure OutputEnv (B : agave_batch_8.cfgCtx.Valuation) (out : Pointer) : Prop where
  outPtr : B ⟨97, rfl⟩ = PoisonOr.value out
  shift : B ⟨54, rfl⟩ = PoisonOr.value 6#64
  one : B ⟨58, rfl⟩ = PoisonOr.value 1#64
  limit : B ⟨88, rfl⟩ = PoisonOr.value 32#64

def outputPtr (out : Pointer) (counter : Nat) : Pointer :=
  out.withOffset (BitVec.ofNat 64 (64*counter))

def finalState (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (counter : Nat) : State Words8 :=
  sevenRounds gVectors (rootInitial cv len flags counter) m

def lowerDelta (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (counter : Nat) : Vector (BitVec 16) 16 :=
  columnSum (BatchXofOutput.lowerColumns (finalState cv len flags m counter) cv)
def upperDelta (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (counter : Nat) : Vector (BitVec 16) 16 :=
  columnSum (BatchXofOutput.upperColumns (finalState cv len flags m counter) cv)

private theorem counterHalves (counter : Nat) (hc : counter < 32) :
    (BitVec.ofNat 64 counter).extractLsb' 0 32 = BitVec.ofNat 32 counter ∧
    (BitVec.ofNat 64 counter).extractLsb' 32 32 = 0#32 := by
  interval_cases counter <;> decide +kernel

theorem rootInitial_lane (cv : CV Words8) (len flags : Words8) (counter : Nat)
    (hc : counter < 32) (lane : Fin 8) :
    (fun i => (rootInitial cv len flags counter i)[lane]) =
      scalarInit (fun i => (cv i)[lane]) (BitVec.ofNat 64 counter) len[lane] flags[lane] := by
  obtain ⟨hl, hh⟩ := counterHalves counter hc
  funext i
  fin_cases i <;> simp [rootInitial, initState, scalarInit, hl, hh]

/-- Every final vector word is the scalar BLAKE3 compression word for that
message lane and the actual root-output counter. -/
theorem finalState_lane (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (counter : Nat) (hc : counter < 32) (lane : Fin 8) :
    (fun i => (finalState cv len flags m counter i)[lane]) =
      scalarCompressPre (fun i => (cv i)[lane]) (fun i => (m i)[lane])
        (BitVec.ofNat 64 counter) len[lane] flags[lane] := by
  unfold finalState sevenRounds
  rw [rounds_vectors_lane, rootInitial_lane cv len flags counter hc lane]
  rfl

theorem lowerDelta_scalar (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (counter : Nat) (hc : counter < 32) (half : Fin 16) :
    (lowerDelta cv len flags m counter)[half] = sum8 (fun lane =>
      AgaveLattice.halfWord
        (scalarCompress (fun i => (cv i)[lane]) (fun i => (m i)[lane])
          (BitVec.ofNat 64 counter) len[lane] flags[lane] ⟨half.val / 2, by omega⟩)
        ⟨half.val % 2, by omega⟩) := by
  rw [lowerDelta, BatchXofOutput.lower_scalar_sum]
  apply congrArg sum8
  funext lane
  rw [finalState_lane cv len flags m counter hc lane]
  rfl

theorem upperDelta_scalar (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (counter : Nat) (hc : counter < 32) (half : Fin 16) :
    (upperDelta cv len flags m counter)[half] = sum8 (fun lane =>
      AgaveLattice.halfWord
        (scalarCompress (fun i => (cv i)[lane]) (fun i => (m i)[lane])
          (BitVec.ofNat 64 counter) len[lane] flags[lane] ⟨half.val / 2 + 8, by omega⟩)
        ⟨half.val % 2, by omega⟩) := by
  rw [upperDelta, BatchXofOutput.upper_scalar_sum]
  apply congrArg sum8
  funext lane
  rw [finalState_lane cv len flags m counter hc lane]
  rfl

/-- The two concrete accumulator writes performed for one counter. -/
def accumulate (s : GlobalState) (out outHigh : Pointer) (counter : Nat)
    (lo hi dlo dhi : Vector (BitVec 16) 16) : GlobalState :=
  {s with mem := (s.mem.splice (outputPtr out counter) (packBits (BatchOutput.sums16 lo dlo))).splice (outputPtr outHigh counter) (packBits (BatchOutput.sums16 hi dhi))}

private theorem byteGep (p : Pointer) (off : BitVec 64) :
    gep (.value p) 1 0 (.value off) = .value (p.withOffset off) := by
  simp [gep, ptradd, Pointer.withOffset, LLVM.add, LLVM.mul,
    LLVM.const?, LLVM.add?, LLVM.mul?]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- One output-block execution feeds the scalar sums into the actual two
memory writes, then follows the actual counter branch. -/
theorem output_run (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (out outHigh : Pointer)
    (hB : OutputEnv B out) (counter : Nat) (hc : counter < 32)
    (s : GlobalState) (v : State Words8) (lo hi : Vector (BitVec 16) 16)
    (flo : Fits s.mem (outputPtr out counter) 256)
    (fhi : Fits s.mem (outputPtr outHigh counter) 256)
    (rlo : readWord? (outputPtr out counter) 256 s.mem = some (packBits lo))
    (rhi : readWord? (outputPtr outHigh counter) 256 s.mem = some (packBits hi))
    (hdisj : (outputPtr out counter).offsetInBits + 256 ≤ (outputPtr outHigh counter).offsetInBits ∨
      (outputPtr outHigh counter).offsetInBits + 256 ≤ (outputPtr out counter).offsetInBits) :
    StateT.run (agave_batch_8.blocks.run B
      (outputTarget (extras cv len flags outHigh counter) v)) s =
      StateT.run (agave_batch_8.blocks.run B
        (if counter = 31 then ⟨25, rfl, .nil⟩ else rootTarget cv len flags outHigh (counter+1)))
        (accumulate s out outHigh counter lo hi
          (columnSum (BatchXofOutput.lowerColumns v cv))
          (columnSum (BatchXofOutput.upperColumns v cv))) := by
  let V := outputVal B (extras cv len flags outHigh counter) v
  have hptr : V ⟨133, rfl⟩ = PoisonOr.value out := hB.outPtr
  have hloPtr : gep (V ⟨133, rfl⟩) 1 0 (.value (BitVec.ofNat 64 (64*counter))) =
      .value (outputPtr out counter) := by rw [hptr]; exact byteGep _ _
  have hhiPtr : gep (V ⟨17, rfl⟩) 1 0 (.value (BitVec.ofNat 64 (64*counter))) =
      .value (outputPtr outHigh counter) := byteGep _ _
  have h : StateT.run (agave_batch_8.cfgBlock_24.denote V >>= fun z => continueBatch B z.2) s =
      StateT.run (agave_batch_8.blocks.run B
        (if counter = 31 then ⟨25, rfl, .nil⟩ else rootTarget cv len flags outHigh (counter+1)))
        (accumulate s out outHigh counter lo hi
          (columnSum (BatchXofOutput.lowerColumns v cv))
          (columnSum (BatchXofOutput.upperColumns v cv))) := by
    rw [BatchOutput.output8_continue, EffectM.run_bind]
    rw [BatchOutput.output8Spec_run V s counter hc (outputPtr out counter) (outputPtr outHigh counter)
      lo hi (columnSum (BatchXofOutput.lowerColumns v cv)) (columnSum (BatchXofOutput.upperColumns v cv))
      (by rfl) hB.shift hB.one hB.limit hloPtr hhiPtr
      (BatchXofOutput.lower_defined V v cv (output_env B cv len flags outHigh counter v))
      (BatchXofOutput.upper_defined V v cv (output_env B cv len flags outHigh counter v))
      flo fhi rlo rhi hdisj]
    simp only [PoisonOr.value_bind]
    by_cases he : counter = 31 <;> simp only [he, reduceIte, continueBatch]
      <;> rfl

  rw [run_step_continue]
  denote_reduce_get
  exact h

/-- Memory preconditions for one actual output iteration. These assert
valid reads and disjoint accumulator halves, not any execution result. -/
structure IterationMemory (s : GlobalState) (out outHigh msg sched : Pointer)
    (counter : Nat) (m : State Words8) (lo hi : Vector (BitVec 16) 16) : Prop where
  scheduleFits : ∀ r i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64
  scheduleRead : ∀ r i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
    some (BitVec.ofNat 64 (schedule r i).val)
  messageFits : ∀ i, Fits s.mem (CompressionRound.messagePtr8 msg i) 256
  messageRead : ∀ i, readWord? (CompressionRound.messagePtr8 msg i) 256 s.mem = some (packBits (m i))
  lowerFits : Fits s.mem (outputPtr out counter) 256
  upperFits : Fits s.mem (outputPtr outHigh counter) 256
  lowerRead : readWord? (outputPtr out counter) 256 s.mem = some (packBits lo)
  upperRead : readWord? (outputPtr outHigh counter) 256 s.mem = some (packBits hi)
  separate : (outputPtr out counter).offsetInBits + 256 ≤ (outputPtr outHigh counter).offsetInBits ∨
    (outputPtr outHigh counter).offsetInBits + 256 ≤ (outputPtr out counter).offsetInBits

/-- One complete actual XOF iteration: initialization, seven rounds,
feed-forward, two memory writes, and the emitted counter branch. -/
theorem iteration_run (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (out outHigh msg sched : Pointer)
    (hInit : InitEnv B) (hOut : OutputEnv B out) (counter : Nat) (hc : counter < 32)
    (hRound : CompressionRound.RoundEnv8 (sourceVal B (extras cv len flags outHigh counter)) msg sched)
    (s : GlobalState) (m : State Words8) (lo hi : Vector (BitVec 16) 16)
    (hmem : IterationMemory s out outHigh msg sched counter m lo hi) :
    StateT.run (agave_batch_8.blocks.run B (rootTarget cv len flags outHigh counter)) s =
      StateT.run (agave_batch_8.blocks.run B
        (if counter = 31 then ⟨25, rfl, .nil⟩ else rootTarget cv len flags outHigh (counter+1)))
        (accumulate s out outHigh counter lo hi
          (lowerDelta cv len flags m counter) (upperDelta cv len flags m counter)) := by
  rw [run_step_continue]
  denote_reduce_get
  change StateT.run (agave_batch_8.cfgBlock_22.denote (rootVal B cv len flags outHigh counter) >>=
    fun z => continueBatch B z.2) s = _
  rw [BatchXof.block22_continue (rootVal B cv len flags outHigh counter) s counter hc
    (by rfl) hInit.zero64 (continueBatch B)]
  change StateT.run (agave_batch_8.blocks.run B
    (BatchXof.next22 (rootVal B cv len flags outHigh counter) counter)) s = _
  rw [next22_initial B hInit]
  rw [seven_rounds_run B cv len flags outHigh msg sched counter hRound s
    (rootInitial cv len flags counter) m hmem.scheduleFits hmem.scheduleRead hmem.messageFits hmem.messageRead]
  exact output_run B cv len flags out outHigh hOut counter hc s
    (finalState cv len flags m counter) lo hi hmem.lowerFits hmem.upperFits
    hmem.lowerRead hmem.upperRead hmem.separate

/-- Accumulator memory after the first `count` root-output blocks.
Each block stores the previous accumulator values plus eight scalar
message contributions, independently modulo 2^16 in every half-word. -/
def accumulatedState (s : GlobalState) (out outHigh : Pointer)
    (cv : CV Words8) (len flags : Words8) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16) : Nat → GlobalState
  | 0 => s
  | c+1 => accumulate (accumulatedState s out outHigh cv len flags m lo hi c)
      out outHigh c (lo c) (hi c) (lowerDelta cv len flags m c) (upperDelta cv len flags m c)

theorem exit_run (B : agave_batch_8.cfgCtx.Valuation) (s : GlobalState) :
    StateT.run (agave_batch_8.blocks.run B ⟨25, rfl, .nil⟩) s = .value (.nil, s) := by
  rw [run_step_continue]
  denote_reduce_get
  change StateT.run (agave_batch_8.cfgBlock_25.denote B >>= fun z => continueBatch B z.2) s = _
  simp only [agave_batch_8.cfgBlock_25, BlockCom.run_bind_denote_lifetime]
  rfl

/-- The actual compiler CFG performs all thirty-two XOF output iterations
and exits normally. Memory premises concern the explicit successive stores;
no premise assumes compression correctness or a CFG execution outcome. -/
theorem xof32_run (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (out outHigh msg sched : Pointer)
    (hInit : InitEnv B) (hOut : OutputEnv B out) (s : GlobalState) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16)
    (hRound : ∀ c, c < 32 → CompressionRound.RoundEnv8
      (sourceVal B (extras cv len flags outHigh c)) msg sched)
    (hMem : ∀ c, c < 32 → IterationMemory
      (accumulatedState s out outHigh cv len flags m lo hi c)
      out outHigh msg sched c m (lo c) (hi c)) :
    StateT.run (agave_batch_8.blocks.run B (rootTarget cv len flags outHigh 0)) s =
      .value (.nil, accumulatedState s out outHigh cv len flags m lo hi 32) := by
  have loop : ∀ n c, c + n = 32 → c < 32 →
      StateT.run (agave_batch_8.blocks.run B (rootTarget cv len flags outHigh c))
        (accumulatedState s out outHigh cv len flags m lo hi c) =
        .value (.nil, accumulatedState s out outHigh cv len flags m lo hi 32) := by
    intro n
    induction n with
    | zero => intro c hn hc; omega
    | succ n ih =>
      intro c hn hc
      rw [iteration_run B cv len flags out outHigh msg sched hInit hOut c hc (hRound c hc)
        (accumulatedState s out outHigh cv len flags m lo hi c) m (lo c) (hi c) (hMem c hc)]
      change StateT.run (agave_batch_8.blocks.run B
        (if c = 31 then ⟨25, rfl, .nil⟩ else rootTarget cv len flags outHigh (c+1)))
        (accumulatedState s out outHigh cv len flags m lo hi (c+1)) = _
      by_cases he : c = 31
      · subst c
        simpa only [reduceIte] using exit_run B
          (accumulatedState s out outHigh cv len flags m lo hi 32)
      · simp only [he, reduceIte]
        exact ih (c+1) (by omega) (by omega)
  exact loop 32 0 rfl (by decide)

/-- Entry form requiring the captured round environment only once. -/
theorem xof32_run_fixedEnv (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV Words8) (len flags : Words8) (out outHigh msg sched : Pointer)
    (hInit : InitEnv B) (hOut : OutputEnv B out) (s : GlobalState) (m : State Words8)
    (lo hi : Nat → Vector (BitVec 16) 16)
    (hRound : CompressionRound.RoundEnv8 (sourceVal B (extras cv len flags outHigh 0)) msg sched)
    (hMem : ∀ c, c < 32 → IterationMemory
      (accumulatedState s out outHigh cv len flags m lo hi c)
      out outHigh msg sched c m (lo c) (hi c)) :
    StateT.run (agave_batch_8.blocks.run B (rootTarget cv len flags outHigh 0)) s =
      .value (.nil, accumulatedState s out outHigh cv len flags m lo hi 32) := by
  exact xof32_run B cv len flags out outHigh msg sched hInit hOut s m lo hi
    (fun c _ => sourceRound_env B cv len flags outHigh msg sched hRound c) hMem

end AgaveLatticeHash.MLIR.BatchXofLoop
