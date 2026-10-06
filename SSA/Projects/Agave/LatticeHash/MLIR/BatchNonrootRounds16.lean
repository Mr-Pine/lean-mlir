/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchPaths16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchUpdate16Refinement
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundSteps16
namespace AgaveLatticeHash.MLIR.BatchNonrootRounds16
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open CompressionRound
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.auxLemma false
abbrev Words16 := Vector Word 16
abbrev ExtraTypes : List SLLVM.Ty :=
  [SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 8))]

def roundTarget (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64)
    (v : State Words16) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨7, rfl, (CompressionRound.headerAt16 r v).args.append e⟩

def updateTarget (e : HVector TyDenote.toType ExtraTypes)
    (v : State Words16) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨8, rfl, e.append (CompressionRound.exitAt16 v).args⟩

noncomputable def roundVal (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64) (v : State Words16) :
    BatchRounds.Input16_7.Valuation :=
  Ctxt.Valuation.ofHVector (roundTarget e r v).args.reverse ++ B

noncomputable def updateVal (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (v : State Words16) :
    BatchUpdate16.Input16.Valuation :=
  Ctxt.Valuation.ofHVector (updateTarget e v).args.reverse ++ B

/-- Unused standalone bindings can depend on the current phi state. Its used
bindings are all immutable batch-entry values, as `sourceEnv_change` proves. -/
noncomputable def sourceVal (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64) (v : State Words16) :
    agave_compress_pre_16.cfgCtx.Valuation :=
  fun _ x => ((roundVal B e r v).comap BatchRounds.rename16_7) (x.appendInr (Γ := Ctxt.ofList (CompressionRound.headerAt16 r v).ts.reverse))

theorem round_renaming (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (r : BitVec 64) (v : State Words16) :
    (roundVal B e r v).comap BatchRounds.rename16_7 =
      Ctxt.Valuation.ofHVector (CompressionRound.headerAt16 r v).args.reverse ++
        sourceVal B e r v := by
  cases e
  rename_i a0 e
  cases e
  rename_i a1 e
  cases e
  rename_i a2 e
  cases e
  rename_i a3 e
  cases e
  rename_i a4 e
  cases e
  rename_i a5 e
  cases e
  rename_i a6 e
  cases e
  rename_i a7 e
  cases e
  rename_i a8 e
  cases e
  rename_i a9 e
  cases e
  rename_i a10 e
  cases e
  rename_i a11 e
  cases e
  rename_i a12 e
  cases e
  rename_i a13 e
  cases e
  rename_i a14 e
  cases e
  rename_i a15 e
  cases e
  rename_i a16 e
  cases e
  rename_i a17 e
  cases e
  rename_i a18 e
  cases e
  rename_i a19 e
  cases e
  rename_i a20 e
  cases e
  rename_i a21 e
  cases e
  rename_i a22 e
  cases e
  rename_i a23 e
  cases e
  rename_i a24 e
  cases e
  rename_i a25 e
  cases e
  rename_i a26 e
  cases e
  funext ty x
  cases x using Ctxt.Var.appendCases
      (Γ := Ctxt.ofList (CompressionRound.headerAt16 r v).ts.reverse)
      (Δ := agave_compress_pre_16.cfgCtx) with
  | left x =>
    rw [Ctxt.Valuation.append_appendInl]
    have hx := x.val_lt
    rcases x with ⟨i, hi⟩
    change i < 17 at hx
    interval_cases i <;> cases hi <;> rfl
  | right x =>
    rw [Ctxt.Valuation.append_appendInr]
    rfl

theorem sourceEnv_change (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (r r' : BitVec 64) (v v' : State Words16) (msg sched : Pointer)
    (h : RoundEnv16 (sourceVal B e r v) msg sched) :
    RoundEnv16 (sourceVal B e r' v') msg sched := by
  exact ⟨h.msg, h.sched, h.one, h.seven, h.off8, h.off16, h.off24, h.off32,
    h.off40, h.off48, h.off56, h.off64, h.off72, h.off80, h.off88, h.off96,
    h.off104, h.off112, h.off120, h.rot16, h.rot20, h.rot24, h.rot25⟩

theorem adapt_header (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (r r' : BitVec 64) (v v' : State Words16) :
    BatchRoundBranches.adapt16_7 (roundVal B e r v)
      (CompressionRound.headerAt16 r' v') = roundTarget e r' v' := by
  cases e
  rename_i a0 e
  cases e
  rename_i a1 e
  cases e
  rename_i a2 e
  cases e
  rename_i a3 e
  cases e
  rename_i a4 e
  cases e
  rename_i a5 e
  cases e
  rename_i a6 e
  cases e
  rename_i a7 e
  cases e
  rename_i a8 e
  cases e
  rename_i a9 e
  cases e
  rename_i a10 e
  cases e
  rename_i a11 e
  cases e
  rename_i a12 e
  cases e
  rename_i a13 e
  cases e
  rename_i a14 e
  cases e
  rename_i a15 e
  cases e
  rename_i a16 e
  cases e
  rename_i a17 e
  cases e
  rename_i a18 e
  cases e
  rename_i a19 e
  cases e
  rename_i a20 e
  cases e
  rename_i a21 e
  cases e
  rename_i a22 e
  cases e
  rename_i a23 e
  cases e
  rename_i a24 e
  cases e
  rename_i a25 e
  cases e
  rename_i a26 e
  cases e
  rfl

theorem adapt_exit (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (r : BitVec 64) (v v' : State Words16) :
    BatchRoundBranches.adapt16_7 (roundVal B e r v)
      (CompressionRound.exitAt16 v') = updateTarget e v' := by
  cases e
  rename_i a0 e
  cases e
  rename_i a1 e
  cases e
  rename_i a2 e
  cases e
  rename_i a3 e
  cases e
  rename_i a4 e
  cases e
  rename_i a5 e
  cases e
  rename_i a6 e
  cases e
  rename_i a7 e
  cases e
  rename_i a8 e
  cases e
  rename_i a9 e
  cases e
  rename_i a10 e
  cases e
  rename_i a11 e
  cases e
  rename_i a12 e
  cases e
  rename_i a13 e
  cases e
  rename_i a14 e
  cases e
  rename_i a15 e
  cases e
  rename_i a16 e
  cases e
  rename_i a17 e
  cases e
  rename_i a18 e
  cases e
  rename_i a19 e
  cases e
  rename_i a20 e
  cases e
  rename_i a21 e
  cases e
  rename_i a22 e
  cases e
  rename_i a23 e
  cases e
  rename_i a24 e
  cases e
  rename_i a25 e
  cases e
  rename_i a26 e
  cases e
  rfl

noncomputable def continueBatch (B : agave_batch_16.cfgCtx.Valuation)
    (r : HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) :
    EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty)) :=
  Blocks.force_limit_next.match_1 (fun _ => EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty))) r
    (fun ret => pure ret) (fun t => agave_batch_16.blocks.run B t)

attribute [local irreducible] BlockCom.denote Blocks.run

/-- One actual batch round preserves the saved CV, both offset vectors, and
active-lane mask while advancing the BLAKE3 state. -/
theorem round_run (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (msg sched : Pointer) (seed : State Words16)
    (hA : RoundEnv16 (sourceVal B e 0 seed) msg sched)
    (s : GlobalState) (r : Fin 7) (v m : State Words16)
    (hsi : ∀ i, Fits s.mem (schedulePtr16 sched r i) 64)
    (hsv : ∀ i, readWord? (schedulePtr16 sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr16 msg i) 512)
    (hmv : ∀ i, readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_16.blocks.run B
      (roundTarget e (BitVec.ofNat 64 r.val) v)) s =
      StateT.run (agave_batch_16.blocks.run B
        (if r.val = 6 then updateTarget e (roundFn gVectors v m r)
         else roundTarget e (BitVec.ofNat 64 (r.val+1))
           (roundFn gVectors v m r))) s := by
  denote_enter_block
  change StateT.run (agave_batch_16.cfgBlock_7.denote
    (roundVal B e (BitVec.ofNat 64 r.val) v) >>=
      fun z => continueBatch B z.2) s = _
  rw [BatchRoundBranches.block16_7_round (continueBatch B)
    (roundVal B e (BitVec.ofNat 64 r.val) v)
    (sourceVal B e (BitVec.ofNat 64 r.val) v)
    msg sched
    (sourceEnv_change B e 0 (BitVec.ofNat 64 r.val) seed v msg sched hA)
    s r v m (round_renaming B e (BitVec.ofNat 64 r.val) v)
    hsi hsv hmi hmv]
  by_cases hr : r.val = 6 <;>
    simp only [hr, reduceIte, adapt_exit, adapt_header, continueBatch]

/-- All seven rounds of the actual nonroot loop reach the actual CV-update
block, with the exact vector BLAKE3 state and every retained value unchanged. -/
theorem seven_rounds_run (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (msg sched : Pointer) (seed m : State Words16)
    (hA : RoundEnv16 (sourceVal B e 0 seed) msg sched)
    (s : GlobalState)
    (hsi : ∀ r i, Fits s.mem (schedulePtr16 sched r i) 64)
    (hsv : ∀ r i, readWord? (schedulePtr16 sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr16 msg i) 512)
    (hmv : ∀ i, readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_16.blocks.run B (roundTarget e 0 seed)) s =
      StateT.run (agave_batch_16.blocks.run B
        (updateTarget e (sevenRounds gVectors seed m))) s := by
  let s1 := roundFn gVectors seed m 0
  let s2 := roundFn gVectors s1 m 1
  let s3 := roundFn gVectors s2 m 2
  let s4 := roundFn gVectors s3 m 3
  let s5 := roundFn gVectors s4 m 4
  let s6 := roundFn gVectors s5 m 5
  let s7 := roundFn gVectors s6 m 6
  calc
    StateT.run (agave_batch_16.blocks.run B (roundTarget e 0 seed)) s = StateT.run (agave_batch_16.blocks.run B
        (roundTarget e 1 s1)) s :=
      round_run B e msg sched seed hA s 0 seed m (hsi 0) (hsv 0) hmi hmv
    _ = StateT.run (agave_batch_16.blocks.run B
        (roundTarget e 2 s2)) s :=
      round_run B e msg sched seed hA s 1 s1 m (hsi 1) (hsv 1) hmi hmv
    _ = StateT.run (agave_batch_16.blocks.run B
        (roundTarget e 3 s3)) s :=
      round_run B e msg sched seed hA s 2 s2 m (hsi 2) (hsv 2) hmi hmv
    _ = StateT.run (agave_batch_16.blocks.run B
        (roundTarget e 4 s4)) s :=
      round_run B e msg sched seed hA s 3 s3 m (hsi 3) (hsv 3) hmi hmv
    _ = StateT.run (agave_batch_16.blocks.run B
        (roundTarget e 5 s5)) s :=
      round_run B e msg sched seed hA s 4 s4 m (hsi 4) (hsv 4) hmi hmv
    _ = StateT.run (agave_batch_16.blocks.run B
        (roundTarget e 6 s6)) s :=
      round_run B e msg sched seed hA s 5 s5 m (hsi 5) (hsv 5) hmi hmv
    _ = StateT.run (agave_batch_16.blocks.run B
        (updateTarget e s7)) s :=
      round_run B e msg sched seed hA s 6 s6 m (hsi 6) (hsv 6) hmi hmv
    _ = StateT.run (agave_batch_16.blocks.run B
        (updateTarget e (sevenRounds gVectors seed m))) s := rfl

end AgaveLatticeHash.MLIR.BatchNonrootRounds16
