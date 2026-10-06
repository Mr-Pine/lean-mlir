/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchNonrootData8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundSteps8
namespace AgaveLatticeHash.MLIR.BatchNonrootRounds8
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open CompressionRound
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.auxLemma false

theorem round_renaming_general (B : agave_batch_8.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (r : BitVec 64) (v : State Words8) :
    (roundVal B e r v).comap BatchRounds.rename8_20 =
      Ctxt.Valuation.ofHVector (CompressionRound.headerAt8 r v).args.reverse ++
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
  funext ty x
  cases x using Ctxt.Var.appendCases
      (Γ := Ctxt.ofList (CompressionRound.headerAt8 r v).ts.reverse)
      (Δ := agave_compress_pre_8.cfgCtx) with
  | left x =>
    rw [Ctxt.Valuation.append_appendInl]
    have hx := x.val_lt
    rcases x with ⟨i, hi⟩
    change i < 17 at hx
    interval_cases i <;> cases hi <;> rfl
  | right x =>
    rw [Ctxt.Valuation.append_appendInr]
    rfl

theorem round_renaming (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool)
    (r : BitVec 64) (v : State Words8) :
    (roundVal B (extras cv offsets advanced active) r v).comap BatchRounds.rename8_20 =
      Ctxt.Valuation.ofHVector (CompressionRound.headerAt8 r v).args.reverse ++
        sourceVal B (extras cv offsets advanced active) r v :=
  round_renaming_general B (extras cv offsets advanced active) r v

theorem sourceEnv_change_general (B : agave_batch_8.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (r r' : BitVec 64) (v v' : State Words8) (msg sched : Pointer)
    (h : RoundEnv8 (sourceVal B e r v) msg sched) :
    RoundEnv8 (sourceVal B e r' v') msg sched := by
  rcases e with ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, _⟩
  exact ⟨h.msg, h.sched, h.one, h.seven, h.off8, h.off16, h.off24, h.off32,
    h.off40, h.off48, h.off56, h.off64, h.off72, h.off80, h.off88, h.off96,
    h.off104, h.off112, h.off120, h.rot16, h.rot20, h.rot24, h.rot25⟩

theorem sourceEnv_change (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool)
    (r r' : BitVec 64) (v v' : State Words8) (msg sched : Pointer)
    (h : RoundEnv8 (sourceVal B (extras cv offsets advanced active) r v) msg sched) :
    RoundEnv8 (sourceVal B (extras cv offsets advanced active) r' v') msg sched :=
  sourceEnv_change_general B (extras cv offsets advanced active) r r' v v' msg sched h

noncomputable def continueBatch (B : agave_batch_8.cfgCtx.Valuation)
    (r : HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) :
    EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty)) :=
  Blocks.force_limit_next.match_1 (fun _ => EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty))) r
    (fun ret => pure ret) (fun t => agave_batch_8.blocks.run B t)

attribute [local irreducible] BlockCom.denote Blocks.run

/-- One actual batch round preserves the saved CV, both offset vectors, and
active-lane mask while advancing the BLAKE3 state. -/
theorem round_run (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool)
    (msg sched : Pointer) (seed : State Words8)
    (hA : RoundEnv8 (sourceVal B (extras cv offsets advanced active) 0 seed) msg sched)
    (s : GlobalState) (r : Fin 7) (v m : State Words8)
    (hsi : ∀ i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64)
    (hsv : ∀ i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (CompressionRound.messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (CompressionRound.messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_8.blocks.run B
      (roundTarget (extras cv offsets advanced active) (BitVec.ofNat 64 r.val) v)) s =
      StateT.run (agave_batch_8.blocks.run B
        (if r.val = 6 then updateTarget (extras cv offsets advanced active) (roundFn gVectors v m r)
         else roundTarget (extras cv offsets advanced active) (BitVec.ofNat 64 (r.val+1))
           (roundFn gVectors v m r))) s := by
  denote_enter_block
  change StateT.run (agave_batch_8.cfgBlock_20.denote
    (roundVal B (extras cv offsets advanced active) (BitVec.ofNat 64 r.val) v) >>=
      fun z => continueBatch B z.2) s = _
  rw [BatchRoundBranches.block8_20_round (continueBatch B)
    (roundVal B (extras cv offsets advanced active) (BitVec.ofNat 64 r.val) v)
    (sourceVal B (extras cv offsets advanced active) (BitVec.ofNat 64 r.val) v)
    msg sched
    (sourceEnv_change B cv offsets advanced active 0 (BitVec.ofNat 64 r.val) seed v msg sched hA)
    s r v m (round_renaming B cv offsets advanced active (BitVec.ofNat 64 r.val) v)
    hsi hsv hmi hmv]
  by_cases hr : r.val = 6 <;>
    simp only [hr, reduceIte, adapt_exit, adapt_header, continueBatch]

/-- All seven rounds of the actual nonroot loop reach the actual CV-update
block, with the exact vector BLAKE3 state and every retained value unchanged. -/
theorem seven_rounds_run (B : agave_batch_8.cfgCtx.Valuation)
    (cv : CV (Lanes 8)) (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool)
    (msg sched : Pointer) (seed m : State Words8)
    (hA : RoundEnv8 (sourceVal B (extras cv offsets advanced active) 0 seed) msg sched)
    (s : GlobalState)
    (hsi : ∀ r i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (CompressionRound.messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (CompressionRound.messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_8.blocks.run B (roundTarget (extras cv offsets advanced active) 0 seed)) s =
      StateT.run (agave_batch_8.blocks.run B
        (updateTarget (extras cv offsets advanced active) (sevenRounds gVectors seed m))) s := by
  let s1 := roundFn gVectors seed m 0
  let s2 := roundFn gVectors s1 m 1
  let s3 := roundFn gVectors s2 m 2
  let s4 := roundFn gVectors s3 m 3
  let s5 := roundFn gVectors s4 m 4
  let s6 := roundFn gVectors s5 m 5
  let s7 := roundFn gVectors s6 m 6
  calc
    StateT.run (agave_batch_8.blocks.run B (roundTarget (extras cv offsets advanced active) 0 seed)) s = StateT.run (agave_batch_8.blocks.run B
        (roundTarget (extras cv offsets advanced active) 1 s1)) s :=
      round_run B cv offsets advanced active msg sched seed hA s 0 seed m (hsi 0) (hsv 0) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
        (roundTarget (extras cv offsets advanced active) 2 s2)) s :=
      round_run B cv offsets advanced active msg sched seed hA s 1 s1 m (hsi 1) (hsv 1) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
        (roundTarget (extras cv offsets advanced active) 3 s3)) s :=
      round_run B cv offsets advanced active msg sched seed hA s 2 s2 m (hsi 2) (hsv 2) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
        (roundTarget (extras cv offsets advanced active) 4 s4)) s :=
      round_run B cv offsets advanced active msg sched seed hA s 3 s3 m (hsi 3) (hsv 3) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
        (roundTarget (extras cv offsets advanced active) 5 s5)) s :=
      round_run B cv offsets advanced active msg sched seed hA s 4 s4 m (hsi 4) (hsv 4) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
        (roundTarget (extras cv offsets advanced active) 6 s6)) s :=
      round_run B cv offsets advanced active msg sched seed hA s 5 s5 m (hsi 5) (hsv 5) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
        (updateTarget (extras cv offsets advanced active) s7)) s :=
      round_run B cv offsets advanced active msg sched seed hA s 6 s6 m (hsi 6) (hsv 6) hmi hmv
    _ = StateT.run (agave_batch_8.blocks.run B
        (updateTarget (extras cv offsets advanced active) (sevenRounds gVectors seed m))) s := rfl

/-- The actual CV-bitcast initializer followed by the actual seven-round loop. -/
theorem init_seven_rounds_run (B : agave_batch_8.cfgCtx.Valuation) (hB : InitEnv B)
    (cv : CV (Lanes 8)) (len flags : Words8)
    (offsets advanced : Vector (BitVec 64) 8) (active : Fin 8 → Bool)
    (msg sched : Pointer) (m : State Words8)
    (hA : RoundEnv8 (sourceVal B (extras cv offsets advanced active) 0 (initial cv len flags)) msg sched)
    (s : GlobalState)
    (hsi : ∀ r i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (CompressionRound.messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (CompressionRound.messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_8.blocks.run B (initTarget cv len flags offsets advanced active)) s =
      StateT.run (agave_batch_8.blocks.run B
        (updateTarget (extras cv offsets advanced active)
          (sevenRounds gVectors (initial cv len flags) m))) s := by
  denote_enter_block
  change StateT.run (agave_batch_8.cfgBlock_19.denote
    (initVal B cv len flags offsets advanced active) >>= fun z => continueBatch B z.2) s = _
  rw [BatchInit8.block19_continue, next19_initial B hB]
  exact seven_rounds_run B cv offsets advanced active msg sched (initial cv len flags) m hA s
    hsi hsv hmi hmv

end AgaveLatticeHash.MLIR.BatchNonrootRounds8
