/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXof16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofOutput16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOutputRun16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundSteps16

namespace AgaveLatticeHash.MLIR.BatchXofLoop16
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open CompressionRound BatchReduction16
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.auxLemma false
abbrev RowTy : SLLVM.Ty := .arith (.vector 16 (.bitvec 32))
abbrev ExtraTypes : List SLLVM.Ty :=
  [RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, RowTy, SLLVM.Ty.bitvec 64]

/-- Root CV, metadata, and output counter retained through seven rounds. -/
def extras (cv : CV Words16) (len flags : Words16) (counter : Nat) :
    HVector TyDenote.toType ExtraTypes :=
  [(cv 7).map PoisonOr.value, (cv 6).map PoisonOr.value,
   (cv 5).map PoisonOr.value, (cv 4).map PoisonOr.value,
   (cv 3).map PoisonOr.value, (cv 2).map PoisonOr.value,
   (cv 1).map PoisonOr.value, (cv 0).map PoisonOr.value,
   len.map PoisonOr.value, flags.map PoisonOr.value,
   PoisonOr.value (BitVec.ofNat 64 counter)]ₕ

def rootTarget (cv : CV Words16) (len flags : Words16) (counter : Nat) :
    SuccArgs agave_batch_16.cfgSigs :=
  ⟨9, rfl, [PoisonOr.value (BitVec.ofNat 64 counter),
   (cv 7).map PoisonOr.value, (cv 6).map PoisonOr.value,
   (cv 5).map PoisonOr.value, (cv 4).map PoisonOr.value,
   (cv 3).map PoisonOr.value, (cv 2).map PoisonOr.value,
   (cv 1).map PoisonOr.value, (cv 0).map PoisonOr.value,
   len.map PoisonOr.value, flags.map PoisonOr.value]ₕ⟩

def roundTarget (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64)
    (v : State Words16) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨10, rfl, (CompressionRound.headerAt16 r v).args.append e⟩
def outputTarget (e : HVector TyDenote.toType ExtraTypes) (v : State Words16) :
    SuccArgs agave_batch_16.cfgSigs :=
  ⟨11, rfl, e.append (CompressionRound.exitAt16 v).args⟩
noncomputable def rootVal (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (counter : Nat) : BatchXof16.Input9.Valuation :=
  Ctxt.Valuation.ofHVector (rootTarget cv len flags counter).args.reverse ++ B
noncomputable def roundVal (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64) (v : State Words16) :
    BatchRounds.Input16_10.Valuation :=
  Ctxt.Valuation.ofHVector (roundTarget e r v).args.reverse ++ B
noncomputable def outputVal (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (v : State Words16) : BatchOutput16.Input11.Valuation :=
  Ctxt.Valuation.ofHVector (outputTarget e v).args.reverse ++ B

noncomputable def sourceVal (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes) (r : BitVec 64) (v : State Words16) :
    agave_compress_pre_16.cfgCtx.Valuation :=
  fun _ x => ((roundVal B e r v).comap BatchRounds.rename16_10) (x.appendInr (Γ := Ctxt.ofList (CompressionRound.headerAt16 r v).ts.reverse))

theorem round_renaming (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (r : BitVec 64) (v : State Words16) :
    (roundVal B e r v).comap BatchRounds.rename16_10 =
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
    BatchRoundBranches.adapt16_10 (roundVal B e r v)
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
  rfl

theorem adapt_exit (B : agave_batch_16.cfgCtx.Valuation)
    (e : HVector TyDenote.toType ExtraTypes)
    (r : BitVec 64) (v v' : State Words16) :
    BatchRoundBranches.adapt16_10 (roundVal B e r v)
      (CompressionRound.exitAt16 v') = outputTarget e v' := by
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
  rfl

noncomputable def continueBatch (B : agave_batch_16.cfgCtx.Valuation)
    (r : HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) :
    EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty)) :=
  Blocks.force_limit_next.match_1 (fun _ => EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty))) r
    (fun ret => pure ret) (fun t => agave_batch_16.blocks.run B t)

attribute [local irreducible] BlockCom.denote Blocks.run

/-- One actual root round preserves the saved CV, metadata, and output counter
while advancing the BLAKE3 state. -/
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
        (if r.val = 6 then outputTarget e (roundFn gVectors v m r)
         else roundTarget e (BitVec.ofNat 64 (r.val+1))
           (roundFn gVectors v m r))) s := by
  denote_enter_block
  change StateT.run (agave_batch_16.cfgBlock_10.denote
    (roundVal B e (BitVec.ofNat 64 r.val) v) >>=
      fun z => continueBatch B z.2) s = _
  rw [BatchRoundBranches.block16_10_round (continueBatch B)
    (roundVal B e (BitVec.ofNat 64 r.val) v)
    (sourceVal B e (BitVec.ofNat 64 r.val) v)
    msg sched
    (sourceEnv_change B e 0 (BitVec.ofNat 64 r.val) seed v msg sched hA)
    s r v m (round_renaming B e (BitVec.ofNat 64 r.val) v)
    hsi hsv hmi hmv]
  by_cases hr : r.val = 6 <;>
    simp only [hr, reduceIte, adapt_exit, adapt_header, continueBatch]

/-- All seven rounds of actual block 10 reach actual output block 11,
with the exact vector BLAKE3 state and every retained value unchanged. -/
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
        (outputTarget e (sevenRounds gVectors seed m))) s := by
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
        (outputTarget e s7)) s :=
      round_run B e msg sched seed hA s 6 s6 m (hsi 6) (hsv 6) hmi hmv
    _ = StateT.run (agave_batch_16.blocks.run B
        (outputTarget e (sevenRounds gVectors seed m))) s := rfl

/-- Constants captured by the emitted batch entry and used at block 9. -/
structure InitEnv (B : agave_batch_16.cfgCtx.Valuation) : Prop where
  zero64 : B ⟨103, rfl⟩ = PoisonOr.value 0#64
  zero32 : B ⟨84, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0#32)
  iv0 : B ⟨94, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0x6A09E667#32)
  iv1 : B ⟨95, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0xBB67AE85#32)
  iv2 : B ⟨96, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0x3C6EF372#32)
  iv3 : B ⟨97, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0xA54FF53A#32)

def rootInitial (cv : CV Words16) (len flags : Words16) (counter : Nat) : State Words16 :=
  initState cv (Vector.replicate 16) (Vector.replicate 16 (BitVec.ofNat 32 counter))
    (Vector.replicate 16 0#32) len flags

theorem next9_initial (B : agave_batch_16.cfgCtx.Valuation) (hB : InitEnv B)
    (cv : CV Words16) (len flags : Words16) (counter : Nat) :
    BatchXof16.next9 (rootVal B cv len flags counter) counter =
      roundTarget (extras cv len flags counter) 0 (rootInitial cv len flags counter) := by
  have hz : (rootVal B cv len flags counter) ⟨114, rfl⟩ = PoisonOr.value 0#64 := hB.zero64
  have hh : (rootVal B cv len flags counter) ⟨95, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0#32) := hB.zero32
  have hi0 : (rootVal B cv len flags counter) ⟨105, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0x6A09E667#32) := hB.iv0
  have hi1 : (rootVal B cv len flags counter) ⟨106, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0xBB67AE85#32) := hB.iv1
  have hi2 : (rootVal B cv len flags counter) ⟨107, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0x3C6EF372#32) := hB.iv2
  have hi3 : (rootVal B cv len flags counter) ⟨108, rfl⟩ = Vector.replicate 16 (PoisonOr.value 0xA54FF53A#32) := hB.iv3
  unfold BatchXof16.next9
  rw [hz, hh, hi0, hi1, hi2, hi3]
  congr 1
  apply HVector.ext
  intro i
  fin_cases i <;> first | rfl | exact Vector.map_replicate.symm

theorem output_env (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (counter : Nat) (v : State Words16) :
    BatchXofOutput16.Env16 (outputVal B (extras cv len flags counter) v) v cv := by
  constructor
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

theorem output_backedge (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (counter : Nat) (v : State Words16) :
    BatchOutput16.next11 (outputVal B (extras cv len flags counter) v)
      (.value (BitVec.ofNat 64 (counter+1))) = rootTarget cv len flags (counter+1) := rfl

structure OutputEnv (B : agave_batch_16.cfgCtx.Valuation) (out : Pointer) : Prop where
  outPtr : B ⟨135, rfl⟩ = PoisonOr.value out
  shift : B ⟨54, rfl⟩ = PoisonOr.value 6#64
  one : B ⟨83, rfl⟩ = PoisonOr.value 1#64
  limit : B ⟨73, rfl⟩ = PoisonOr.value 32#64

def outputPtr (out : Pointer) (counter : Nat) : Pointer :=
  out.withOffset (BitVec.ofNat 64 (64*counter))
def finalState (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (counter : Nat) : State Words16 :=
  sevenRounds gVectors (rootInitial cv len flags counter) m
def delta (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (counter : Nat) : Vector (BitVec 16) 32 :=
  columnSum (BatchXofOutput16.columns (finalState cv len flags m counter) cv)
def accumulate (s : GlobalState) (out : Pointer) (counter : Nat)
    (old d : Vector (BitVec 16) 32) : GlobalState :=
  {s with mem := s.mem.splice (outputPtr out counter) (packBits (BatchOutput16.sums32 old d))}

private theorem byteGep (p : Pointer) (off : BitVec 64) :
    gep (.value p) 1 0 (.value off) = .value (p.withOffset off) := by
  simp [gep, ptradd, Pointer.withOffset, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?]

/-- Actual block 11 feed-forward, reduction, 512-bit store, and counter branch. -/
theorem output_run (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (out : Pointer) (hB : OutputEnv B out)
    (counter : Nat) (hc : counter < 32) (s : GlobalState) (v : State Words16)
    (old : Vector (BitVec 16) 32)
    (fit : Fits s.mem (outputPtr out counter) 512)
    (read : readWord? (outputPtr out counter) 512 s.mem = some (packBits old)) :
    StateT.run (agave_batch_16.blocks.run B (outputTarget (extras cv len flags counter) v)) s =
      StateT.run (agave_batch_16.blocks.run B
        (if counter = 31 then ⟨12, rfl, .nil⟩ else rootTarget cv len flags (counter+1)))
        (accumulate s out counter old (columnSum (BatchXofOutput16.columns v cv))) := by
  have hp : gep ((outputVal B (extras cv len flags counter) v) ⟨162, rfl⟩) 1 0
      (.value (BitVec.ofNat 64 (64*counter))) = .value (outputPtr out counter) := by
    change gep (B ⟨135, rfl⟩) 1 0 _ = _
    rw [hB.outPtr]
    exact byteGep _ _
  have h := BatchOutputRun16.run11 B (outputTarget (extras cv len flags counter) v).args
    s counter hc (outputPtr out counter) old (columnSum (BatchXofOutput16.columns v cv))
    (by rfl) hB.shift hB.one hB.limit hp
    (BatchXofOutput16.delta16_defined _ v cv (output_env B cv len flags counter v)) fit read
  change StateT.run (agave_batch_16.blocks.run B (outputTarget (extras cv len flags counter) v)) s =
    StateT.run (agave_batch_16.blocks.run B (if counter = 31 then _ else
      BatchOutput16.next11 (outputVal B (extras cv len flags counter) v) _)) _ at h
  rw [output_backedge] at h
  exact h

/-- Read obligations of a single counter, before its actual instructions run. -/
structure IterationMemory (s : GlobalState) (out msg sched : Pointer)
    (counter : Nat) (m : State Words16) (old : Vector (BitVec 16) 32) : Prop where
  scheduleFits : ∀ r i, Fits s.mem (schedulePtr16 sched r i) 64
  scheduleRead : ∀ r i, readWord? (schedulePtr16 sched r i) 64 s.mem = some (BitVec.ofNat 64 (schedule r i).val)
  messageFits : ∀ i, Fits s.mem (messagePtr16 msg i) 512
  messageRead : ∀ i, readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i))
  outputFits : Fits s.mem (outputPtr out counter) 512
  outputRead : readWord? (outputPtr out counter) 512 s.mem = some (packBits old)

/-- Actual initialization, seven actual round-block executions, and output store. -/
theorem iteration_run (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (out msg sched : Pointer)
    (hInit : InitEnv B) (hOut : OutputEnv B out) (counter : Nat) (hc : counter < 32)
    (hRound : RoundEnv16 (sourceVal B (extras cv len flags counter) 0 (rootInitial cv len flags counter)) msg sched)
    (s : GlobalState) (m : State Words16) (old : Vector (BitVec 16) 32)
    (hmem : IterationMemory s out msg sched counter m old) :
    StateT.run (agave_batch_16.blocks.run B (rootTarget cv len flags counter)) s =
      StateT.run (agave_batch_16.blocks.run B
        (if counter = 31 then ⟨12, rfl, .nil⟩ else rootTarget cv len flags (counter+1)))
        (accumulate s out counter old (delta cv len flags m counter)) := by
  have h := BatchXof16.run9 B (rootTarget cv len flags counter).args s counter hc (by rfl) hInit.zero64
  change StateT.run (agave_batch_16.blocks.run B (rootTarget cv len flags counter)) s =
    StateT.run (agave_batch_16.blocks.run B (BatchXof16.next9 (rootVal B cv len flags counter) counter)) s at h
  rw [h, next9_initial B hInit]
  rw [seven_rounds_run B (extras cv len flags counter) msg sched (rootInitial cv len flags counter) m
    hRound s hmem.scheduleFits hmem.scheduleRead hmem.messageFits hmem.messageRead]
  exact output_run B cv len flags out hOut counter hc s (finalState cv len flags m counter)
    old hmem.outputFits hmem.outputRead

def accumulatedState (s : GlobalState) (out : Pointer)
    (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32) : Nat → GlobalState
  | 0 => s
  | c+1 => accumulate (accumulatedState s out cv len flags m old c)
      out c (old c) (delta cv len flags m c)

/-- All 32 actual root-output iterations terminate at the emitted return block. -/
theorem xof32_run (B : agave_batch_16.cfgCtx.Valuation)
    (cv : CV Words16) (len flags : Words16) (out msg sched : Pointer)
    (hInit : InitEnv B) (hOut : OutputEnv B out) (s : GlobalState) (m : State Words16)
    (old : Nat → Vector (BitVec 16) 32)
    (hRound : ∀ c, c < 32 → RoundEnv16
      (sourceVal B (extras cv len flags c) 0 (rootInitial cv len flags c)) msg sched)
    (hMem : ∀ c, c < 32 → IterationMemory (accumulatedState s out cv len flags m old c)
      out msg sched c m (old c)) :
    StateT.run (agave_batch_16.blocks.run B (rootTarget cv len flags 0)) s =
      .value (.nil, accumulatedState s out cv len flags m old 32) := by
  have loop : ∀ n c, c+n = 32 → c < 32 →
      StateT.run (agave_batch_16.blocks.run B (rootTarget cv len flags c))
        (accumulatedState s out cv len flags m old c) =
        .value (.nil, accumulatedState s out cv len flags m old 32) := by
    intro n
    induction n with
    | zero => intro c hn hc; omega
    | succ n ih =>
      intro c hn hc
      rw [iteration_run B cv len flags out msg sched hInit hOut c hc (hRound c hc)
        (accumulatedState s out cv len flags m old c) m (old c) (hMem c hc)]
      change StateT.run (agave_batch_16.blocks.run B
        (if c = 31 then ⟨12, rfl, .nil⟩ else rootTarget cv len flags (c+1)))
        (accumulatedState s out cv len flags m old (c+1)) = _
      by_cases he : c = 31
      · subst c
        simpa only [reduceIte] using BatchOutputRun16.run12 B (accumulatedState s out cv len flags m old 32)
      · simp only [he, reduceIte]
        exact ih (c+1) (by omega) (by omega)
  exact loop 32 0 rfl (by decide)

end AgaveLatticeHash.MLIR.BatchXofLoop16
