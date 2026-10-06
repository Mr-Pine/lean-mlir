import SSA.Projects.Agave.LatticeHash.MLIR.agave_compress_pre_8
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionSupport
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Firedancer.Proof.Tactics

namespace AgaveLatticeHash.MLIR.CompressionRound
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression
abbrev V8 := SLLVM.Ty.arith (.vector 8 (.bitvec 32))
abbrev headerAt8 (r : BitVec 64) (v : State (Vector Word 8)) : SuccArgs agave_compress_pre_8.cfgSigs :=
  ⟨0, rfl, ([PoisonOr.value r,
    (v 0).map PoisonOr.value,
    (v 1).map PoisonOr.value,
    (v 2).map PoisonOr.value,
    (v 3).map PoisonOr.value,
    (v 4).map PoisonOr.value,
    (v 5).map PoisonOr.value,
    (v 6).map PoisonOr.value,
    (v 7).map PoisonOr.value,
    (v 8).map PoisonOr.value,
    (v 9).map PoisonOr.value,
    (v 10).map PoisonOr.value,
    (v 11).map PoisonOr.value,
    (v 12).map PoisonOr.value,
    (v 13).map PoisonOr.value,
    (v 14).map PoisonOr.value,
    (v 15).map PoisonOr.value]ₕ : HVector TyDenote.toType [SLLVM.Ty.bitvec 64, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8])⟩
abbrev exitAt8 (v : State (Vector Word 8)) : SuccArgs agave_compress_pre_8.cfgSigs :=
  ⟨1, rfl, ([(v 0).map PoisonOr.value,
(v 15).map PoisonOr.value,
(v 10).map PoisonOr.value,
(v 5).map PoisonOr.value,
(v 1).map PoisonOr.value,
(v 12).map PoisonOr.value,
(v 11).map PoisonOr.value,
(v 6).map PoisonOr.value,
(v 2).map PoisonOr.value,
(v 13).map PoisonOr.value,
(v 8).map PoisonOr.value,
(v 7).map PoisonOr.value,
(v 3).map PoisonOr.value,
(v 14).map PoisonOr.value,
(v 9).map PoisonOr.value,
(v 4).map PoisonOr.value]ₕ : HVector TyDenote.toType [V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8, V8])⟩
structure RoundEnv8 (V : agave_compress_pre_8.cfgCtx.Valuation) (msg sched : Pointer) : Prop where
  msg : V ⟨65, rfl⟩ = PoisonOr.value msg
  sched : V ⟨51, rfl⟩ = PoisonOr.value sched
  one : V ⟨52, rfl⟩ = PoisonOr.value (1 : BitVec 64)
  seven : V ⟨34, rfl⟩ = PoisonOr.value (7 : BitVec 64)
  off8 : V ⟨50, rfl⟩ = PoisonOr.value (8 : BitVec 64)
  off16 : V ⟨44, rfl⟩ = PoisonOr.value (16 : BitVec 64)
  off24 : V ⟨45, rfl⟩ = PoisonOr.value (24 : BitVec 64)
  off32 : V ⟨60, rfl⟩ = PoisonOr.value (32 : BitVec 64)
  off40 : V ⟨43, rfl⟩ = PoisonOr.value (40 : BitVec 64)
  off48 : V ⟨41, rfl⟩ = PoisonOr.value (48 : BitVec 64)
  off56 : V ⟨42, rfl⟩ = PoisonOr.value (56 : BitVec 64)
  off64 : V ⟨59, rfl⟩ = PoisonOr.value (64 : BitVec 64)
  off72 : V ⟨40, rfl⟩ = PoisonOr.value (72 : BitVec 64)
  off80 : V ⟨38, rfl⟩ = PoisonOr.value (80 : BitVec 64)
  off88 : V ⟨39, rfl⟩ = PoisonOr.value (88 : BitVec 64)
  off96 : V ⟨58, rfl⟩ = PoisonOr.value (96 : BitVec 64)
  off104 : V ⟨37, rfl⟩ = PoisonOr.value (104 : BitVec 64)
  off112 : V ⟨35, rfl⟩ = PoisonOr.value (112 : BitVec 64)
  off120 : V ⟨36, rfl⟩ = PoisonOr.value (120 : BitVec 64)
  rot16 : V ⟨49, rfl⟩ = Vector.replicate 8 (PoisonOr.value (16 : Word))
  rot20 : V ⟨48, rfl⟩ = Vector.replicate 8 (PoisonOr.value (20 : Word))
  rot24 : V ⟨47, rfl⟩ = Vector.replicate 8 (PoisonOr.value (24 : Word))
  rot25 : V ⟨46, rfl⟩ = Vector.replicate 8 (PoisonOr.value (25 : Word))

private theorem run_load64 {m : MemoryState} {p : Pointer} (x : BitVec 64)
    (hp : Fits m p 64) (hr : readWord? p 64 m = some x) :
    (load (.value p) (.bitvec (.concrete 64))).run m = .value (.value x, m) := by
  obtain ⟨block, hblk, hlen⟩ := hp
  have hread : block.bytes.extractLsb' p.offsetInBits 64 = x := by
    simpa [readWord?, MemoryState.live?, hblk] using hr
  rw [run_load (t := .bitvec (.concrete 64)) hblk hlen]
  simp only [LLVM.Ty.width]
  rw [hread]
  rfl

def rowPtr (sched : Pointer) (r : Fin 7) := sched.withOffset (BitVec.ofNat 64 r.val * 128)
def schedulePtr (sched : Pointer) (r : Fin 7) (i : Fin 16) :=
  (rowPtr sched r).withOffset (BitVec.ofNat 64 (8*i.val))
def messagePtr8 (msg : Pointer) (i : Fin 16) :=
  msg.withOffset (BitVec.ofNat 64 i.val * 32)

private def diagonalG (a b c d x y : Word) : Quad Word :=
  let a₁ := x + a + b
  let d₁ := fshlBV (a₁ ^^^ d) (a₁ ^^^ d) 16
  let c₁ := d₁ + c
  let b₁ := fshlBV (c₁ ^^^ b) (c₁ ^^^ b) 20
  let a₂ := a₁ + y + b₁
  let d₂ := fshlBV (a₂ ^^^ d₁) (a₂ ^^^ d₁) 24
  let c₂ := d₂ + c₁
  let b₂ := fshlBV (c₂ ^^^ b₁) (c₂ ^^^ b₁) 25
  ⟨a₂, b₂, c₂, d₂⟩

private theorem diagonalG_compiledG (a b c d x y : Word) :
    diagonalG a b c d x y = compiledG a b c d x y := by
  simp only [diagonalG, compiledG, BitVec.add_comm x a]

private def diagonalFlipG (a b c d x y : Word) : Quad Word :=
  let a₁ := x + a + b
  let d₁ := fshlBV (d ^^^ a₁) (d ^^^ a₁) 16
  let c₁ := d₁ + c
  let b₁ := fshlBV (c₁ ^^^ b) (c₁ ^^^ b) 20
  let a₂ := a₁ + y + b₁
  let d₂ := fshlBV (a₂ ^^^ d₁) (a₂ ^^^ d₁) 24
  let c₂ := d₂ + c₁
  let b₂ := fshlBV (c₂ ^^^ b₁) (c₂ ^^^ b₁) 25
  ⟨a₂, b₂, c₂, d₂⟩

private theorem diagonalFlipG_compiledG (a b c d x y : Word) :
    diagonalFlipG a b c d x y = compiledG a b c d x y := by
  simp only [diagonalFlipG, compiledG, BitVec.add_comm x a, BitVec.xor_comm d (a + x + b)]

private theorem roundG_compiledG (a b c d x y : Word) :
    roundG a b c d x y = compiledG a b c d x y :=
  (roundG_eq a b c d x y).trans (compiledG_eq a b c d x y).symm

private theorem roundCmp (r : Fin 7) :
    LLVM.icmp .eq (.value (BitVec.ofNat 64 (r.val+1))) (.value 7) =
      .value (if r.val = 6 then (1 : BitVec 1) else 0) := by
  rcases r with ⟨r, hr⟩
  interval_cases r <;> rfl

private theorem roundInc (r : Fin 7) :
    LLVM.add (.value (BitVec.ofNat 64 r.val)) (.value 1) {nsw := true, nuw := true} =
      .value (BitVec.ofNat 64 (r.val+1)) := by
  rcases r with ⟨r, hr⟩
  interval_cases r <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 40000000 in
/-- Executes one round of the actual compiler CFG, including schedule/message loads. -/
theorem round8_cont_run {α : Type}
    (K : (HVector toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_compress_pre_8.cfgSigs) → EffectM α)
    (V : agave_compress_pre_8.cfgCtx.Valuation)
    (msg sched : Pointer) (hV : RoundEnv8 V msg sched) (s : GlobalState)
    (r : Fin 7) (v m : State (Vector Word 8))
    (hsi : ∀ i, Fits s.mem (schedulePtr sched r i) 64)
    (hsv : ∀ i, readWord? (schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (do
      let (_, t) ← agave_compress_pre_8.cfgBlock_0.denote
        (Ctxt.Valuation.ofHVector (headerAt8 (BitVec.ofNat 64 r.val) v).args.reverse ++ V)
      K t) s =
    StateT.run (K (.inr
      (if r.val = 6 then exitAt8 (roundFn gVectors v m r)
       else headerAt8 (BitVec.ofNat 64 (r.val+1)) (roundFn gVectors v m r)))) s := by
  first
  | denote_number_from 0
    denote_step_all w 0
    denote_eval w 0 0
    have hw0p : w0 = PoisonOr.value (BitVec.ofNat 64 (r.val+1)) := by
      simp only [hw0]
      simp only [simp_spine, headerAt8, hV.one]
      exact roundInc r
    subst hw0p
    rw [BlockCom.run_bind_denote_var_of_nil (s' := s)
      (by simp [Expr.denoteOp, simp_denote, simp_sllvm])]
    denote_step_all w 1
    denote_eval w 1 1
    have hw1p : w1 = PoisonOr.value (rowPtr sched r) := by
      simp only [hw1]
      simp only [simp_spine]
      simp only [hV.sched]
      simp [rowPtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw1p
    denote_step_all w 2
    denote_eval w 2 2
    have hw2p : w2 = PoisonOr.value (schedulePtr sched r 1) := by
      simp only [hw2]
      simp only [simp_spine]
      simp only [hV.off8]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw2p
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 1).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 1) (hsv 1))]
        rfl)]
    have hs0 : schedulePtr sched r 0 = rowPtr sched r := by simp [schedulePtr, Pointer.withOffset]
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 0).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hs0 ▸ hsi 0) (hs0 ▸ hsv 0))]
        rfl)]
    denote_step_all w 5
    denote_eval w 5 5
    have hw5p : w5 = PoisonOr.value (messagePtr8 msg (schedule r 0)) := by
      simp only [hw5]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw5p
    clear hw5
    peel_load_vector (m (schedule r 0)), (messagePtr8 msg (schedule r 0)),
      (hmi (schedule r 0)), (hmv (schedule r 0)), s
    denote_step_all w 7
    denote_eval w 7 7
    have hw7p : w7 = PoisonOr.value (messagePtr8 msg (schedule r 1)) := by
      simp only [hw7]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw7p
    clear hw7
    peel_load_vector (m (schedule r 1)), (messagePtr8 msg (schedule r 1)),
      (hmi (schedule r 1)), (hmv (schedule r 1)), s
    obtain ⟨q0, hq0⟩ : ∃ q : Quad (Vector Word 8), q = gVectors (v 0) (v 4) (v 8) (v 12) (m (schedule r 0)) (m (schedule r 1)) := ⟨_, rfl⟩
    denote_step_all w 22
    denote_eval w 9 22
    simp only [simp_spine, hV.rot16, hV.rot20, hV.rot24, hV.rot25] at hw9 hw10 hw11 hw12 hw13 hw14 hw15 hw16 hw17 hw18 hw19 hw20 hw21 hw22
    have eq0a : w17 = q0.a.map PoisonOr.value := by
      simp only [hw22, hw21, hw20, hw19, hw18, hw17, hw16, hw15, hw14, hw13, hw12, hw11, hw10, hw9]
      apply Vector.ext
      intro i hi
      simp [hq0, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq0b : w22 = q0.b.map PoisonOr.value := by
      simp only [hw22, hw21, hw20, hw19, hw18, hw17, hw16, hw15, hw14, hw13, hw12, hw11, hw10, hw9]
      apply Vector.ext
      intro i hi
      simp [hq0, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq0c : w20 = q0.c.map PoisonOr.value := by
      simp only [hw22, hw21, hw20, hw19, hw18, hw17, hw16, hw15, hw14, hw13, hw12, hw11, hw10, hw9]
      apply Vector.ext
      intro i hi
      simp [hq0, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq0d : w19 = q0.d.map PoisonOr.value := by
      simp only [hw22, hw21, hw20, hw19, hw18, hw17, hw16, hw15, hw14, hw13, hw12, hw11, hw10, hw9]
      apply Vector.ext
      intro i hi
      simp [hq0, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    subst eq0a
    subst eq0b
    subst eq0c
    subst eq0d
    clear hw9 hw10 hw11 hw12 hw13 hw14 hw15 hw16 hw17 hw18 hw19 hw20 hw21 hw22
    denote_step_all w 23
    denote_eval w 23 23
    have hw23p : w23 = PoisonOr.value (schedulePtr sched r 3) := by
      simp only [hw23]
      simp only [simp_spine]
      simp only [hV.off24]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw23p
    clear hw23
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 3).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 3) (hsv 3))]
        rfl)]
    denote_step_all w 25
    denote_eval w 25 25
    have hw25p : w25 = PoisonOr.value (schedulePtr sched r 2) := by
      simp only [hw25]
      simp only [simp_spine]
      simp only [hV.off16]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw25p
    clear hw25
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 2).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 2) (hsv 2))]
        rfl)]
    denote_step_all w 27
    denote_eval w 27 27
    have hw27p : w27 = PoisonOr.value (messagePtr8 msg (schedule r 2)) := by
      simp only [hw27]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw27p
    clear hw27
    peel_load_vector (m (schedule r 2)), (messagePtr8 msg (schedule r 2)),
      (hmi (schedule r 2)), (hmv (schedule r 2)), s
    denote_step_all w 29
    denote_eval w 29 29
    have hw29p : w29 = PoisonOr.value (messagePtr8 msg (schedule r 3)) := by
      simp only [hw29]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw29p
    clear hw29
    peel_load_vector (m (schedule r 3)), (messagePtr8 msg (schedule r 3)),
      (hmi (schedule r 3)), (hmv (schedule r 3)), s
    obtain ⟨q1, hq1⟩ : ∃ q : Quad (Vector Word 8), q = gVectors (v 1) (v 5) (v 9) (v 13) (m (schedule r 2)) (m (schedule r 3)) := ⟨_, rfl⟩
    denote_step_all w 44
    denote_eval w 31 44
    simp only [simp_spine, hV.rot16, hV.rot20, hV.rot24, hV.rot25] at hw31 hw32 hw33 hw34 hw35 hw36 hw37 hw38 hw39 hw40 hw41 hw42 hw43 hw44
    have eq1a : w39 = q1.a.map PoisonOr.value := by
      simp only [hw44, hw43, hw42, hw41, hw40, hw39, hw38, hw37, hw36, hw35, hw34, hw33, hw32, hw31]
      apply Vector.ext
      intro i hi
      simp [hq1, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq1b : w44 = q1.b.map PoisonOr.value := by
      simp only [hw44, hw43, hw42, hw41, hw40, hw39, hw38, hw37, hw36, hw35, hw34, hw33, hw32, hw31]
      apply Vector.ext
      intro i hi
      simp [hq1, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq1c : w42 = q1.c.map PoisonOr.value := by
      simp only [hw44, hw43, hw42, hw41, hw40, hw39, hw38, hw37, hw36, hw35, hw34, hw33, hw32, hw31]
      apply Vector.ext
      intro i hi
      simp [hq1, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq1d : w41 = q1.d.map PoisonOr.value := by
      simp only [hw44, hw43, hw42, hw41, hw40, hw39, hw38, hw37, hw36, hw35, hw34, hw33, hw32, hw31]
      apply Vector.ext
      intro i hi
      simp [hq1, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    subst eq1a
    subst eq1b
    subst eq1c
    subst eq1d
    clear hw31 hw32 hw33 hw34 hw35 hw36 hw37 hw38 hw39 hw40 hw41 hw42 hw43 hw44
    denote_step_all w 45
    denote_eval w 45 45
    have hw45p : w45 = PoisonOr.value (schedulePtr sched r 5) := by
      simp only [hw45]
      simp only [simp_spine]
      simp only [hV.off40]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw45p
    clear hw45
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 5).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 5) (hsv 5))]
        rfl)]
    denote_step_all w 47
    denote_eval w 47 47
    have hw47p : w47 = PoisonOr.value (schedulePtr sched r 4) := by
      simp only [hw47]
      simp only [simp_spine]
      simp only [hV.off32]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw47p
    clear hw47
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 4).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 4) (hsv 4))]
        rfl)]
    denote_step_all w 49
    denote_eval w 49 49
    have hw49p : w49 = PoisonOr.value (messagePtr8 msg (schedule r 4)) := by
      simp only [hw49]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw49p
    clear hw49
    peel_load_vector (m (schedule r 4)), (messagePtr8 msg (schedule r 4)),
      (hmi (schedule r 4)), (hmv (schedule r 4)), s
    denote_step_all w 51
    denote_eval w 51 51
    have hw51p : w51 = PoisonOr.value (messagePtr8 msg (schedule r 5)) := by
      simp only [hw51]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw51p
    clear hw51
    peel_load_vector (m (schedule r 5)), (messagePtr8 msg (schedule r 5)),
      (hmi (schedule r 5)), (hmv (schedule r 5)), s
    obtain ⟨q2, hq2⟩ : ∃ q : Quad (Vector Word 8), q = gVectors (v 2) (v 6) (v 10) (v 14) (m (schedule r 4)) (m (schedule r 5)) := ⟨_, rfl⟩
    denote_step_all w 66
    denote_eval w 53 66
    simp only [simp_spine, hV.rot16, hV.rot20, hV.rot24, hV.rot25] at hw53 hw54 hw55 hw56 hw57 hw58 hw59 hw60 hw61 hw62 hw63 hw64 hw65 hw66
    have eq2a : w61 = q2.a.map PoisonOr.value := by
      simp only [hw66, hw65, hw64, hw63, hw62, hw61, hw60, hw59, hw58, hw57, hw56, hw55, hw54, hw53]
      apply Vector.ext
      intro i hi
      simp [hq2, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq2b : w66 = q2.b.map PoisonOr.value := by
      simp only [hw66, hw65, hw64, hw63, hw62, hw61, hw60, hw59, hw58, hw57, hw56, hw55, hw54, hw53]
      apply Vector.ext
      intro i hi
      simp [hq2, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq2c : w64 = q2.c.map PoisonOr.value := by
      simp only [hw66, hw65, hw64, hw63, hw62, hw61, hw60, hw59, hw58, hw57, hw56, hw55, hw54, hw53]
      apply Vector.ext
      intro i hi
      simp [hq2, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq2d : w63 = q2.d.map PoisonOr.value := by
      simp only [hw66, hw65, hw64, hw63, hw62, hw61, hw60, hw59, hw58, hw57, hw56, hw55, hw54, hw53]
      apply Vector.ext
      intro i hi
      simp [hq2, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    subst eq2a
    subst eq2b
    subst eq2c
    subst eq2d
    clear hw53 hw54 hw55 hw56 hw57 hw58 hw59 hw60 hw61 hw62 hw63 hw64 hw65 hw66
    denote_step_all w 67
    denote_eval w 67 67
    have hw67p : w67 = PoisonOr.value (schedulePtr sched r 7) := by
      simp only [hw67]
      simp only [simp_spine]
      simp only [hV.off56]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw67p
    clear hw67
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 7).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 7) (hsv 7))]
        rfl)]
    denote_step_all w 69
    denote_eval w 69 69
    have hw69p : w69 = PoisonOr.value (schedulePtr sched r 6) := by
      simp only [hw69]
      simp only [simp_spine]
      simp only [hV.off48]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw69p
    clear hw69
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 6).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 6) (hsv 6))]
        rfl)]
    denote_step_all w 71
    denote_eval w 71 71
    have hw71p : w71 = PoisonOr.value (messagePtr8 msg (schedule r 6)) := by
      simp only [hw71]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw71p
    clear hw71
    peel_load_vector (m (schedule r 6)), (messagePtr8 msg (schedule r 6)),
      (hmi (schedule r 6)), (hmv (schedule r 6)), s
    denote_step_all w 73
    denote_eval w 73 73
    have hw73p : w73 = PoisonOr.value (messagePtr8 msg (schedule r 7)) := by
      simp only [hw73]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw73p
    clear hw73
    peel_load_vector (m (schedule r 7)), (messagePtr8 msg (schedule r 7)),
      (hmi (schedule r 7)), (hmv (schedule r 7)), s
    obtain ⟨q3, hq3⟩ : ∃ q : Quad (Vector Word 8), q = gVectors (v 3) (v 7) (v 11) (v 15) (m (schedule r 6)) (m (schedule r 7)) := ⟨_, rfl⟩
    denote_step_all w 88
    denote_eval w 75 88
    simp only [simp_spine, hV.rot16, hV.rot20, hV.rot24, hV.rot25] at hw75 hw76 hw77 hw78 hw79 hw80 hw81 hw82 hw83 hw84 hw85 hw86 hw87 hw88
    have eq3a : w83 = q3.a.map PoisonOr.value := by
      simp only [hw88, hw87, hw86, hw85, hw84, hw83, hw82, hw81, hw80, hw79, hw78, hw77, hw76, hw75]
      apply Vector.ext
      intro i hi
      simp [hq3, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq3b : w88 = q3.b.map PoisonOr.value := by
      simp only [hw88, hw87, hw86, hw85, hw84, hw83, hw82, hw81, hw80, hw79, hw78, hw77, hw76, hw75]
      apply Vector.ext
      intro i hi
      simp [hq3, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq3c : w86 = q3.c.map PoisonOr.value := by
      simp only [hw88, hw87, hw86, hw85, hw84, hw83, hw82, hw81, hw80, hw79, hw78, hw77, hw76, hw75]
      apply Vector.ext
      intro i hi
      simp [hq3, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq3d : w85 = q3.d.map PoisonOr.value := by
      simp only [hw88, hw87, hw86, hw85, hw84, hw83, hw82, hw81, hw80, hw79, hw78, hw77, hw76, hw75]
      apply Vector.ext
      intro i hi
      simp [hq3, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    subst eq3a
    subst eq3b
    subst eq3c
    subst eq3d
    clear hw75 hw76 hw77 hw78 hw79 hw80 hw81 hw82 hw83 hw84 hw85 hw86 hw87 hw88
    denote_step_all w 89
    denote_eval w 89 89
    have hw89p : w89 = PoisonOr.value (schedulePtr sched r 9) := by
      simp only [hw89]
      simp only [simp_spine]
      simp only [hV.off72]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw89p
    clear hw89
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 9).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 9) (hsv 9))]
        rfl)]
    denote_step_all w 91
    denote_eval w 91 91
    have hw91p : w91 = PoisonOr.value (schedulePtr sched r 8) := by
      simp only [hw91]
      simp only [simp_spine]
      simp only [hV.off64]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw91p
    clear hw91
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 8).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 8) (hsv 8))]
        rfl)]
    denote_step_all w 93
    denote_eval w 93 93
    have hw93p : w93 = PoisonOr.value (messagePtr8 msg (schedule r 8)) := by
      simp only [hw93]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw93p
    clear hw93
    peel_load_vector (m (schedule r 8)), (messagePtr8 msg (schedule r 8)),
      (hmi (schedule r 8)), (hmv (schedule r 8)), s
    denote_step_all w 95
    denote_eval w 95 95
    have hw95p : w95 = PoisonOr.value (messagePtr8 msg (schedule r 9)) := by
      simp only [hw95]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw95p
    clear hw95
    peel_load_vector (m (schedule r 9)), (messagePtr8 msg (schedule r 9)),
      (hmi (schedule r 9)), (hmv (schedule r 9)), s
    obtain ⟨q4, hq4⟩ : ∃ q : Quad (Vector Word 8), q = gVectors (q0.a) (q1.b) (q2.c) (q3.d) (m (schedule r 8)) (m (schedule r 9)) := ⟨_, rfl⟩
    denote_step_all w 110
    denote_eval w 97 110
    simp only [simp_spine, hV.rot16, hV.rot20, hV.rot24, hV.rot25] at hw97 hw98 hw99 hw100 hw101 hw102 hw103 hw104 hw105 hw106 hw107 hw108 hw109 hw110
    have eq4a : w105 = q4.a.map PoisonOr.value := by
      simp only [hw110, hw109, hw108, hw107, hw106, hw105, hw104, hw103, hw102, hw101, hw100, hw99, hw98, hw97]
      apply Vector.ext
      intro i hi
      simp [hq4, gVectors, ← diagonalFlipG_compiledG, diagonalFlipG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq4b : w110 = q4.b.map PoisonOr.value := by
      simp only [hw110, hw109, hw108, hw107, hw106, hw105, hw104, hw103, hw102, hw101, hw100, hw99, hw98, hw97]
      apply Vector.ext
      intro i hi
      simp [hq4, gVectors, ← diagonalFlipG_compiledG, diagonalFlipG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq4c : w108 = q4.c.map PoisonOr.value := by
      simp only [hw110, hw109, hw108, hw107, hw106, hw105, hw104, hw103, hw102, hw101, hw100, hw99, hw98, hw97]
      apply Vector.ext
      intro i hi
      simp [hq4, gVectors, ← diagonalFlipG_compiledG, diagonalFlipG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq4d : w107 = q4.d.map PoisonOr.value := by
      simp only [hw110, hw109, hw108, hw107, hw106, hw105, hw104, hw103, hw102, hw101, hw100, hw99, hw98, hw97]
      apply Vector.ext
      intro i hi
      simp [hq4, gVectors, ← diagonalFlipG_compiledG, diagonalFlipG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    subst eq4a
    subst eq4b
    subst eq4c
    subst eq4d
    clear hw97 hw98 hw99 hw100 hw101 hw102 hw103 hw104 hw105 hw106 hw107 hw108 hw109 hw110
    denote_step_all w 111
    denote_eval w 111 111
    have hw111p : w111 = PoisonOr.value (schedulePtr sched r 11) := by
      simp only [hw111]
      simp only [simp_spine]
      simp only [hV.off88]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw111p
    clear hw111
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 11).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 11) (hsv 11))]
        rfl)]
    denote_step_all w 113
    denote_eval w 113 113
    have hw113p : w113 = PoisonOr.value (schedulePtr sched r 10) := by
      simp only [hw113]
      simp only [simp_spine]
      simp only [hV.off80]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw113p
    clear hw113
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 10).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 10) (hsv 10))]
        rfl)]
    denote_step_all w 115
    denote_eval w 115 115
    have hw115p : w115 = PoisonOr.value (messagePtr8 msg (schedule r 10)) := by
      simp only [hw115]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw115p
    clear hw115
    peel_load_vector (m (schedule r 10)), (messagePtr8 msg (schedule r 10)),
      (hmi (schedule r 10)), (hmv (schedule r 10)), s
    denote_step_all w 117
    denote_eval w 117 117
    have hw117p : w117 = PoisonOr.value (messagePtr8 msg (schedule r 11)) := by
      simp only [hw117]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw117p
    clear hw117
    peel_load_vector (m (schedule r 11)), (messagePtr8 msg (schedule r 11)),
      (hmi (schedule r 11)), (hmv (schedule r 11)), s
    obtain ⟨q5, hq5⟩ : ∃ q : Quad (Vector Word 8), q = gVectors (q1.a) (q2.b) (q3.c) (q0.d) (m (schedule r 10)) (m (schedule r 11)) := ⟨_, rfl⟩
    denote_step_all w 132
    denote_eval w 119 132
    simp only [simp_spine, hV.rot16, hV.rot20, hV.rot24, hV.rot25] at hw119 hw120 hw121 hw122 hw123 hw124 hw125 hw126 hw127 hw128 hw129 hw130 hw131 hw132
    have eq5a : w127 = q5.a.map PoisonOr.value := by
      simp only [hw132, hw131, hw130, hw129, hw128, hw127, hw126, hw125, hw124, hw123, hw122, hw121, hw120, hw119]
      apply Vector.ext
      intro i hi
      simp [hq5, gVectors, ← diagonalG_compiledG, diagonalG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq5b : w132 = q5.b.map PoisonOr.value := by
      simp only [hw132, hw131, hw130, hw129, hw128, hw127, hw126, hw125, hw124, hw123, hw122, hw121, hw120, hw119]
      apply Vector.ext
      intro i hi
      simp [hq5, gVectors, ← diagonalG_compiledG, diagonalG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq5c : w130 = q5.c.map PoisonOr.value := by
      simp only [hw132, hw131, hw130, hw129, hw128, hw127, hw126, hw125, hw124, hw123, hw122, hw121, hw120, hw119]
      apply Vector.ext
      intro i hi
      simp [hq5, gVectors, ← diagonalG_compiledG, diagonalG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq5d : w129 = q5.d.map PoisonOr.value := by
      simp only [hw132, hw131, hw130, hw129, hw128, hw127, hw126, hw125, hw124, hw123, hw122, hw121, hw120, hw119]
      apply Vector.ext
      intro i hi
      simp [hq5, gVectors, ← diagonalG_compiledG, diagonalG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    subst eq5a
    subst eq5b
    subst eq5c
    subst eq5d
    clear hw119 hw120 hw121 hw122 hw123 hw124 hw125 hw126 hw127 hw128 hw129 hw130 hw131 hw132
    denote_step_all w 133
    denote_eval w 133 133
    have hw133p : w133 = PoisonOr.value (schedulePtr sched r 13) := by
      simp only [hw133]
      simp only [simp_spine]
      simp only [hV.off104]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw133p
    clear hw133
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 13).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 13) (hsv 13))]
        rfl)]
    denote_step_all w 135
    denote_eval w 135 135
    have hw135p : w135 = PoisonOr.value (schedulePtr sched r 12) := by
      simp only [hw135]
      simp only [simp_spine]
      simp only [hV.off96]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw135p
    clear hw135
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 12).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 12) (hsv 12))]
        rfl)]
    denote_step_all w 137
    denote_eval w 137 137
    have hw137p : w137 = PoisonOr.value (messagePtr8 msg (schedule r 12)) := by
      simp only [hw137]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw137p
    clear hw137
    peel_load_vector (m (schedule r 12)), (messagePtr8 msg (schedule r 12)),
      (hmi (schedule r 12)), (hmv (schedule r 12)), s
    denote_step_all w 139
    denote_eval w 139 139
    have hw139p : w139 = PoisonOr.value (messagePtr8 msg (schedule r 13)) := by
      simp only [hw139]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw139p
    clear hw139
    peel_load_vector (m (schedule r 13)), (messagePtr8 msg (schedule r 13)),
      (hmi (schedule r 13)), (hmv (schedule r 13)), s
    obtain ⟨q6, hq6⟩ : ∃ q : Quad (Vector Word 8), q = gVectors (q2.a) (q3.b) (q0.c) (q1.d) (m (schedule r 12)) (m (schedule r 13)) := ⟨_, rfl⟩
    denote_step_all w 154
    denote_eval w 141 154
    simp only [simp_spine, hV.rot16, hV.rot20, hV.rot24, hV.rot25] at hw141 hw142 hw143 hw144 hw145 hw146 hw147 hw148 hw149 hw150 hw151 hw152 hw153 hw154
    have eq6a : w149 = q6.a.map PoisonOr.value := by
      simp only [hw154, hw153, hw152, hw151, hw150, hw149, hw148, hw147, hw146, hw145, hw144, hw143, hw142, hw141]
      apply Vector.ext
      intro i hi
      simp [hq6, gVectors, ← diagonalG_compiledG, diagonalG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq6b : w154 = q6.b.map PoisonOr.value := by
      simp only [hw154, hw153, hw152, hw151, hw150, hw149, hw148, hw147, hw146, hw145, hw144, hw143, hw142, hw141]
      apply Vector.ext
      intro i hi
      simp [hq6, gVectors, ← diagonalG_compiledG, diagonalG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq6c : w152 = q6.c.map PoisonOr.value := by
      simp only [hw154, hw153, hw152, hw151, hw150, hw149, hw148, hw147, hw146, hw145, hw144, hw143, hw142, hw141]
      apply Vector.ext
      intro i hi
      simp [hq6, gVectors, ← diagonalG_compiledG, diagonalG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq6d : w151 = q6.d.map PoisonOr.value := by
      simp only [hw154, hw153, hw152, hw151, hw150, hw149, hw148, hw147, hw146, hw145, hw144, hw143, hw142, hw141]
      apply Vector.ext
      intro i hi
      simp [hq6, gVectors, ← diagonalG_compiledG, diagonalG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    subst eq6a
    subst eq6b
    subst eq6c
    subst eq6d
    clear hw141 hw142 hw143 hw144 hw145 hw146 hw147 hw148 hw149 hw150 hw151 hw152 hw153 hw154
    denote_step_all w 155
    denote_eval w 155 155
    have hw155p : w155 = PoisonOr.value (schedulePtr sched r 15) := by
      simp only [hw155]
      simp only [simp_spine]
      simp only [hV.off120]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw155p
    clear hw155
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 15).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 15) (hsv 15))]
        rfl)]
    denote_step_all w 157
    denote_eval w 157 157
    have hw157p : w157 = PoisonOr.value (schedulePtr sched r 14) := by
      simp only [hw157]
      simp only [simp_spine]
      simp only [hV.off112]
      simp [schedulePtr,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw157p
    clear hw157
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (BitVec.ofNat 64 (schedule r 14).val)) (s' := s)
      (by
        simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
        rw [run_liftM (run_load64 _ (hsi 14) (hsv 14))]
        rfl)]
    denote_step_all w 159
    denote_eval w 159 159
    have hw159p : w159 = PoisonOr.value (messagePtr8 msg (schedule r 14)) := by
      simp only [hw159]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw159p
    clear hw159
    peel_load_vector (m (schedule r 14)), (messagePtr8 msg (schedule r 14)),
      (hmi (schedule r 14)), (hmv (schedule r 14)), s
    denote_step_all w 161
    denote_eval w 161 161
    have hw161p : w161 = PoisonOr.value (messagePtr8 msg (schedule r 15)) := by
      simp only [hw161]
      simp only [simp_spine]
      simp only [hV.msg]
      simp [messagePtr8,
        gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?,
        Pointer.withOffset, simp_sllvm]
    subst hw161p
    clear hw161
    peel_load_vector (m (schedule r 15)), (messagePtr8 msg (schedule r 15)),
      (hmi (schedule r 15)), (hmv (schedule r 15)), s
    obtain ⟨q7, hq7⟩ : ∃ q : Quad (Vector Word 8), q = gVectors (q3.a) (q0.b) (q1.c) (q2.d) (m (schedule r 14)) (m (schedule r 15)) := ⟨_, rfl⟩
    denote_step_all w 176
    denote_eval w 163 176
    simp only [simp_spine, hV.rot16, hV.rot20, hV.rot24, hV.rot25] at hw163 hw164 hw165 hw166 hw167 hw168 hw169 hw170 hw171 hw172 hw173 hw174 hw175 hw176
    have eq7a : w171 = q7.a.map PoisonOr.value := by
      simp only [hw176, hw175, hw174, hw173, hw172, hw171, hw170, hw169, hw168, hw167, hw166, hw165, hw164, hw163]
      apply Vector.ext
      intro i hi
      simp [hq7, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq7b : w176 = q7.b.map PoisonOr.value := by
      simp only [hw176, hw175, hw174, hw173, hw172, hw171, hw170, hw169, hw168, hw167, hw166, hw165, hw164, hw163]
      apply Vector.ext
      intro i hi
      simp [hq7, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq7c : w174 = q7.c.map PoisonOr.value := by
      simp only [hw176, hw175, hw174, hw173, hw172, hw171, hw170, hw169, hw168, hw167, hw166, hw165, hw164, hw163]
      apply Vector.ext
      intro i hi
      simp [hq7, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    have eq7d : w173 = q7.d.map PoisonOr.value := by
      simp only [hw176, hw175, hw174, hw173, hw172, hw171, hw170, hw169, hw168, hw167, hw166, hw165, hw164, hw163]
      apply Vector.ext
      intro i hi
      simp [hq7, gVectors, ← roundG_compiledG, roundG, InstCombine.binaryDenote,
        simp_llvm, simp_llvm_option, vfshl, fshl, LLVM.Ty.dense,
        Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_replicate]
    subst eq7a
    subst eq7b
    subst eq7c
    subst eq7d
    clear hw163 hw164 hw165 hw166 hw167 hw168 hw169 hw170 hw171 hw172 hw173 hw174 hw175 hw176
    denote_step_all w 177
    denote_eval w 177 177
    have hw177p : w177 = PoisonOr.value (if r.val = 6 then (1 : BitVec 1) else 0) := by
      simp only [hw177, simp_spine, hV.seven]
      exact roundCmp r
    subst hw177p
    rw [← roundRegisters_eq,
      roundRegisters_of_quads gVectors v (fun i => m (schedule r i))
        q0 q1 q2 q3 q4 q5 q6 q7 hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7]
    by_cases hr : r.val = 6
    · simp only [hr, ite_true]
      simp only [BlockCom.denote_term, Terminator.denote_condBr]
      simp only [simp_spine]
      simp only [simp_denote, simp_sllvm]
      all_goals rfl
    · simp only [hr, ite_false]
      simp only [BlockCom.denote_term, Terminator.denote_condBr]
      simp only [simp_spine]
      simp only [simp_denote, simp_sllvm]
      all_goals rfl

end AgaveLatticeHash.MLIR.CompressionRound
