/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Agave.LatticeHash.MLIR.GlobalsProof
import SSA.Projects.Firedancer.Proof.Tactics

namespace AgaveLatticeHash.MLIR.BatchEntry
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)

def localWidths (_ : Nat) : Nat := 4096
def entryState (s : GlobalState) : GlobalState := s.allocaChain localWidths 2
def scratch (s : GlobalState) (i : Fin 2) : Pointer := s.chainPtr localWidths i.val

@[simp] theorem scratch_zero (s : GlobalState) : scratch s 0 = ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ := rfl
@[simp] theorem scratch_one (s : GlobalState) : scratch s 1 = ⟨⟨s.alloc.nextFreeBlock + 1⟩, 0⟩ := rfl

/-- The exact ambient valuation produced by the compiler's batch8 entry. -/
noncomputable def entryVal8 (s : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) : agave_batch_8.cfgCtx.Valuation :=
  Ctxt.Valuation.ofHVector (
    (PoisonOr.value ((scratch s 0).withOffset 480)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 448)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 416)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 384)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 352)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 320)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 288)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 256)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 224)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 192)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 160)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 128)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 96)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 64)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 32)) ::ₕ
    (lengths.map PoisonOr.value) ::ₕ
    (PoisonOr.value (src.withOffset 7168)) ::ₕ
    (PoisonOr.value (src.withOffset 6144)) ::ₕ
    (PoisonOr.value (src.withOffset 5120)) ::ₕ
    (PoisonOr.value (src.withOffset 4096)) ::ₕ
    (PoisonOr.value (src.withOffset 3072)) ::ₕ
    (PoisonOr.value (src.withOffset 2048)) ::ₕ
    (PoisonOr.value (src.withOffset 1024)) ::ₕ
    (PoisonOr.value (scratch s 1)) ::ₕ
    (PoisonOr.value (scratch s 0)) ::ₕ
    (PoisonOr.value panic) ::ₕ
    (LLVM.Ty.poison (.vector 8 (.bitvec 32))) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 512)) ::ₕ
    (LLVM.Ty.dense (.vector 32 (.bitvec 8)) [0]) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 112)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 120)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 104)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 80)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 88)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 72)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 48)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 56)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 40)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 16)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 24)) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [25]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [24]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [20]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [16]) ::ₕ
    (PoisonOr.value sched) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [-1521486534]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [1013904242]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [-1150833019]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [1779033703]) ::ₕ
    (PoisonOr.value (BitVec.ofInt 8 0)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 995)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 8)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 1027)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 7)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 6)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 5)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 4)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 3)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 1)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 2)) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [10]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [0]) ::ₕ
    (PoisonOr.value (BitVec.ofInt 32 0)) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 64)) [0]) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 0)) ::ₕ
    (LLVM.Ty.dense (.vector 4 (.bitvec 64)) [7640891574645810791]) ::ₕ
    (LLVM.Ty.dense (.vector 4 (.bitvec 64)) [-4942790176617812347]) ::ₕ
    (LLVM.Ty.dense (.vector 4 (.bitvec 64)) [4354685561679573874]) ::ₕ
    (LLVM.Ty.dense (.vector 4 (.bitvec 64)) [-6534734902060911302]) ::ₕ
    (LLVM.Ty.dense (.vector 4 (.bitvec 64)) [5840696473520329343]) ::ₕ
    (LLVM.Ty.dense (.vector 4 (.bitvec 64)) [-7276294669841635188]) ::ₕ
    (LLVM.Ty.dense (.vector 4 (.bitvec 64)) [2270897966116231595]) ::ₕ
    (LLVM.Ty.dense (.vector 4 (.bitvec 64)) [6620516961033964825]) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 480)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 448)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 416)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 384)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 352)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 320)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 288)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 256)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 224)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 192)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 160)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 128)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 96)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 64)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 32)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 7168)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 6144)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 5120)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 4096)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 3072)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 2048)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 1024)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 32 1)) ::ₕ
    PoisonOr.value out ::ₕ PoisonOr.value len ::ₕ PoisonOr.value src ::ₕ HVector.nil :
    HVector TyDenote.toType [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 32 (.bitvec 8)), SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.ptr, SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.bitvec 32, SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])

/-- The initial loop arguments are the emitted IV splats and zero offsets. -/
noncomputable def header8 : SuccArgs agave_batch_8.cfgSigs :=
  ⟨0, rfl, [LLVM.Ty.dense (.vector 4 (.bitvec 64)) [6620516961033964825],
    LLVM.Ty.dense (.vector 4 (.bitvec 64)) [2270897966116231595],
    LLVM.Ty.dense (.vector 4 (.bitvec 64)) [-7276294669841635188],
    LLVM.Ty.dense (.vector 4 (.bitvec 64)) [5840696473520329343],
    LLVM.Ty.dense (.vector 4 (.bitvec 64)) [-6534734902060911302],
    LLVM.Ty.dense (.vector 4 (.bitvec 64)) [4354685561679573874],
    LLVM.Ty.dense (.vector 4 (.bitvec 64)) [-4942790176617812347],
    LLVM.Ty.dense (.vector 4 (.bitvec 64)) [7640891574645810791],
    LLVM.Ty.dense (.vector 8 (.bitvec 64)) [0]]ₕ⟩

@[simp] theorem entryVal8_zero (s : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) :
    entryVal8 s src len out sched panic lengths
      (⟨65, by decide⟩ : agave_batch_8.cfgCtx.Var (SLLVM.Ty.bitvec 64)) =
      PoisonOr.value (0 : BitVec 64) := rfl

@[simp] theorem entryVal8_limit (s : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) :
    entryVal8 s src len out sched panic lengths
      (⟨52, by decide⟩ : agave_batch_8.cfgCtx.Var (SLLVM.Ty.bitvec 64)) =
      PoisonOr.value (1027 : BitVec 64) := rfl

@[simp] theorem header8_offsets :
    header8.args.reverse.head = Vector.replicate 8 (PoisonOr.value (0 : BitVec 64)) := rfl

@[simp] theorem header8_offset_lane (i : Fin 8) :
    (LLVM.Ty.ofVector header8.args.reverse.head)[i.val]'i.isLt =
      PoisonOr.value (0 : BitVec 64) := by
  rw [header8_offsets]
  simp [LLVM.Ty.ofVector]

theorem entryState_frame (s : GlobalState) : FrameBelow s.alloc.nextFreeBlock s (entryState s) :=
  FrameBelow.allocaChain (Nat.le_refl _) (FrameBelow.refl _ _) 2

theorem entryState_WF {s : GlobalState} (hs : s.WF) : (entryState s).WF :=
  Firedancer.GlobalState.WF.allocaChain hs 2

theorem scratch_fits (s : GlobalState) (i : Fin 2) : Fits (entryState s).mem (scratch s i) 4096 :=
  GlobalState.fits_chainPtr i.isLt

theorem input_live {s : GlobalState} (hs : s.WF) {p : Pointer} {w : Nat}
    (hp : Fits s.mem p w) : (entryState s).mem.live? p.id = s.mem.live? p.id :=
  entryState_frame s p.id (lt_nextFreeBlock_of_fits hs hp)

theorem input_fits {s : GlobalState} (hs : s.WF) {p : Pointer} {w : Nat}
    (hp : Fits s.mem p w) : Fits (entryState s).mem p w :=
  fits_of_live?_eq (input_live hs hp) hp

theorem input_read {s : GlobalState} (hs : s.WF) {p : Pointer} {w : Nat}
    (hp : Fits s.mem p w) : readWord? p w (entryState s).mem = readWord? p w s.mem :=
  readWord?_of_live?_eq (input_live hs hp)

theorem scratch_id (s : GlobalState) (i : Fin 2) :
    (scratch s i).id.id = s.alloc.nextFreeBlock + i.val :=
  Firedancer.GlobalState.chainPtr_id i.val

theorem scratch_ne_input {s : GlobalState} (hs : s.WF) {p : Pointer} {w : Nat}
    (hp : Fits s.mem p w) (i : Fin 2) : (scratch s i).id ≠ p.id := by
  intro heq
  have hi := lt_nextFreeBlock_of_fits hs hp
  have heq' := congrArg BlockId.id heq
  rw [scratch_id] at heq'
  omega

theorem global_preserved {s : GlobalState} (hs : s.WF) {p : Pointer} {name : String}
    {w : Nat} {v : BitVec w} (h : HoldsGlobal s name p v) :
    HoldsGlobal (entryState s) name p v := by
  obtain ⟨hptr, hfit, hval⟩ := h
  refine ⟨hptr, input_fits hs hfit, ?_⟩
  exact readWord_eq_of ((input_read hs hfit).trans (readWord?_eq_some hfit hval))

theorem schedule_preserved {s : GlobalState} (hs : s.WF) {p : Pointer}
    (h : ScheduleGlobal s p) : ScheduleGlobal (entryState s) p :=
  ⟨global_preserved hs h.1, h.2⟩

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
/-- Execute the actual entry up to its branch to bb1, for any continuation. -/
theorem entry8_continue {α : Type} (s : GlobalState) (hs : s.WF)
    (src len out sched panic : Pointer) (lengths : Vector (BitVec 64) 8)
    (hsrc : Fits s.mem src 65536) (hlen : Fits s.mem len 512)
    (rlen : readWord? len 512 s.mem = some (packBits lengths))
    (hg : GlobalPtr s "alloc_61fb4a9344bbdaf2573accd6331d7e32" sched)
    (hgpanic : GlobalPtr s "alloc_83bddfce772813ac48c9037cf7b0770f" panic)
    (k : agave_batch_8.cfgCtx.Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgEntry.denote
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ) >>= k) s =
      StateT.run (k (entryVal8 s src len out sched panic lengths, .inr header8)) (entryState s) := by
  dsimp only [agave_batch_8.cfgEntry]
  denote_step_reduce v 51 [LLVM.const?]
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28 hv29 hv30 hv31 hv32 hv33 hv34 hv35 hv36 hv37 hv38 hv39 hv40 hv41 hv42 hv43 hv44 hv45 hv46 hv47 hv48 hv49 hv50 hv51
  peel_addressof hg
  denote_step_reduce v 70 [LLVM.const?]
  subst hv53 hv54 hv55 hv56 hv57 hv58 hv59 hv60 hv61 hv62 hv63 hv64 hv65 hv66 hv67 hv68 hv69 hv70
  peel_addressof hgpanic
  peel_alloca from s as (s.allocaChain localWidths 1) with (allocaChain_step s localWidths 0 1 rfl)
  have hs2 : entryState s = (s.allocaChain localWidths 1).afterAlloca 4096 := rfl
  peel_alloca from (s.allocaChain localWidths 1) as (entryState s) with hs2
  have hsrc' := input_fits hs hsrc
  peel_gep 1024 with src, hsrc', (entryState s) as src1
  peel_gep 2048 with src, hsrc', (entryState s) as src2
  peel_gep 3072 with src, hsrc', (entryState s) as src3
  peel_gep 4096 with src, hsrc', (entryState s) as src4
  peel_gep 5120 with src, hsrc', (entryState s) as src5
  peel_gep 6144 with src, hsrc', (entryState s) as src6
  peel_gep 7168 with src, hsrc', (entryState s) as src7
  have hlen' := input_fits hs hlen
  have rlen' : readWord? len 512 (entryState s).mem = some (packBits lengths) :=
    (input_read hs hlen).trans rlen
  peel_load_vector lengths, len, hlen', rlen', (entryState s)
  have hscratch := scratch_fits s 0
  peel_gep 32 with (scratch s 0), hscratch, (entryState s) as tmp1
  peel_gep 64 with (scratch s 0), hscratch, (entryState s) as tmp2
  peel_gep 96 with (scratch s 0), hscratch, (entryState s) as tmp3
  peel_gep 128 with (scratch s 0), hscratch, (entryState s) as tmp4
  peel_gep 160 with (scratch s 0), hscratch, (entryState s) as tmp5
  peel_gep 192 with (scratch s 0), hscratch, (entryState s) as tmp6
  peel_gep 224 with (scratch s 0), hscratch, (entryState s) as tmp7
  peel_gep 256 with (scratch s 0), hscratch, (entryState s) as tmp8
  peel_gep 288 with (scratch s 0), hscratch, (entryState s) as tmp9
  peel_gep 320 with (scratch s 0), hscratch, (entryState s) as tmp10
  peel_gep 352 with (scratch s 0), hscratch, (entryState s) as tmp11
  peel_gep 384 with (scratch s 0), hscratch, (entryState s) as tmp12
  peel_gep 416 with (scratch s 0), hscratch, (entryState s) as tmp13
  peel_gep 448 with (scratch s 0), hscratch, (entryState s) as tmp14
  peel_gep 480 with (scratch s 0), hscratch, (entryState s) as tmp15
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  rfl

set_option maxHeartbeats 1600000 in
/-- The entry returns the exact ambient valuation and branch arguments. -/
theorem entry8_denote (s : GlobalState) (hs : s.WF)
    (src len out sched panic : Pointer) (lengths : Vector (BitVec 64) 8)
    (hsrc : Fits s.mem src 65536) (hlen : Fits s.mem len 512)
    (rlen : readWord? len 512 s.mem = some (packBits lengths))
    (hg : GlobalPtr s "alloc_61fb4a9344bbdaf2573accd6331d7e32" sched)
    (hgpanic : GlobalPtr s "alloc_83bddfce772813ac48c9037cf7b0770f" panic)
 :
    StateT.run (agave_batch_8.cfgEntry.denote
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ)) s =
      .value ((entryVal8 s src len out sched panic lengths, .inr header8), entryState s) := by
  simpa only [bind_pure, EffectM.run_pure] using entry8_continue s hs src len out sched panic lengths hsrc hlen rlen hg hgpanic pure


end AgaveLatticeHash.MLIR.BatchEntry
