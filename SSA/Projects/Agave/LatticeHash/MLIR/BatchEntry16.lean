/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Agave.LatticeHash.MLIR.GlobalsProof
import SSA.Projects.Firedancer.Proof.Tactics

namespace AgaveLatticeHash.MLIR.BatchEntry16
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)

def localWidths (_ : Nat) : Nat := 8192
def entryState (s : GlobalState) : GlobalState := s.allocaChain localWidths 2
def scratch (s : GlobalState) (i : Fin 2) : Pointer := s.chainPtr localWidths i.val

@[simp] theorem scratch_zero (s : GlobalState) : scratch s 0 = ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ := rfl
@[simp] theorem scratch_one (s : GlobalState) : scratch s 1 = ⟨⟨s.alloc.nextFreeBlock + 1⟩, 0⟩ := rfl

/-- Exact ambient valuation of the compiler-emitted batch16 entry. -/
noncomputable def entryVal16 (s : GlobalState) (src len out sched panic : Pointer)
    (lengthsLo lengthsHi : Vector (BitVec 64) 8) : agave_batch_16.cfgCtx.Valuation :=
  Ctxt.Valuation.ofHVector (
    (lengthsHi.map PoisonOr.value) ::ₕ
    (PoisonOr.value (len.withOffset 64)) ::ₕ
    (lengthsLo.map PoisonOr.value) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 960)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 896)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 832)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 768)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 704)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 640)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 576)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 512)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 448)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 384)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 320)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 256)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 192)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 128)) ::ₕ
    (PoisonOr.value ((scratch s 0).withOffset 64)) ::ₕ
    (PoisonOr.value (src.withOffset 15360)) ::ₕ
    (PoisonOr.value (src.withOffset 14336)) ::ₕ
    (PoisonOr.value (src.withOffset 13312)) ::ₕ
    (PoisonOr.value (src.withOffset 12288)) ::ₕ
    (PoisonOr.value (src.withOffset 11264)) ::ₕ
    (PoisonOr.value (src.withOffset 10240)) ::ₕ
    (PoisonOr.value (src.withOffset 9216)) ::ₕ
    (PoisonOr.value (src.withOffset 8192)) ::ₕ
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
    (LLVM.Ty.poison (.vector 16 (.bitvec 32))) ::ₕ
    (PoisonOr.value (BitVec.ofInt 16 15)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 15)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 16 14)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 14)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 16 13)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 13)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 16 12)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 12)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 16 11)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 11)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 16 10)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 10)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 16 9)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 9)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 16 8)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 8 7)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 8 6)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 6)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 8 5)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 5)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 8 4)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 4)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 8 3)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 3)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 8 2)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 8 1)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 7)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 112)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 120)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 96)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 104)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 80)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 88)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 72)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 48)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 56)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 32)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 40)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 16)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 24)) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [25]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [24]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [20]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [16]) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 8)) ::ₕ
    (PoisonOr.value sched) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 1)) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [0]) ::ₕ
    (PoisonOr.value (BitVec.ofInt 16 0)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 1027)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 2)) ::ₕ
    (LLVM.Ty.poison (.vector 8 (.bitvec 8))) ::ₕ
    (LLVM.Ty.poison (.vector 4 (.bitvec 64))) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [10]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 32)) [0]) ::ₕ
    (PoisonOr.value (BitVec.ofInt 32 0)) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [1779033703]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [-1150833019]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [1013904242]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [-1521486534]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [1359893119]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [-1694144372]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [528734635]) ::ₕ
    (LLVM.Ty.dense (.vector 16 (.bitvec 32)) [1541459225]) ::ₕ
    (LLVM.Ty.dense (.vector 8 (.bitvec 64)) [0]) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 0)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 960)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 896)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 832)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 768)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 704)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 640)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 576)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 512)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 448)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 384)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 320)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 256)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 192)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 128)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 64)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 15360)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 14336)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 13312)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 12288)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 11264)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 10240)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 9216)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 8192)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 7168)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 6144)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 5120)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 4096)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 3072)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 2048)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 64 1024)) ::ₕ
    (PoisonOr.value (BitVec.ofInt 32 1)) ::ₕ
    PoisonOr.value out ::ₕ PoisonOr.value len ::ₕ PoisonOr.value src ::ₕ HVector.nil :
    HVector TyDenote.toType [SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.ptr, SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 8 (.bitvec 8)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.bitvec 32, SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])

noncomputable def header16 : SuccArgs agave_batch_16.cfgSigs :=
  ⟨0, rfl, [LLVM.Ty.dense (.vector 8 (.bitvec 64)) [0],
    LLVM.Ty.dense (.vector 8 (.bitvec 64)) [0],
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    PoisonOr.value (BitVec.ofInt 64 0),
    LLVM.Ty.dense (.vector 16 (.bitvec 32)) [1541459225],
    LLVM.Ty.dense (.vector 16 (.bitvec 32)) [528734635],
    LLVM.Ty.dense (.vector 16 (.bitvec 32)) [-1694144372],
    LLVM.Ty.dense (.vector 16 (.bitvec 32)) [1359893119],
    LLVM.Ty.dense (.vector 16 (.bitvec 32)) [-1521486534],
    LLVM.Ty.dense (.vector 16 (.bitvec 32)) [1013904242],
    LLVM.Ty.dense (.vector 16 (.bitvec 32)) [-1150833019],
    LLVM.Ty.dense (.vector 16 (.bitvec 32)) [1779033703]]ₕ⟩

theorem entryState_frame (s : GlobalState) : FrameBelow s.alloc.nextFreeBlock s (entryState s) :=
  FrameBelow.allocaChain (Nat.le_refl _) (FrameBelow.refl _ _) 2

theorem entryState_WF {s : GlobalState} (hs : s.WF) : (entryState s).WF :=
  Firedancer.GlobalState.WF.allocaChain hs 2

theorem scratch_fits (s : GlobalState) (i : Fin 2) : Fits (entryState s).mem (scratch s i) 8192 :=
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

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
/-- Execute the actual batch16 entry, including both halves of its lengths array. -/
theorem entry16_continue {α : Type} (s : GlobalState) (hs : s.WF)
    (src len out sched panic : Pointer) (lengthsLo lengthsHi : Vector (BitVec 64) 8)
    (hsrc : Fits s.mem src 131072) (hlen : Fits s.mem len 1024)
    (rlenLo : readWord? len 512 s.mem = some (packBits lengthsLo))
    (rlenHi : readWord? (len.withOffset 64) 512 s.mem = some (packBits lengthsHi))
    (hg : GlobalPtr s "alloc_61fb4a9344bbdaf2573accd6331d7e32" sched)
    (hgpanic : GlobalPtr s "alloc_83bddfce772813ac48c9037cf7b0770f" panic)
    (k : agave_batch_16.cfgCtx.Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_16.cfgEntry.denote
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ) >>= k) s =
      StateT.run (k (entryVal16 s src len out sched panic lengthsLo lengthsHi, .inr header16)) (entryState s) := by
  dsimp only [agave_batch_16.cfgEntry]
  denote_step_reduce v 51 [LLVM.const?]
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28 hv29 hv30 hv31 hv32 hv33 hv34 hv35 hv36 hv37 hv38 hv39 hv40 hv41 hv42 hv43 hv44 hv45 hv46 hv47 hv48 hv49 hv50 hv51
  peel_addressof hg
  denote_step_reduce v 98 [LLVM.const?]
  subst hv53 hv54 hv55 hv56 hv57 hv58 hv59 hv60 hv61 hv62 hv63 hv64 hv65 hv66 hv67 hv68 hv69 hv70 hv71 hv72 hv73 hv74 hv75 hv76 hv77 hv78 hv79 hv80 hv81 hv82 hv83 hv84 hv85 hv86 hv87 hv88 hv89 hv90 hv91 hv92 hv93 hv94 hv95 hv96 hv97 hv98
  peel_addressof hgpanic
  peel_alloca from s as (s.allocaChain localWidths 1) with (allocaChain_step s localWidths 0 1 rfl)
  have hs2 : entryState s = (s.allocaChain localWidths 1).afterAlloca 8192 := rfl
  peel_alloca from (s.allocaChain localWidths 1) as (entryState s) with hs2
  have hsrc' := input_fits hs hsrc
  peel_gep 1024 with src, hsrc', (entryState s) as src1
  peel_gep 2048 with src, hsrc', (entryState s) as src2
  peel_gep 3072 with src, hsrc', (entryState s) as src3
  peel_gep 4096 with src, hsrc', (entryState s) as src4
  peel_gep 5120 with src, hsrc', (entryState s) as src5
  peel_gep 6144 with src, hsrc', (entryState s) as src6
  peel_gep 7168 with src, hsrc', (entryState s) as src7
  peel_gep 8192 with src, hsrc', (entryState s) as src8
  peel_gep 9216 with src, hsrc', (entryState s) as src9
  peel_gep 10240 with src, hsrc', (entryState s) as src10
  peel_gep 11264 with src, hsrc', (entryState s) as src11
  peel_gep 12288 with src, hsrc', (entryState s) as src12
  peel_gep 13312 with src, hsrc', (entryState s) as src13
  peel_gep 14336 with src, hsrc', (entryState s) as src14
  peel_gep 15360 with src, hsrc', (entryState s) as src15
  have hscratch := scratch_fits s 0
  peel_gep 64 with (scratch s 0), hscratch, (entryState s) as tmp1
  peel_gep 128 with (scratch s 0), hscratch, (entryState s) as tmp2
  peel_gep 192 with (scratch s 0), hscratch, (entryState s) as tmp3
  peel_gep 256 with (scratch s 0), hscratch, (entryState s) as tmp4
  peel_gep 320 with (scratch s 0), hscratch, (entryState s) as tmp5
  peel_gep 384 with (scratch s 0), hscratch, (entryState s) as tmp6
  peel_gep 448 with (scratch s 0), hscratch, (entryState s) as tmp7
  peel_gep 512 with (scratch s 0), hscratch, (entryState s) as tmp8
  peel_gep 576 with (scratch s 0), hscratch, (entryState s) as tmp9
  peel_gep 640 with (scratch s 0), hscratch, (entryState s) as tmp10
  peel_gep 704 with (scratch s 0), hscratch, (entryState s) as tmp11
  peel_gep 768 with (scratch s 0), hscratch, (entryState s) as tmp12
  peel_gep 832 with (scratch s 0), hscratch, (entryState s) as tmp13
  peel_gep 896 with (scratch s 0), hscratch, (entryState s) as tmp14
  peel_gep 960 with (scratch s 0), hscratch, (entryState s) as tmp15
  have hlen' := input_fits hs hlen
  have hlenLo : Fits s.mem len 512 := Fits.mono hlen (by omega)
  have rlenLo' : readWord? len 512 (entryState s).mem = some (packBits lengthsLo) :=
    (input_read hs hlenLo).trans rlenLo
  peel_load_vector lengthsLo, len, (input_fits hs hlenLo), rlenLo', (entryState s)
  peel_gep 64 with len, hlen', (entryState s) as lenHi
  have hlenHi0 : Fits s.mem (len.withOffset 64) 512 :=
    remainingFits s.mem len hlen 64 (by decide)
  have rlenHi' : readWord? lenHi 512 (entryState s).mem = some (packBits lengthsHi) :=
    (input_read hs hlenHi0).trans rlenHi
  peel_load_vector lengthsHi, lenHi, hlenHi, rlenHi', (entryState s)
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  rfl

set_option maxHeartbeats 2400000 in
/-- Exact ambient valuation, initialized memory and header branch of batch16. -/
theorem entry16_denote (s : GlobalState) (hs : s.WF)
    (src len out sched panic : Pointer) (lengthsLo lengthsHi : Vector (BitVec 64) 8)
    (hsrc : Fits s.mem src 131072) (hlen : Fits s.mem len 1024)
    (rlenLo : readWord? len 512 s.mem = some (packBits lengthsLo))
    (rlenHi : readWord? (len.withOffset 64) 512 s.mem = some (packBits lengthsHi))
    (hg : GlobalPtr s "alloc_61fb4a9344bbdaf2573accd6331d7e32" sched)
    (hgpanic : GlobalPtr s "alloc_83bddfce772813ac48c9037cf7b0770f" panic)
 :
    StateT.run (agave_batch_16.cfgEntry.denote
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ)) s =
      .value ((entryVal16 s src len out sched panic lengthsLo lengthsHi, .inr header16), entryState s) := by
  simpa only [bind_pure, EffectM.run_pure] using
    entry16_continue s hs src len out sched panic lengthsLo lengthsHi hsrc hlen rlenLo rlenHi hg hgpanic pure

end AgaveLatticeHash.MLIR.BatchEntry16
