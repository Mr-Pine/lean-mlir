/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Firedancer.Proof.Tactics

namespace AgaveLatticeHash.MLIR.BatchRootCopy16
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Input5 := blockInput agave_batch_16.cfgBlock_5

def words16 (v : Vector (LLVM.IntW 64) 8) : Vector (LLVM.IntW 32) 16 :=
  bitcast (.vector 8 (.bitvec 64)) (.vector 16 (.bitvec 32)) v

/-- Root-loop arguments preserve all sixteen lanes' CV, block length and flags. -/
def next5 (V : Input5.Valuation) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨9, rfl, [V ⟨113, rfl⟩, V ⟨9, rfl⟩, V ⟨8, rfl⟩, V ⟨7, rfl⟩,
    V ⟨6, rfl⟩, V ⟨5, rfl⟩, V ⟨4, rfl⟩, V ⟨3, rfl⟩, V ⟨2, rfl⟩,
    words16 (V ⟨0, rfl⟩), words16 (V ⟨1, rfl⟩)]ₕ⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Execute the actual retained-root copy and enter the XOF loop, preserving
all 1024 transposed message bytes with the exact compiler successor payload. -/
theorem block5_continue {α : Type} (V : Input5.Valuation) (s : GlobalState)
    (src dst : Pointer) (bytes : BitVec 8192)
    (hsrc : V ⟨44, rfl⟩ = PoisonOr.value src)
    (hdst : V ⟨43, rfl⟩ = PoisonOr.value dst)
    (hlen : V ⟨143, rfl⟩ = PoisonOr.value 1024#64)
    (fsrc : Fits s.mem src 8192) (fdst : Fits s.mem dst 8192)
    (hread : readWord? src 8192 s.mem = some bytes)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_16.cfgBlock_5.denote V >>= fun r => k r.2) s =
      StateT.run (k (.inr (next5 V))) {s with mem := s.mem.splice dst bytes} := by
  obtain ⟨blk, hblk, hfit⟩ := fsrc
  have hbits : blk.bytes.extractLsb' src.offsetInBits 8192 = bytes := by
    simpa [readWord?, MemoryState.live?, hblk] using hread
  peel_lifetime
  rw [BlockCom.run_bind_denote_var_of_nil
    (s' := {s with mem := s.mem.splice dst bytes})
    (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [hsrc, hdst, hlen]
      rw [run_liftM (run_memcpy (len := 1024#64) hblk hfit fdst)]
      have hb1024 : blk.bytes.extractLsb' src.offsetInBits (8 * (1024#64).toNat) = bytes := hbits
      rw [hb1024]
      rfl)]
  peel_lifetime
  denote_step_all v
  denote_eval v 0 1
  simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote]
  simp only [next5, words16, hv0, hv1]
  rfl

end AgaveLatticeHash.MLIR.BatchRootCopy16
