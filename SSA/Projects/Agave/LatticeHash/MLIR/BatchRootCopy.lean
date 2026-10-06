/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Firedancer.Proof.Tactics

namespace AgaveLatticeHash.MLIR.BatchRootCopy
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)

private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ

abbrev Input18 := blockInput agave_batch_8.cfgBlock_18

def cvWords (v : Vector (LLVM.IntW 64) 4) : Vector (LLVM.IntW 32) 8 :=
  bitcast (.vector 4 (.bitvec 64)) (.vector 8 (.bitvec 32)) v

/-- Exact XOF-loop arguments after copying the retained root message block.
The duplicated CV values match the compiler's two sets of bitcasts. -/
def next18 (V : Input18.Valuation) (out : Pointer) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨22, rfl, [V ⟨75, rfl⟩, V ⟨1, rfl⟩, V ⟨0, rfl⟩,
    cvWords (V ⟨2, rfl⟩), cvWords (V ⟨3, rfl⟩),
    cvWords (V ⟨4, rfl⟩), cvWords (V ⟨5, rfl⟩),
    cvWords (V ⟨6, rfl⟩), cvWords (V ⟨7, rfl⟩),
    cvWords (V ⟨8, rfl⟩), cvWords (V ⟨9, rfl⟩),
    cvWords (V ⟨2, rfl⟩), cvWords (V ⟨3, rfl⟩),
    cvWords (V ⟨4, rfl⟩), cvWords (V ⟨5, rfl⟩),
    cvWords (V ⟨6, rfl⟩), cvWords (V ⟨7, rfl⟩),
    cvWords (V ⟨8, rfl⟩), cvWords (V ⟨9, rfl⟩),
    PoisonOr.value (out.withOffset 32)]ₕ⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The actual root-copy block retains all 512 message bytes, then enters
the XOF loop with the compiler's precise CV, flag, length and output arguments. -/
theorem block18_continue {α : Type} (V : Input18.Valuation) (s : GlobalState)
    (src dst out : Pointer) (bytes : BitVec 4096)
    (hsrc : V ⟨34, rfl⟩ = PoisonOr.value src)
    (hdst : V ⟨33, rfl⟩ = PoisonOr.value dst)
    (hlen : V ⟨37, rfl⟩ = PoisonOr.value 512#64)
    (hoff : V ⟨98, rfl⟩ = PoisonOr.value 32#64)
    (hout : V ⟨107, rfl⟩ = PoisonOr.value out)
    (fsrc : Fits s.mem src 4096) (fdst : Fits s.mem dst 4096)
    (hread : readWord? src 4096 s.mem = some bytes)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_18.denote V >>= fun r => k r.2) s =
      StateT.run (k (.inr (next18 V out))) {s with mem := s.mem.splice dst bytes} := by
  obtain ⟨blk, hblk, hfit⟩ := fsrc
  have hbits : blk.bytes.extractLsb' src.offsetInBits 4096 = bytes := by
    simpa [readWord?, MemoryState.live?, hblk] using hread
  peel_lifetime
  rw [BlockCom.run_bind_denote_var_of_nil
    (s' := {s with mem := s.mem.splice dst bytes})
    (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [hsrc, hdst, hlen]
      rw [run_liftM (run_memcpy (len := 512#64) hblk hfit fdst)]
      have hb512 : blk.bytes.extractLsb' src.offsetInBits (8 * (512#64).toNat) = bytes := hbits
      rw [hb512]
      rfl)]
  peel_lifetime
  denote_step_all v
  denote_eval v 0 16
  have ep : v16 = PoisonOr.value (out.withOffset 32) := by
    rw [hv16, hout, hoff]
    simp [gep, ptradd, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  rw [ep]
  simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote]
  simp only [next18, cvWords, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7,
    hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
  rfl

end AgaveLatticeHash.MLIR.BatchRootCopy
