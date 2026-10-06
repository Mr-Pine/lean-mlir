import SSA.Projects.Agave.LatticeHash.Compression
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Firedancer.Proof.Tactics

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression

private theorem portable_load_word {m : MemoryState} {p : Pointer} (x : Word)
    (hp : Fits m p 32) (hr : readWord? p 32 m = some x) :
    (load (.value p) (.bitvec (.concrete 32))).run m = .value (.value x, m) := by
  obtain ⟨block, hblk, hlen⟩ := hp
  have hread : block.bytes.extractLsb' p.offsetInBits 32 = x := by
    simpa [readWord?, MemoryState.live?, hblk] using hr
  rw [run_load (t := .bitvec (.concrete 32)) hblk hlen]
  simp only [LLVM.Ty.width]
  rw [hread]
  rfl

macro "peel_portable_word " x:term ", " p:term ", " hp:term ", " hr:term ", " st:term : tactic =>
  `(tactic|
    (try simp only [bind_assoc]
     reduce_cfg_indices
     rw [BlockCom.run_bind_denote_var_of_value (x := PoisonOr.value $x) (s' := $st)
       (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
           rw [run_liftM (portable_load_word (p := $p) $x $hp $hr)]
           rfl)]))

/-- The actual portable compiler output stores sixteen consecutive words. -/
def portableCompressionMemory (mem : MemoryState) (out : Pointer) (v : State Word) : MemoryState :=
  let mem := mem.splice out (v 0)
  let mem := mem.splice (out.withOffset 4) (v 1)
  let mem := mem.splice (out.withOffset 8) (v 2)
  let mem := mem.splice (out.withOffset 12) (v 3)
  let mem := mem.splice (out.withOffset 16) (v 4)
  let mem := mem.splice (out.withOffset 20) (v 5)
  let mem := mem.splice (out.withOffset 24) (v 6)
  let mem := mem.splice (out.withOffset 28) (v 7)
  let mem := mem.splice (out.withOffset 32) (v 8)
  let mem := mem.splice (out.withOffset 36) (v 9)
  let mem := mem.splice (out.withOffset 40) (v 10)
  let mem := mem.splice (out.withOffset 44) (v 11)
  let mem := mem.splice (out.withOffset 48) (v 12)
  let mem := mem.splice (out.withOffset 52) (v 13)
  let mem := mem.splice (out.withOffset 56) (v 14)
  let mem := mem.splice (out.withOffset 60) (v 15)
  mem


/-- No unrelated allocation changes during the sixteen result stores. -/
theorem portableCompressionMemory_frame (mem : MemoryState) (out : Pointer)
    (v : State Word) (b : BlockId) (hb : out.id ≠ b) :
    (portableCompressionMemory mem out v).live? b = mem.live? b := by
  unfold portableCompressionMemory
  simp only [live?_splice_ne (p := out.withOffset _) hb, live?_splice_ne hb]

/-- Result stores cannot create an allocation. -/
theorem portableCompressionMemory_dead (mem : MemoryState) (out : Pointer)
    (v : State Word) (b : BlockId) (hb : mem.live? b = none) :
    (portableCompressionMemory mem out v).live? b = none := by
  unfold portableCompressionMemory
  repeat' apply live?_splice_eq_none
  exact hb

/-- Returning the portable helper preserves its result in the caller's memory. -/
theorem portableCompressionMemory_popFrame (s : GlobalState) (hs : s.WF)
    (out : Pointer) (v : State Word) :
    s.popFrame (portableCompressionMemory s.mem out v) ≈
      ({s with mem := portableCompressionMemory s.mem out v} : GlobalState) :=
  killFrom_equiv_of_none (fun b hb => portableCompressionMemory_dead s.mem out v b (hs b hb))

end AgaveLatticeHash.MLIR
