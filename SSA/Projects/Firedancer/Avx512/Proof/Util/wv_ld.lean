/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Util.wv_ld
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.MLIR.DenoteStep

/-!
# `wv_ld` conforms to its spec

One `llvm.load` at `vector<4xi64>`, which `LLVM.Ty.unflatten` turns into the
four lanes `readWv` reads. The region allocates nothing and writes nothing, so
the state the load runs in is the state it returns and the frame pop is
invisible.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- A `vector<4xi64>` load at `p` decodes to the four lanes `readWv` reads:
lane `j` at bits `[64j, 64j + 64)` from `p`. The 256-bit counterpart of
`unflatten_readQuad_v03`. -/
theorem unflatten_readWv {m : MemoryState} {p : Pointer} (h : IsWvPtr m p)
    {blk : LiveBlock} (hblk : m.live? p.id = some blk) :
    LLVM.Ty.unflatten (.vector 4 (.bitvec (.concrete 64)))
        (blk.bytes.extractLsb' p.offsetInBits 256)
      = (readWv h).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [readWv, readWv?, hblk, LLVM.Ty.unflatten]
  show (blk.bytes.extractLsb' p.offsetInBits 256).extractLsb' (i * 64) 64
      = blk.bytes.extractLsb' (p.offsetInBits + 64 * i) 64
  rw [BitVec.extractLsb'_extractLsb'_add_of_le (show i * 64 + 64 ≤ 256 from by omega), Nat.mul_comm i 64]

theorem wv_ld_conforms (p : Pointer) (s : GlobalState) (hs : s.WF) (hp : IsWvPtr s.mem p) :
    wv_ld_spec p s hp := by
  simp only [wv_ld_spec, wv_ld, Cfg.denote]
  refine Firedancer.run_runFunction' _ ?_
  -- nothing is allocated and nothing is written: the load returns `s` itself
  refine ⟨s, ?_, hs.popFrame_equiv⟩
  obtain ⟨blk, hblk, hlen⟩ := hp.1
  have hlive : s.mem.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  peel_load (.vector 4 (.bitvec (.concrete 64))), blk, p, hblk, s
  rw [unflatten_readWv hp hlive]
  simp_return

end Firedancer.Avx512
