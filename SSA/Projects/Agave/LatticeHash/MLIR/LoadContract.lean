/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Firedancer.Proof.Memory

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)

/-- Load contract over the public `Fits`/`readWord` memory interface. This
avoids exposing live-block witnesses in the compression loop invariant. -/
theorem run_load_readWord {t : LLVM.Ty} {m : MemoryState} {p : Pointer}
    (hp : Fits m p (LLVM.Ty.width t)) :
    (load (.value p) t).run m =
      .value (LLVM.Ty.unflatten t (readWord hp), m) := by
  obtain ⟨blk, hblk, hlen⟩ := hp
  rw [run_load hblk hlen]
  congr 2
  simp only [readWord, readWord?, MemoryState.live?, hblk, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.get_some]

/-- An initialized word plus a bounds proof determine an actual SLLVM load. -/
theorem run_load_of_readWord {t : LLVM.Ty} {m : MemoryState} {p : Pointer}
    (hp : Fits m p (LLVM.Ty.width t)) (bits : BitVec (LLVM.Ty.width t))
    (hr : readWord hp = bits) :
    (load (.value p) t).run m = .value (LLVM.Ty.unflatten t bits, m) := by
  rw [run_load_readWord hp, hr]

end AgaveLatticeHash.MLIR
