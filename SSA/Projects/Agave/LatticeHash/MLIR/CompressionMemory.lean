/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Agave.LatticeHash.Compression

namespace AgaveLatticeHash.MLIR.CompressionExit
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression

/-- Memory left by the first `count` output stores in ascending state order. -/
def outputMem {n : Nat} (out : Pointer) (v : State (Vector Word n)) : Nat → MemoryState → MemoryState
  | 0, m => m
  | k+1, m => (outputMem out v k m).splice
      (out.withOffset (BitVec.ofNat 64 (4*n*k))) (packBits (v (Fin.ofNat 16 k)))

private def writeBody {n : Nat} (out : Pointer) (v : State (Vector Word n)) : Nat → EffectM (HVector toType ([] : List SLLVM.Ty))
  | 0 => pure []ₕ
  | k+1 => do
    let _ ← writeBody out v k
    let _ ← (liftM (store (.value (out.withOffset (BitVec.ofNat 64 (4*n*k))))
      (.vector n (.bitvec (.concrete 32))) ((v (Fin.ofNat 16 k)).map PoisonOr.value)) : EffectM _)
    pure []ₕ

theorem fits_outputMem {n : Nat} (out : Pointer) (v : State (Vector Word n))
    (k : Nat) {m : MemoryState} {p : Pointer} {w : Nat} (hp : Fits m p w) :
    Fits (outputMem out v k m) p w := by
  induction k with
  | zero => exact hp
  | succ k ih => exact fits_splice ih

private theorem writeBody_run {n : Nat} (out : Pointer) (v : State (Vector Word n))
    (count : Nat) (s : GlobalState)
    (hfit : ∀ k < count, Fits s.mem (out.withOffset (BitVec.ofNat 64 (4*n*k))) (32*n)) :
    StateT.run (writeBody out v count) s = .value ([]ₕ, {s with mem := outputMem out v count s.mem}) := by
  induction count with
  | zero => rfl
  | succ k ih =>
    have hk := hfit k (by omega)
    have hprev := ih (fun i hi => hfit i (by omega))
    simp -failIfUnchanged only [writeBody, EffectM.run_bind, hprev, PoisonOr.value_bind]
    rw [run_liftM (s := {s with mem := outputMem out v k s.mem}) (run_store (flatten_packBits (v (Fin.ofNat 16 k)))
      (fits_outputMem out v k hk))]
    rfl

/-- Other allocations are unchanged by all sixteen output stores. -/
theorem outputMem_frame {n : Nat} (out : Pointer) (v : State (Vector Word n))
    (count : Nat) (m : MemoryState) (q : BlockId) (hq : q ≠ out.id) :
    (outputMem out v count m).live? q = m.live? q := by
  induction count with
  | zero => rfl
  | succ k ih =>
    exact (live?_splice_ne (show (out.withOffset _).id ≠ q from Ne.symm hq)).trans ih

end AgaveLatticeHash.MLIR.CompressionExit
