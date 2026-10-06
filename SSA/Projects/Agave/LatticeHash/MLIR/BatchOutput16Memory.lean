/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOutput16
namespace AgaveLatticeHash.MLIR.BatchOutput16
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open BatchReduction16
def sums32 (a b : Vector (BitVec 16) 32) : Vector (BitVec 16) 32 :=
  Vector.ofFn fun i => a[i] + b[i]

/-- The accumulator is updated by the exact lane reduction, and the only
exit is counter 31; all flagged scalar operations are defined. -/
theorem output16Spec_run (V : Input11.Valuation) (s : GlobalState)
    (counter : Nat) (hc : counter < 32) (ptr : Pointer)
    (old delta : Vector (BitVec 16) 32)
    (hcounter : V ⟨16, rfl⟩ = .value (BitVec.ofNat 64 counter))
    (hshift : V ⟨81, rfl⟩ = .value 6#64)
    (hone : V ⟨110, rfl⟩ = .value 1#64)
    (hend : V ⟨100, rfl⟩ = .value 32#64)
    (hptr : gep (V ⟨162, rfl⟩) 1 0 (.value (BitVec.ofNat 64 (64*counter))) = .value ptr)
    (hdelta : delta16 V = delta.map PoisonOr.value)
    (fit : Fits s.mem ptr 512)
    (read : readWord? ptr 512 s.mem = some (packBits old)) :
    StateT.run (output16Spec V) s = .value
      (.inr (if counter = 31 then ⟨12, rfl, .nil⟩
        else next11 V (.value (BitVec.ofNat 64 (counter+1)))),
        {s with mem := s.mem.splice ptr (packBits (sums32 old delta))}) := by
  simp only [output16Spec, hcounter, hshift, hone, hend,
    BatchXof.counter_shift6 counter hc, BatchXof.counter_succ counter hc,
    hptr, hdelta]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector old fit read)]
  simp only [PoisonOr.value_bind]
  rw [show addHalves (old.map PoisonOr.value) (delta.map PoisonOr.value) =
    (sums32 old delta).map PoisonOr.value from addHalves_defined old delta]
  rw [EffectM.run_bind, run_liftM (s := s)
    (run_store (flatten_packBits (sums32 old delta)) fit)]
  simp only [PoisonOr.value_bind, BatchXof.counter_exit counter hc]
  by_cases h : counter = 31 <;> simp [h]
end AgaveLatticeHash.MLIR.BatchOutput16
