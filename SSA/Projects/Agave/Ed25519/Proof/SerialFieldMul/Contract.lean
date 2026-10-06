import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Execution
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Correctness

namespace Agave.Ed25519.SerialFieldMul
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
section

/-- Full scalar multiplication contract for the compiler-produced RIR function.
The semantic premises are ordinary allocated input/output objects and nonwrapping
object offsets. The arithmetic premises are exactly the source's input-limb bound.
All carries, word truncations, overflow flags and output bounds are discharged.
-/
theorem kernel_correct (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40) (hb : SmallRange s.mem b 40)
    (hA : Bounded (unsigned (readLimbs s a)))
    (hB : Bounded (unsigned (readLimbs s b))) :
    ∃ output : Fin 5 → BitVec 64,
      kernel.call (kernel.args (.value r) (.value a) (.value b)) s =
        .value (.nil, {s with mem := storeLimbs s.mem r output}) ∧
      decode (unsigned output) % modulus =
        (decode (unsigned (readLimbs s a)) * decode (unsigned (readLimbs s b))) % modulus ∧
      (∀ i, i ≠ 1 → unsigned output i < radix) ∧
      unsigned output 1 < radix + 2^13 ∧ Bounded (unsigned output) := by
  refine ⟨machine (readLimbs s a) (readLimbs s b),
    kernel_call r a b s hwf hr ha hb, machine_correct _ _ hA hB, ?_⟩
  rw [machine_unsigned _ _ hA hB]
  exact mul_output_bounds _ _ hA hB

end
end Agave.Ed25519.SerialFieldMul
