import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec
import SSA.Projects.RIR.Semantics.Instruction

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR

def vec4 (a b c d : Spec.Word) : Ty.denote (.vec 4 64) :=
  Ty.wrap #v[a, b, c, d]

def pack4 (a b c d : Spec.Word) : BitVec 256 := d ++ c ++ b ++ a

theorem vec4_insert (v : Ty.denote (.vec 4 64)) (a b c d : Spec.Word) :
    Operation.insertelement
      (Operation.insertelement
        (Operation.insertelement
          (Operation.insertelement v (.value a) (.value 0#64))
          (.value b) (.value 1#64))
        (.value c) (.value 2#64))
      (.value d) (.value 3#64) = vec4 a b c d := by
  ext i hi
  interval_cases i <;> simp [Operation.insertelement, vec4, Ty.wrap_vec]

theorem vec4_add (a b c d e f g h : Spec.Word) :
    (BinOp.vector (BinOp.add {})).compute (vec4 a b c d) (vec4 e f g h) =
      vec4 (a + e) (b + f) (c + g) (d + h) := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, vec4, Ty.wrap_vec, Operation.add]

theorem vec4_flatten (a b c d : Spec.Word) :
    Ty.flatten (.vec 4 64) (vec4 a b c d) = .value (pack4 a b c d) := by
  simp [vec4, Ty.flatten_wrap_vec, pack4, BitVec.packLanes]
  have hz : 0#0 ++ d = d := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_append, ite_eq_left hi]
  rw [hz]

theorem vec4_unflatten (a b c d : Spec.Word) :
    Ty.unflatten (.vec 4 64) (pack4 a b c d) = vec4 a b c d :=
  Ty.unflatten_flatten (vec4_flatten a b c d)

end Agave.Ed25519.SHA512.Execution.Avx2
