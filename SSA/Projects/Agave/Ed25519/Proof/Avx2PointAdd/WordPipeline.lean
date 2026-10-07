import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Word
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionPacking

/-! Physical word operations used at the point-add caller boundary. All
subtractions retain their wrapping u32 meaning; bounds are supplied only when
refining these words to natural limbs. -/
namespace Agave.Ed25519.Avx2PointAdd.Execution
open Avx2FieldMul.Execution

theorem word_add_left_comm (x y z : BitVec n) : x + (y + z) = y + (x + z) := by
  rw [← BitVec.add_assoc, BitVec.add_comm x y, BitVec.add_assoc]

def rawPrepare (a : Blocks) : Blocks := fun k =>
  let e := word (twiceP ⟨2 * k.val, by omega⟩)
  let o := word (twiceP ⟨2 * k.val + 1, by omega⟩)
  #v[(a k)[1] + (e - (a k)[0]), (a k)[1] + (a k)[0],
     (a k)[3] + (o - (a k)[2]), (a k)[3] + (a k)[2],
     (a k)[4], (a k)[5], (a k)[6], (a k)[7]]

def rawDiffSum (a : Blocks) : Blocks := fun k =>
  let e := word (twiceP ⟨2 * k.val, by omega⟩)
  let o := word (twiceP ⟨2 * k.val + 1, by omega⟩)
  #v[(a k)[1] + (e - (a k)[0]), (a k)[1] + (a k)[0],
     (a k)[3] + (o - (a k)[2]), (a k)[3] + (a k)[2],
     (a k)[5] + (e - (a k)[4]), (a k)[5] + (a k)[4],
     (a k)[7] + (o - (a k)[6]), (a k)[7] + (a k)[6]]

def rawNegate (a : Blocks) : Blocks := fun k =>
  let e := word (twiceP ⟨2 * k.val, by omega⟩)
  let o := word (twiceP ⟨2 * k.val + 1, by omega⟩)
  #v[(a k)[1], (a k)[0], (a k)[3], (a k)[2],
     (a k)[4], e - (a k)[5], (a k)[6], o - (a k)[7]]

def rawABDC (a : Blocks) : Blocks := fun k =>
  #v[(a k)[0], (a k)[1], (a k)[2], (a k)[3],
     (a k)[5], (a k)[4], (a k)[7], (a k)[6]]

def rawADDA (a : Blocks) : Blocks := fun k =>
  #v[(a k)[0], (a k)[5], (a k)[2], (a k)[7],
     (a k)[5], (a k)[0], (a k)[7], (a k)[2]]

def rawCBCB (a : Blocks) : Blocks := fun k =>
  #v[(a k)[4], (a k)[1], (a k)[6], (a k)[3],
     (a k)[4], (a k)[1], (a k)[6], (a k)[3]]

def rawMultiply (a b : Blocks) : Blocks :=
  Reduce64.Execution.packedOutput (rawColumns4 a b)

def rawAdd (a b : Blocks) : Blocks :=
  let t := rawDiffSum (rawABDC (rawMultiply (rawPrepare a) b))
  rawMultiply (rawADDA t) (rawCBCB t)

def rawSub (a b : Blocks) : Blocks := rawAdd a (rawNegate b)

end Agave.Ed25519.Avx2PointAdd.Execution
