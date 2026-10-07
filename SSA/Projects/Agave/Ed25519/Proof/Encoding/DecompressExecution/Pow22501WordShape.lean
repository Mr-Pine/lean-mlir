import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501

/-! Definitional folds for the exact two outputs of the addition chain. Keeping
these equations separate avoids re-expanding every intermediate field value
while erasing the executed function's stack frame. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
open SerialFieldMul
attribute [local irreducible] machine Pow2k.iterateSquare
set_option maxRecDepth 20000

theorem rawWordChain_first (x : Words) :
  let t0 := Pow2k.iterateSquare 1 x
  let t1a := Pow2k.iterateSquare 1 t0
  let t1 := Pow2k.iterateSquare 1 t1a
  let t2 := machine x t1
  let t3 := machine t0 t2
  let t4 := Pow2k.iterateSquare 1 t3
  let t5 := machine t2 t4
  let t6 := Pow2k.iterateSquare 5 t5
  let t7 := machine t6 t5
  let t8 := Pow2k.iterateSquare 10 t7
  let t9 := machine t8 t7
  let t10 := Pow2k.iterateSquare 20 t9
  let t11 := machine t10 t9
  let t12 := Pow2k.iterateSquare 10 t11
  let t13 := machine t12 t7
  let t14 := Pow2k.iterateSquare 50 t13
  let t15 := machine t14 t13
  let t16 := Pow2k.iterateSquare 100 t15
  let t17 := machine t16 t15
  let t18 := Pow2k.iterateSquare 50 t17
  let t19 := machine t18 t13
  t19 = (rawWordChain x).1 := by
  rfl

theorem rawWordChain_second (x : Words) :
  let t0 := Pow2k.iterateSquare 1 x
  let t1a := Pow2k.iterateSquare 1 t0
  let t1 := Pow2k.iterateSquare 1 t1a
  let t2 := machine x t1
  let t3 := machine t0 t2
  t3 = (rawWordChain x).2 := by
  rfl

/-- Exact limb value produced by each of the twenty-one helper calls. -/
def wordAt (x : Words) (n : Nat) : Words :=
  let t0 := Pow2k.iterateSquare 1 x
  let t1a := Pow2k.iterateSquare 1 t0
  let t1 := Pow2k.iterateSquare 1 t1a
  let t2 := machine x t1
  let t3 := machine t0 t2
  let t4 := Pow2k.iterateSquare 1 t3
  let t5 := machine t2 t4
  let t6 := Pow2k.iterateSquare 5 t5
  let t7 := machine t6 t5
  let t8 := Pow2k.iterateSquare 10 t7
  let t9 := machine t8 t7
  let t10 := Pow2k.iterateSquare 20 t9
  let t11 := machine t10 t9
  let t12 := Pow2k.iterateSquare 10 t11
  let t13 := machine t12 t7
  let t14 := Pow2k.iterateSquare 50 t13
  let t15 := machine t14 t13
  let t16 := Pow2k.iterateSquare 100 t15
  let t17 := machine t16 t15
  let t18 := Pow2k.iterateSquare 50 t17
  let t19 := machine t18 t13
  match n with
  | 0 => t0
  | 1 => t1a
  | 2 => t1
  | 3 => t2
  | 4 => t3
  | 5 => t4
  | 6 => t5
  | 7 => t6
  | 8 => t7
  | 9 => t8
  | 10 => t9
  | 11 => t10
  | 12 => t11
  | 13 => t12
  | 14 => t13
  | 15 => t14
  | 16 => t15
  | 17 => t16
  | 18 => t17
  | 19 => t18
  | 20 => t19
  | _ => x

theorem wordAt0 (x : Words) : wordAt x 0 = Pow2k.iterateSquare 1 x := rfl

theorem wordAt1 (x : Words) : wordAt x 1 = Pow2k.iterateSquare 1 (wordAt x 0) := rfl

theorem wordAt2 (x : Words) : wordAt x 2 = Pow2k.iterateSquare 1 (wordAt x 1) := rfl

theorem wordAt3 (x : Words) : wordAt x 3 = machine x (wordAt x 2) := rfl

theorem wordAt4 (x : Words) : wordAt x 4 = machine (wordAt x 0) (wordAt x 3) := rfl

theorem wordAt5 (x : Words) : wordAt x 5 = Pow2k.iterateSquare 1 (wordAt x 4) := rfl

theorem wordAt6 (x : Words) : wordAt x 6 = machine (wordAt x 3) (wordAt x 5) := rfl

theorem wordAt7 (x : Words) : wordAt x 7 = Pow2k.iterateSquare 5 (wordAt x 6) := rfl

theorem wordAt8 (x : Words) : wordAt x 8 = machine (wordAt x 7) (wordAt x 6) := rfl

theorem wordAt9 (x : Words) : wordAt x 9 = Pow2k.iterateSquare 10 (wordAt x 8) := rfl

theorem wordAt10 (x : Words) : wordAt x 10 = machine (wordAt x 9) (wordAt x 8) := rfl

theorem wordAt11 (x : Words) : wordAt x 11 = Pow2k.iterateSquare 20 (wordAt x 10) := rfl

theorem wordAt12 (x : Words) : wordAt x 12 = machine (wordAt x 11) (wordAt x 10) := rfl

theorem wordAt13 (x : Words) : wordAt x 13 = Pow2k.iterateSquare 10 (wordAt x 12) := rfl

theorem wordAt14 (x : Words) : wordAt x 14 = machine (wordAt x 13) (wordAt x 8) := rfl

theorem wordAt15 (x : Words) : wordAt x 15 = Pow2k.iterateSquare 50 (wordAt x 14) := rfl

theorem wordAt16 (x : Words) : wordAt x 16 = machine (wordAt x 15) (wordAt x 14) := rfl

theorem wordAt17 (x : Words) : wordAt x 17 = Pow2k.iterateSquare 100 (wordAt x 16) := rfl

theorem wordAt18 (x : Words) : wordAt x 18 = machine (wordAt x 17) (wordAt x 16) := rfl

theorem wordAt19 (x : Words) : wordAt x 19 = Pow2k.iterateSquare 50 (wordAt x 18) := rfl

theorem wordAt20 (x : Words) : wordAt x 20 = machine (wordAt x 19) (wordAt x 14) := rfl

theorem wordAt20_eq_first (x : Words) : wordAt x 20 = (rawWordChain x).1 := rfl

theorem wordAt4_eq_second (x : Words) : wordAt x 4 = (rawWordChain x).2 := rfl

end Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
