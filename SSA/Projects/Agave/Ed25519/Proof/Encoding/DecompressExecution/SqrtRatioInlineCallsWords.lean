import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineCallsSteps

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Pow22501 (TightWords)
set_option maxRecDepth 20000
attribute [local irreducible] machine Pow2k.iterateSquare Pow22501.rawWordChain

def callWords (u v : Words) (n : Nat) : Words :=
  let t0 := Pow2k.iterateSquare 1 v
  let t1 := machine t0 v
  let t2 := Pow2k.iterateSquare 1 t1
  let t3 := machine t2 v
  let t4 := machine u t1
  let t5 := machine u t3
  let t6 := (Pow22501.rawWordChain t5).1
  let t7 := t6
  let t8 := Pow2k.iterateSquare 2 t7
  let t9 := machine t5 t8
  let t10 := machine t4 t9
  let t11 := Pow2k.iterateSquare 1 t10
  let t12 := machine v t11
  match n with
  | 0 => t0
  | 1 => t1
  | 2 => t2
  | 3 => t3
  | 4 => t4
  | 5 => t5
  | 6 => t6
  | 7 => t7
  | 8 => t8
  | 9 => t9
  | 10 => t10
  | 11 => t11
  | 12 => t12
  | _ => u

theorem callWords0 (u v : Words) : callWords u v 0 = Pow2k.iterateSquare 1 v := rfl

theorem callWords1 (u v : Words) : callWords u v 1 = machine (callWords u v 0) v := rfl

theorem callWords2 (u v : Words) : callWords u v 2 = Pow2k.iterateSquare 1 (callWords u v 1) := rfl

theorem callWords3 (u v : Words) : callWords u v 3 = machine (callWords u v 2) v := rfl

theorem callWords4 (u v : Words) : callWords u v 4 = machine u (callWords u v 1) := rfl

theorem callWords5 (u v : Words) : callWords u v 5 = machine u (callWords u v 3) := rfl

theorem callWords6 (u v : Words) : callWords u v 6 = (Pow22501.rawWordChain (callWords u v 5)).1 := rfl

theorem callWords7 (u v : Words) : callWords u v 7 = (callWords u v 6) := rfl

theorem callWords8 (u v : Words) : callWords u v 8 = Pow2k.iterateSquare 2 (callWords u v 7) := rfl

theorem callWords9 (u v : Words) : callWords u v 9 = machine (callWords u v 5) (callWords u v 8) := rfl

theorem callWords10 (u v : Words) : callWords u v 10 = machine (callWords u v 4) (callWords u v 9) := rfl

theorem callWords11 (u v : Words) : callWords u v 11 = Pow2k.iterateSquare 1 (callWords u v 10) := rfl

theorem callWords12 (u v : Words) : callWords u v 12 = machine v (callWords u v 11) := rfl

def callExtra (u v : Words) : Words := (Pow22501.rawWordChain (callWords u v 5)).2

theorem callWords_pow (u v : Words) :
    Pow22501.rawWordChain (callWords u v 5) = (callWords u v 6,callExtra u v) := rfl

theorem callWords_candidate (u v : TightWords) :
    callWords u.limbs v.limbs 10 = (wordCandidate u v).limbs := by
  simp only [callWords10,callWords9,callWords8,callWords7,callWords6,callWords5,
    callWords4,callWords3,callWords2,callWords1,callWords0]
  have hp := congrArg Prod.fst (Pow22501.rawWordChain_eq
    (u.mul ((((v.square 1).mul v).square 1).mul v)))
  simp only [TightWords.mul,TightWords.square] at hp
  rw [hp]
  rfl

theorem callWords_check (u v : TightWords) :
    callWords u.limbs v.limbs 12 = (wordCheck u v).limbs := by
  rw [callWords12,callWords11,callWords_candidate]
  rfl

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
