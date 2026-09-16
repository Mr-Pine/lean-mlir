/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_mul4
import SSA.Projects.Firedancer.Ref.Spec.Apart

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Four `fd_f25519_mul`s in order. The destinations do not overlap, and no source
shares a block with a destination, so every call reads its operands unwritten. -/
abbrev fd_f25519_mul4_spec (r1 a1 b1 r2 a2 b2 r3 a3 b3 r4 a4 b4 : Pointer) (s : GlobalState)
    (_hdst : [r1, r2, r3, r4].Pairwise FieldApart)
    (_hsrc : ∀ d ∈ [r1, r2, r3, r4], ∀ x ∈ [a1, b1, a2, b2, a3, b3, a4, b4], d.id ≠ x.id)
    (hr1 : IsFieldElemPtr s.mem r1) (ha1 : IsFieldElemPtr s.mem a1) (hb1 : IsFieldElemPtr s.mem b1)
    (hr2 : IsFieldElemPtr s.mem r2) (ha2 : IsFieldElemPtr s.mem a2) (hb2 : IsFieldElemPtr s.mem b2)
    (hr3 : IsFieldElemPtr s.mem r3) (ha3 : IsFieldElemPtr s.mem a3) (hb3 : IsFieldElemPtr s.mem b3)
    (hr4 : IsFieldElemPtr s.mem r4) (ha4 : IsFieldElemPtr s.mem a4)
    (hb4 : IsFieldElemPtr s.mem b4) : Prop :=
  let invocation :=
    runFunction
      (fd_f25519_mul4.denote
        (Ctxt.Valuation.ofHVector
          [.value b4, .value a4, .value r4, .value b3, .value a3, .value r3, .value b2, .value a2,
            .value r2, .value b1, .value a1, .value r1]ₕ))
  let result := StateT.run invocation s
  ∃ o1 o2 o3 o4 : BitVec (5 * 64),
    let outMem := (((s.mem.splice r1 o1).splice r2 o2).splice r3 o3).splice r4 o4
    let output_state : GlobalState := { s with mem := outMem }
    have ho1 : IsFieldElemPtr outMem r1 :=
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr1)))
    have ho2 : IsFieldElemPtr outMem r2 :=
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr2)))
    have ho3 : IsFieldElemPtr outMem r3 :=
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr3)))
    have ho4 : IsFieldElemPtr outMem r4 :=
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr4)))
    (∃ s' : GlobalState, result = .value ([]ₕ, s') ∧ output_state ≈ s') ∧
      readFieldElem ho1 = readFieldElem ha1 * readFieldElem hb1 ∧
      LimbBounds ho1 ∧
      readFieldElem ho2 = readFieldElem ha2 * readFieldElem hb2 ∧
      LimbBounds ho2 ∧
      readFieldElem ho3 = readFieldElem ha3 * readFieldElem hb3 ∧
      LimbBounds ho3 ∧ readFieldElem ho4 = readFieldElem ha4 * readFieldElem hb4 ∧ LimbBounds ho4

end Firedancer.Ref
