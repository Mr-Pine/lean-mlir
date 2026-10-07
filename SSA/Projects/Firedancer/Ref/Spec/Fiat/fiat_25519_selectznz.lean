module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_selectznz
public import SSA.Projects.Firedancer.Ref.Spec.F25519

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fiat_25519_add` adds limbwise without carrying, so the result is a *loose*
field element: the value is the sum, but the limbs are only bounded by the loose
bound `fiat_25519_carry` accepts. -/
abbrev fiat_25519_selectznz_spec (r : Pointer) (c : BitVec 8) (x y : Pointer) (s : GlobalState)
    (hr : IsFieldElemPtr s.mem r) (hx : IsFieldElemPtr s.mem x) (hy : IsFieldElemPtr s.mem y) :
    Prop :=
  let invocation :=
    runFunction
      (fiat_25519_selectznz.denote
        (Ctxt.Valuation.ofHVector [.value y, .value x, .value c, .value r]ₕ))
  let result := StateT.run invocation s
  let xIn := readFieldElem hx
  let yIn := readFieldElem hy
  let outPtr := if (c = 0) then x else y
  have houtPtr : IsFieldElemPtr s.mem outPtr := by grind only
  let out := if (c = 0) then xIn else yIn
  let output_state : GlobalState :=
    { s with mem := s.mem.splice r (packLimbs (fun i => readLimb i houtPtr)) }
  readFieldElem (m := output_state.mem) (isFieldElemPtr_splice hr) = out ∧
    (∃ s' : GlobalState, result = .value ([]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref
