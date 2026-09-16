/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_sub_with_opts
import SSA.Projects.Firedancer.Ref.Proof.RefWF
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Spec.Point.Add
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_sub_with_opts

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = a.addPrecomputedPartial b.neg` for `b_is_precomputed = skip_last_mul = 1`:
`fd_ed25519_point_add_with_opts` with `b`'s `X` and `Y` exchanged and the sign of
`r7` flipped. Stored `X, Y, Z, T` (byte offsets 0, 40, 120, 80), all loose.
`b_Z_is_one ≠ 0` takes `b`'s `Z` as 1 without reading it. `a` and `b` are read only
before the first store to `r`, so either may overlap it. `@fd_f25519_k`'s address is
taken but not read, hence `RefWF []`. The input bounds are the callees', as for add. -/
abbrev fd_ed25519_point_sub_with_opts_spec (r a b : Pointer) (bZ1 bPre skip : BitVec 32)
    (s : GlobalState) (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a)
    (hb : IsPointPtr s.mem b) : Prop :=
  let invocation :=
    runFunction
      (fd_ed25519_point_sub_with_opts.denote
        (Ctxt.Valuation.ofHVector
          [.value skip, .value bPre, .value bZ1, .value b, .value a, .value r]ₕ))
  let result := StateT.run invocation s
  let Q := PrecomputedPoint.ofSlots (readPoint hb)
  bPre = 1 →
    skip = 1 →
      s.RefWF [] →
        LimbBounds (isCoordPtr ha 0) →
          LimbBounds (isCoordPtr ha 1) →
            LimbBounds.Loose (isCoordPtr ha 2) →
              LimbBounds (isCoordPtr ha 3) →
                (∀ i, LimbBounds.Loose (isCoordPtr hb i)) →
                  ∃ s' : GlobalState,
                    result = .value ([.value r]ₕ, s') ∧
                      ∃ oX oY oZ oT : BitVec (5 * 64),
                        let outMem :=
                          (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
                                (r.withOffset 120) oZ).splice
                            (r.withOffset 80) oT
                        let output_state : GlobalState := { s with mem := outMem }
                        have hpt : IsPointPtr outMem r :=
                          isPointPtr_splice
                            (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))
                        output_state ≈ s' ∧
                          readPoint hpt =
                            (readPoint ha).addPrecomputedPartial
                              (if bZ1 = 0 then Q else { Q with Z := 1 }).neg ∧
                          ∀ i, LimbBounds.Loose (isCoordPtr hpt i)

end Firedancer.Ref
