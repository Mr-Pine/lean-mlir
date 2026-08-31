import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_from
import SSA.Projects.Firedancer.Ref.Spec.Point

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `r = (x : y : z : t)`: four `fd_f25519_set`s into the point's coordinates,
stated limb for limb like `fd_f25519_set_spec`. The struct field order is
`X, Y, T, Z`, so `z` lands at byte offset 120 and `t` at 80 -- and the splice
chain mirrors the region's call order `X, Y, Z, T`. The block disjointness
carries over from `fd_f25519_set`: no coordinate source may live in `r`'s
block. -/
abbrev fd_ed25519_point_from_spec (r x y z t: Pointer) (s: GlobalState)
    (_ : x.id ≠ r.id) (_ : y.id ≠ r.id) (_ : z.id ≠ r.id) (_ : t.id ≠ r.id) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_from.denote (Ctxt.Valuation.ofHVector
      [.value t, .value z, .value y, .value x, .value r]ₕ))
  let result := StateT.run invocation s

  ∃ oX oY oZ oT : BitVec (5 * 64),
    let outMem := (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
      (r.withOffset 120) oZ).splice (r.withOffset 80) oT
    let output_state : GlobalState := { s with mem := outMem }

    (∃ s' : GlobalState , result = .value ([.value r]ₕ, s') ∧ output_state ≈ s')
    ∧ (∀ i : Fin 5, readLimb? r i output_state.mem = readLimb? x i s.mem)
    ∧ (∀ i : Fin 5, readLimb? (r.withOffset 40) i output_state.mem = readLimb? y i s.mem)
    ∧ (∀ i : Fin 5, readLimb? (r.withOffset 80) i output_state.mem = readLimb? t i s.mem)
    ∧ (∀ i : Fin 5, readLimb? (r.withOffset 120) i output_state.mem = readLimb? z i s.mem)

end Firedancer.Ref
