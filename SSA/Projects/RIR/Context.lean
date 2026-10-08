module

public import SSA.Projects.RIR.Ty

namespace LeanMLIR.RIR

@[expose] public section

/-- A function's registers: `args`, and `n` values of types `vals`. The count is a literal, so
indices `Fin Γ.n` never make the elaborator walk `vals`. Argument `i` is named `%arg(argBase + i)`
and value `i` is `%(valBase + i)`, as the region numbers them. -/
structure Ctx where
  n : Nat
  args : List Ty
  vals : List Ty
  hn : vals.length = n
  argBase : Nat
  valBase : Nat

/-- The type of value register `i`. -/
abbrev Ctx.ty (Γ : Ctx) (i : Fin Γ.n) : Ty :=
  Γ.vals[i.1]'(Nat.lt_of_lt_of_eq i.2 Γ.hn.symm)

inductive Reg (Γ : Ctx) (t : Ty)
  | arg (i : Fin Γ.args.length) (h : Γ.args[i] = t) : Reg Γ t
  | val (i : Fin Γ.n) (h : Γ.ty i = t) : Reg Γ t

structure Dst (Γ : Ctx) (t : Ty) where
  i : Fin Γ.n
  h : Γ.ty i = t

end

end LeanMLIR.RIR
