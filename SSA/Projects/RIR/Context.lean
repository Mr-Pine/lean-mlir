module

public import SSA.Projects.RIR.Ty

namespace LeanMLIR.RIR

@[expose] public section

/-- A function's registers: `args`, and `n` values of types `vals`. The count is a literal, so
indices `Fin Γ.n` never make the elaborator walk `vals`. -/
structure Ctx where
  n : Nat
  args : List Ty
  vals : List Ty
  hn : vals.length = n

/-- The type of value register `i`. -/
abbrev Ctx.ty (Γ : Ctx) (i : Fin Γ.n) : Ty :=
  Γ.vals[i.1]'(Nat.lt_of_lt_of_eq i.2 Γ.hn.symm)

inductive Reg (Γ : Ctx) (t : Ty)
  | arg (i : Fin Γ.args.length) (h : Γ.args[i] = t) : Reg Γ t
  | val (i : Fin Γ.n) (h : Γ.ty i = t) : Reg Γ t

structure Dst (Γ : Ctx) (t : Ty) where
  i : Fin Γ.n
  h : Γ.ty i = t

/-- Registers are equal when their kind and index are: `decide` tells `%arg0 ≠ %2`. -/
instance : DecidableEq (Reg Γ t)
  | .arg i _, .arg j _ => decidable_of_iff (i = j) ⟨fun h => h ▸ rfl, Reg.arg.inj⟩
  | .val i _, .val j _ => decidable_of_iff (i = j) ⟨fun h => h ▸ rfl, Reg.val.inj⟩
  | .arg _ _, .val _ _ => isFalse nofun
  | .val _ _, .arg _ _ => isFalse nofun

end

end LeanMLIR.RIR
