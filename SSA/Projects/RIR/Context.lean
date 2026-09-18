module

public import SSA.Projects.RIR.Ty

namespace LeanMLIR.RIR

@[expose] public section

structure Ctx where
  args : List Ty
  vals : List Ty

inductive Reg (Γ : Ctx) (t : Ty)
  | arg (i : Fin Γ.args.length) (h : Γ.args[i] = t) : Reg Γ t
  | val (i : Fin Γ.vals.length) (h : Γ.vals[i] = t) : Reg Γ t

structure Dst (Γ : Ctx) (t : Ty) where
  i : Fin Γ.vals.length
  h : Γ.vals[i] = t

end

end LeanMLIR.RIR
