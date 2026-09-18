module

public import SSA.Projects.RIR.Context

namespace LeanMLIR.RIR

@[expose] public section

inductive Regs (Γ : Ctx) : List Ty → Type
  | nil : Regs Γ []
  | cons (r : Reg Γ t) (rs : Regs Γ ts) : Regs Γ (t :: ts)

inductive BinOp : Ty → Ty → (out : Ty) → Type
  | and {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | smin {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)

inductive Instr (Γ : Ctx)
  | const (v : BitVec w) (dst : Dst Γ (Ty.bv w))
  | binop (op : BinOp t₁ t₂ t) (dst : Dst Γ t) (a : Reg Γ t₁) (b : Reg Γ t₂)

-- call, etc...

inductive Exit (Γ : Ctx) (tRets : List Ty) (blockParams : Fin n → List (Fin Γ.vals.length))
  | ret (vs : Regs Γ tRets)

end

end LeanMLIR.RIR
