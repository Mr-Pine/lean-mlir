module

public import SSA.Projects.RIR.Context
public import SSA.Projects.RIR.OverflowFlags
public import SSA.Projects.RIR.IntPred

namespace LeanMLIR.RIR

@[expose] public section

inductive Regs (Γ : Ctx) : List Ty → Type
  | nil : Regs Γ []
  | cons (r : Reg Γ t) (rs : Regs Γ ts) : Regs Γ (t :: ts)

/-- Registers written together, typed by their list of types: a block's parameters. -/
inductive Dsts (Γ : Ctx) : List Ty → Type
  | nil : Dsts Γ []
  | cons (d : Dst Γ t) (ds : Dsts Γ ts) : Dsts Γ (t :: ts)

inductive UnOp : Ty → (out : Ty) → Type
  | gepConst (byteOff : Nat) : UnOp .ptr .ptr

inductive BinOp : Ty → Ty → (out : Ty) → Type
  | and {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | add (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | sub (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | mul (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | lshr (isExact : Bool) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | smin {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | icmp (p : IntPred) {w : Nat} : BinOp (.bv w) (.bv w) (.bv 1)

inductive TernOp : Ty → Ty → Ty → (out : Ty) → Type
  | select {τ : Ty} : TernOp (.bv 1) τ τ τ

inductive Instr (Γ : Ctx)
  | const (v : BitVec w) (dst : Dst Γ (Ty.bv w))
  | unop (op : UnOp t₁ t) (dst : Dst Γ t) (a : Reg Γ t₁)
  | binop (op : BinOp t₁ t₂ t) (dst : Dst Γ t) (a : Reg Γ t₁) (b : Reg Γ t₂)
  | ternop (op : TernOp t₁ t₂ t₃ t) (dst : Dst Γ t) (a : Reg Γ t₁) (b : Reg Γ t₂) (c : Reg Γ t₃)
  | load (dst : Dst Γ τ) (p : Reg Γ .ptr)
  | store (p : Reg Γ .ptr) (v : Reg Γ τ)

-- call, etc...

/-- A jump to block `target`, with one argument per parameter of the target (`blockTys target`). -/
structure Jump (Γ : Ctx) (blockTys : Fin n → List Ty) where
  target : Fin n
  args : Regs Γ (blockTys target)

inductive Exit (Γ : Ctx) (tRets : List Ty) (blockTys : Fin n → List Ty)
  | ret (vs : Regs Γ tRets)
  | br (target : Jump Γ blockTys)
  | condBr (cond : Reg Γ (.bv 1)) (ttrue : Jump Γ blockTys) (tfalse : Jump Γ blockTys)
  |
  switch (val : Reg Γ t) (defaultTarget : Jump Γ blockTys)
    (branches : List (⟦t⟧ᵣ × Jump Γ blockTys))

end

end LeanMLIR.RIR
