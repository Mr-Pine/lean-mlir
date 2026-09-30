module

public import SSA.Projects.RIR.Context
public import SSA.Projects.RIR.OverflowFlags
public import SSA.Projects.RIR.IntPred
public import SSA.Projects.RIR.Semantics.Vals
public import SSA.Projects.RIR.Semantics.Effectful.EffectM

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
  | trunc (flags : OverflowFlags) {w w' : Nat} : UnOp (.bv w) (.bv w')
  | zext (nneg : Bool) {w w' : Nat} : UnOp (.bv w) (.bv w')
  | bswap {w : Nat} : UnOp (.bv w) (.bv w)
  | bitcast {t t' : Ty} (h : t.width = t'.width) : UnOp t t'

inductive BinOp : Ty → Ty → (out : Ty) → Type
  | and {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | or (disjoint : Bool) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | xor {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | add (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | sub (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | mul (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | shl (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | lshr (isExact : Bool) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | ashr (isExact : Bool) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | smin {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | icmp (p : IntPred) {w : Nat} : BinOp (.bv w) (.bv w) (.bv 1)
  |
  vector {l w₁ w₂ w : Nat} (op : BinOp (.bv w₁) (.bv w₂) (.bv w)) :
    BinOp (.vec l w₁) (.vec l w₂) (.vec l w)
  | extractelement {l w wi : Nat} : BinOp (.vec l w) (.bv wi) (.bv w)
  |
  shufflevector {l w : Nat} (indices : Vector (Option (Fin (2 * l))) l) :
    BinOp (.vec l w) (.vec l w) (.vec l w)

inductive TernOp : Ty → Ty → Ty → (out : Ty) → Type
  | select {τ : Ty} : TernOp (.bv 1) τ τ τ
  | insertelement {l w wi : Nat} : TernOp (.vec l w) (.bv w) (.bv wi) (.vec l w) -- (v, x, idx)
  | vpermi2var {l w : Nat} : TernOp (.vec l w) (.vec l w) (.vec l w) (.vec l w) -- (a, idx, b)
  /-- `vpmadd52luq`: `a + (b * c)`, the multiplicands' and the product's low 52 bits. -/
  | vpmadd52l {l : Nat} : TernOp (.vec l 64) (.vec l 64) (.vec l 64) (.vec l 64)
  /-- `vpmadd52huq`: `a + (b * c)`'s high part, of the multiplicands' low 52 bits. -/
  | vpmadd52h {l : Nat} : TernOp (.vec l 64) (.vec l 64) (.vec l 64) (.vec l 64)
  | fshl {w : Nat} : TernOp (.bv w) (.bv w) (.bv w) (.bv w)
  | fshr {w : Nat} : TernOp (.bv w) (.bv w) (.bv w) (.bv w)

inductive Instr (Γ : Ctx)
  | const (v : ⟦τ⟧ᵣ) (dst : Dst Γ τ)
  /-- `llvm.mlir.poison`. -/
  | poison (dst : Dst Γ τ)
  | unop (op : UnOp t₁ t) (dst : Dst Γ t) (a : Reg Γ t₁)
  | binop (op : BinOp t₁ t₂ t) (dst : Dst Γ t) (a : Reg Γ t₁) (b : Reg Γ t₂)
  | ternop (op : TernOp t₁ t₂ t₃ t) (dst : Dst Γ t) (a : Reg Γ t₁) (b : Reg Γ t₂) (c : Reg Γ t₃)
  | load (dst : Dst Γ τ) (p : Reg Γ .ptr)
  | store (p : Reg Γ .ptr) (v : Reg Γ τ)
  /-- A fresh, zeroed block of `bytes` bytes; `dst` points to its start. -/
  | alloca (dst : Dst Γ .ptr) (bytes : Nat)
  /-- `llvm.intr.lifetime.start`: the `bytes` at `p` become live. A no-op. -/
  | lifetimeStart (p : Reg Γ .ptr) (bytes : Nat)
  /-- `llvm.intr.lifetime.end`: the `bytes` at `p` become dead. A no-op. -/
  | lifetimeEnd (p : Reg Γ .ptr) (bytes : Nat)
  /-- The semantics of the calle `f` should generally be `Func.call` -/
  | call {ts us : List Ty} (f : Vals ts → EffectM (Vals us)) (args : Regs Γ ts) (rets : Dsts Γ us)

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
