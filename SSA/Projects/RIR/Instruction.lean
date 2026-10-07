module

public import SSA.Projects.RIR.Aggregate
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
  | extractvalue (path : AggregatePath s t) : UnOp s t
  | gepConst (byteOff : Nat) : UnOp .ptr .ptr
  | trunc (flags : OverflowFlags) {w w' : Nat} : UnOp (.bv w) (.bv w')
  | zext (nneg : Bool) {w w' : Nat} : UnOp (.bv w) (.bv w')
  | sext {w w' : Nat} : UnOp (.bv w) (.bv w')
  /-- Apply a scalar operation independently, preserving lane-local poison. -/
  | vector {l w w' : Nat} (op : UnOp (.bv w) (.bv w')) : UnOp (.vec l w) (.vec l w')
  | bswap {w : Nat} : UnOp (.bv w) (.bv w)
  | bitcast {t t' : Ty} (h : t.width = t'.width) : UnOp t t'

inductive BinOp : Ty → Ty → (out : Ty) → Type
  | insertvalue (path : AggregatePath s t) : BinOp s t s
  | and {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | or (disjoint : Bool) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | xor {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | add (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | sub (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  /-- Unsigned subtraction clamped to zero, propagating either operand's poison. -/
  | usubSat {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | mul (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | shl (flags : OverflowFlags) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | lshr (isExact : Bool) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | ashr (isExact : Bool) {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | smin {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | icmp (p : IntPred) {w : Nat} : BinOp (.bv w) (.bv w) (.bv 1)
  /-- Same-allocation pointer equality, or inequality when `isNe` is true.
  Comparisons across allocation identities are outside RIR's address-free pointer model. -/
  | ptrCmp (isNe : Bool) : BinOp .ptr .ptr (.bv 1)
  /-- Three-way integer comparison, with an independently typed result width. -/
  | cmp (signed : Bool) {w wr : Nat} : BinOp (.bv w) (.bv w) (.bv wr)
  |
  vector {l w₁ w₂ w : Nat} (op : BinOp (.bv w₁) (.bv w₂) (.bv w)) :
    BinOp (.vec l w₁) (.vec l w₂) (.vec l w)
  | extractelement {l w wi : Nat} : BinOp (.vec l w) (.bv wi) (.bv w)
  |
  shufflevector {l₁ l₂ w : Nat} (indices : Vector (Option (Fin (2 * l₁))) l₂) :
    BinOp (.vec l₁ w) (.vec l₁ w) (.vec l₂ w)

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
  |
  vector {l w₁ w₂ w₃ w : Nat} (op : TernOp (.bv w₁) (.bv w₂) (.bv w₃) (.bv w)) :
    TernOp (.vec l w₁) (.vec l w₂) (.vec l w₃) (.vec l w)

/-- A byte offset or a scaled, signed LLVM GEP index. Pointer index width is 64. -/
inductive GepIndex (Γ : Ctx)
  | constant (byteOff : Int)
  | scaled {w : Nat} (stride : Nat) (index : Reg Γ (.bv w))

inductive Instr (Γ : Ctx)
  /-- A noalias scope declaration is metadata, with no runtime effect. -/
  | noaliasScopeDecl (scope : String)
  /-- `fence syncscope("singlethread") seq_cst`, retained explicitly.
  In sequential RIR it changes no registers or memory. This is not a model
  of inter-thread synchronization, signal handlers, or volatile event traces. -/
  | fenceSingleThread
  /-- Unflagged GEP: signed indices and wrapping pointer-index arithmetic. -/
  | gep (dst : Dst Γ .ptr) (base : Reg Γ .ptr) (indices : List (GepIndex Γ))
  /-- `inbounds nusw nuw` on the explicit live-allocation subset. -/
  | gepInbounds (dst : Dst Γ .ptr) (base : Reg Γ .ptr) (indices : List (GepIndex Γ))
  | const (v : ⟦τ⟧ᵣ) (dst : Dst Γ τ)
  /-- `llvm.mlir.poison`. -/
  | poison (dst : Dst Γ τ)
  /-- `llvm.assume`: a false or poison condition causes immediate undefined behavior. -/
  | assume (cond : Reg Γ (.bv 1))
  | unop (op : UnOp t₁ t) (dst : Dst Γ t) (a : Reg Γ t₁)
  | binop (op : BinOp t₁ t₂ t) (dst : Dst Γ t) (a : Reg Γ t₁) (b : Reg Γ t₂)
  | ternop (op : TernOp t₁ t₂ t₃ t) (dst : Dst Γ t) (a : Reg Γ t₁) (b : Reg Γ t₂) (c : Reg Γ t₃)
  | load (dst : Dst Γ τ) (p : Reg Γ .ptr)
  /-- An LLVM monotonic atomic byte load, retaining its source ordering marker.
  RIR models the value read in one sequential execution. Relating this instruction
  to LLVM requires exclusive access to the byte during the execution; this is not
  a model of concurrent atomic histories or inter-thread synchronization. -/
  | loadMonotonic (dst : Dst Γ (.bv 8)) (p : Reg Γ .ptr)
  | store (p : Reg Γ .ptr) (v : Reg Γ τ)
  | memset (dst : Reg Γ .ptr) (val : Reg Γ (.bv 8)) (len : Reg Γ (.bv w))
  | memcpy (dst : Reg Γ .ptr) (src : Reg Γ .ptr) (count : Reg Γ (.bv w))
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
  /-- Reaching `llvm.unreachable` is immediate undefined behavior. -/
  | unreachable
  | br (target : Jump Γ blockTys)
  | condBr (cond : Reg Γ (.bv 1)) (ttrue : Jump Γ blockTys) (tfalse : Jump Γ blockTys)
  |
  switch (val : Reg Γ t) (defaultTarget : Jump Γ blockTys)
    (branches : List (⟦t⟧ᵣ × Jump Γ blockTys))

end

end LeanMLIR.RIR
