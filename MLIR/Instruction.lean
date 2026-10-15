module

public import MLIR.Context
public import MLIR.OverflowFlags
public import MLIR.IntPred
public import MLIR.Semantics.Vals
public import MLIR.Semantics.Effectful.EffectM

namespace MLIR

@[expose] public section

inductive Regs (Γ : Ctx) : List Ty → Type
  | nil : Regs Γ []
  | cons (r : Reg Γ t) (rs : Regs Γ ts) : Regs Γ (t :: ts)

/-- Registers written together, typed by their list of types: a block's parameters. -/
inductive Dsts (Γ : Ctx) : List Ty → Type
  | nil : Dsts Γ []
  | cons (d : Dst Γ t) (ds : Dsts Γ ts) : Dsts Γ (t :: ts)

inductive UnOp : Ty → (out : Ty) → Type
  | gepConst (flags : GepFlags) (byteOff : Int) : UnOp .ptr .ptr
  | trunc (flags : OverflowFlags) {w w' : Nat} : UnOp (.bv w) (.bv w')
  | zext (nneg : Bool) {w w' : Nat} : UnOp (.bv w) (.bv w')
  | sext {w w' : Nat} : UnOp (.bv w) (.bv w')
  | bswap {w : Nat} : UnOp (.bv w) (.bv w)
  /-- An empty inline `asm` whose output is tied to its input: the input. -/
  | copy {t : Ty} : UnOp t t
  | cttz (isZeroPoison : Bool) {w : Nat} : UnOp (.bv w) (.bv w)
  | abs (isIntMinPoison : Bool) {w : Nat} : UnOp (.bv w) (.bv w)
  | reduceOr {l w : Nat} : UnOp (.vec l w) (.bv w)
  | reduceAnd {l w : Nat} : UnOp (.vec l w) (.bv w)
  | reduceAdd {l w : Nat} : UnOp (.vec l w) (.bv w)
  | bitcast {t t' : Ty} (h : t.width = t'.width) : UnOp t t'
  |
  extractvalue (indices : List Nat) (tCont tVal : Ty) (h : tCont.memberType indices == some tVal) :
    UnOp tCont tVal
  | vector {l w w' : Nat} (op : UnOp (.bv w) (.bv w')) : UnOp (.vec l w) (.vec l w')
  /-- `op` on each lane of a pointer vector, `vector<n x ptr>` as `.array n .ptr`. -/
  | ptrLanes {n : Nat} (op : UnOp .ptr .ptr) : UnOp (.array n .ptr) (.array n .ptr)

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
  | smax {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | umin {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | umax {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  | usubSat {w : Nat} : BinOp (.bv w) (.bv w) (.bv w)
  /-- `llvm.scmp`: `-1`, `0` or `1` as `a` is less than, equal to or greater than `b`, signed. -/
  | scmp {w w' : Nat} : BinOp (.bv w) (.bv w) (.bv w')
  /-- `llvm.ucmp`: `scmp`, unsigned. -/
  | ucmp {w w' : Nat} : BinOp (.bv w) (.bv w) (.bv w')
  | icmp (p : IntPred) {w : Nat} : BinOp (.bv w) (.bv w) (.bv 1)
  /-- `getelementptr` with one `i64` index: `byteOff + index * stride` bytes on. -/
  | gepDyn (flags : GepFlags) (byteOff stride : Nat) : BinOp .ptr (.bv 64) .ptr
  /-- `getelementptr` to a pointer vector: lane `k` is `gepDyn` of the base's and the index's lane
  `k`, a scalar one splat. -/
  |
  gepVec (flags : GepFlags) (byteOff stride : Nat) {n : Nat} (vecBase vecIdx : Bool) :
    BinOp (Ty.gepBase n vecBase) (Ty.gepIndex n vecIdx) (.array n .ptr)
  /-- `icmp eq` (`ne := false`) or `icmp ne` on pointers. -/
  | ptrcmp (ne : Bool) : BinOp .ptr .ptr (.bv 1)
  |
  vector {l w₁ w₂ w : Nat} (op : BinOp (.bv w₁) (.bv w₂) (.bv w)) :
    BinOp (.vec l w₁) (.vec l w₂) (.vec l w)
  | extractelement {l w wi : Nat} : BinOp (.vec l w) (.bv wi) (.bv w)
  |
  shufflevector {l₁ l₂ w : Nat} (indices : Vector (Option (Fin (2 * l₁))) l₂) :
    BinOp (.vec l₁ w) (.vec l₁ w) (.vec l₂ w)
  |
  insertvalue (indices : List Nat) (tCont tVal : Ty) (h : tCont.memberType indices == some tVal) :
    BinOp tCont tVal tCont -- (c, x)

inductive TernOp : Ty → Ty → Ty → (out : Ty) → Type
  | select {τ : Ty} : TernOp (.bv 1) τ τ τ
  | insertelement {l w wi : Nat} : TernOp (.vec l w) (.bv w) (.bv wi) (.vec l w) -- (v, x, idx)
  | vpermi2var {l w : Nat} : TernOp (.vec l w) (.vec l w) (.vec l w) (.vec l w) -- (a, idx, b)
  /-- `vpmadd52luq`: `a + (b * c)`, the multiplicands' and the product's low 52 bits. -/
  | vpmadd52l {l : Nat} : TernOp (.vec l 64) (.vec l 64) (.vec l 64) (.vec l 64)
  /-- `vpmadd52huq`: `a + (b * c)`'s high part, of the multiplicands' low 52 bits. -/
  | vpmadd52h {l : Nat} : TernOp (.vec l 64) (.vec l 64) (.vec l 64) (.vec l 64)
  /-- `pblendvb`: lane `i` is `b[i]` if `mask[i]`'s top bit is set, else `a[i]`. -/
  | pblendvb {l : Nat} : TernOp (.vec l 8) (.vec l 8) (.vec l 8) (.vec l 8) -- (a, b, mask)
  /-- `subborrow`: `(borrow out, a - b - borrow in)`, the borrow in being `c ≠ 0`. -/
  | subborrow {w : Nat} : TernOp (.bv 8) (.bv w) (.bv w) (.struct [.bv 8, .bv w]) -- (c, a, b)
  | fshl {w : Nat} : TernOp (.bv w) (.bv w) (.bv w) (.bv w)
  | fshr {w : Nat} : TernOp (.bv w) (.bv w) (.bv w) (.bv w)
  |
  vector {l w₁ w₂ w₃ w : Nat} (op : TernOp (.bv w₁) (.bv w₂) (.bv w₃) (.bv w)) :
    TernOp (.vec l w₁) (.vec l w₂) (.vec l w₃) (.vec l w)

inductive Instr (Γ : Ctx)
  | const (v : ⟦τ⟧ᵣ) (dst : Dst Γ τ)
  /-- `llvm.mlir.poison`. -/
  | poison (dst : Dst Γ τ)
  | unop (op : UnOp t₁ t) (dst : Dst Γ t) (a : Reg Γ t₁)
  | binop (op : BinOp t₁ t₂ t) (dst : Dst Γ t) (a : Reg Γ t₁) (b : Reg Γ t₂)
  | ternop (op : TernOp t₁ t₂ t₃ t) (dst : Dst Γ t) (a : Reg Γ t₁) (b : Reg Γ t₂) (c : Reg Γ t₃)
  | load (dst : Dst Γ τ) (p : Reg Γ .ptr)
  | store (p : Reg Γ .ptr) (v : Reg Γ τ)
  /-- `llvm.masked.load`: the lanes `mask` sets loaded, the others `passthru`'s. -/
  |
  maskedLoad {l w : Nat} (dst : Dst Γ (.vec l w)) (p : Reg Γ .ptr) (mask : Reg Γ (.vec l 1))
    (passthru : Reg Γ (.vec l w))
  /-- `llvm.masked.store`: the lanes `mask` sets stored. -/
  | maskedStore {l w : Nat} (v : Reg Γ (.vec l w)) (p : Reg Γ .ptr) (mask : Reg Γ (.vec l 1))
  | memset (dst : Reg Γ .ptr) (val : Reg Γ (.bv 8)) (len : Reg Γ (.bv w))
  | memcpy (dst : Reg Γ .ptr) (src : Reg Γ .ptr) (count : Reg Γ (.bv w))
  /-- `memcpy` whose ranges may overlap: `src` read, then `dst` written. -/
  | memmove (dst : Reg Γ .ptr) (src : Reg Γ .ptr) (count : Reg Γ (.bv w))
  /-- `ptrtoaddr`/`ptrtoint`: `p`'s address, of the state's unspecified block addresses. -/
  | ptrtoaddr (dst : Dst Γ (.bv w)) (p : Reg Γ .ptr)
  /-- `icmp` on pointers by an ordering: their addresses (`ptrtoaddr`) compared. -/
  | ptricmp (pred : IntPred) (dst : Dst Γ (.bv 1)) (a b : Reg Γ .ptr)
  /-- A fresh block of `bytes` undefined bytes; `dst` points to its start. `dead` until a
  `lifetimeStart`: an `alloca` with lifetime markers. -/
  | alloca (dst : Dst Γ .ptr) (bytes : Nat) (dead : Bool := false)
  /-- `llvm.intr.lifetime.start`: `p`'s object becomes live, its bytes undefined; `bytes` is
  ignored. -/
  | lifetimeStart (p : Reg Γ .ptr) (bytes : Nat)
  /-- `llvm.intr.lifetime.end`: `p`'s object becomes dead; `bytes` is ignored. -/
  | lifetimeEnd (p : Reg Γ .ptr) (bytes : Nat)
  /-- `llvm.intr.assume`: UB unless `c` is `1`. -/
  | assume (c : Reg Γ (.bv 1))
  /-- The semantics of the calle `f` should generally be `Func.call` -/
  | call {ts us : List Ty} (f : Vals ts → EffectM (Vals us)) (args : Regs Γ ts) (rets : Dsts Γ us)
  /-- `llvm.mlir.addressof @sym`: the address of the global `sym`'s block, UB if there is none. -/
  | addressof (sym : String) (dst : Dst Γ .ptr)

/-- A jump to block `target`, with one argument per parameter of the target (`blockTys target`). -/
structure Jump (Γ : Ctx) (blockTys : Fin n → List Ty) where
  target : Fin n
  args : Regs Γ (blockTys target)

inductive Exit (Γ : Ctx) (tRets : List Ty) (blockTys : Fin n → List Ty)
  | ret (vs : Regs Γ tRets)
  /-- `llvm.unreachable`: UB. -/
  | unreachable
  | br (target : Jump Γ blockTys)
  | condBr (cond : Reg Γ (.bv 1)) (ttrue : Jump Γ blockTys) (tfalse : Jump Γ blockTys)
  |
  switch (val : Reg Γ t) (defaultTarget : Jump Γ blockTys)
    (branches : List (⟦t⟧ᵣ × Jump Γ blockTys))

end

end MLIR
