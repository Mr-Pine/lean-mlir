module

public import MLIR.Instruction
public import MLIR.Semantics.Effectful.EffectM
public import MLIR.Semantics.Effectful.Memory.Operations
public import MLIR.Semantics.Env
public import MLIR.Semantics.Regs
public import MLIR.Semantics.Operations.Scalar
public import MLIR.Semantics.Operations.Memory
public import MLIR.SimpSets

namespace MLIR

@[expose] public section

@[mlir_instr]
def UnOp.compute : UnOp t₁ t → ⟦t₁⟧ → ⟦t⟧
  | gepConst byteOff => Operation.gep (.value byteOff)
  | trunc flags => Operation.trunc flags
  | zext nneg => Operation.zext nneg

@[mlir_instr]
def BinOp.compute : BinOp t₁ t₂ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t⟧
  | and => Operation.and
  | add flags => Operation.add flags
  | sub flags => Operation.sub flags
  | mul flags => Operation.mul flags
  | shl flags => Operation.shl flags
  | lshr exact => Operation.lshr exact
  | smin => Operation.smin
  | icmp p => Operation.icmp p

@[mlir_instr]
def TernOp.compute : TernOp t₁ t₂ t₃ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t₃⟧ → ⟦t⟧
  | select => Operation.select

/-- Write `vs` into `ds`, first to last. -/
def Env.writeMany (env : ⟪Γ⟫) : Dsts Γ ts → Vals ts → ⟪Γ⟫
  | .nil, .nil => env
  | .cons d ds, .cons v vs => (env.write d v).writeMany ds vs

@[mlir_instr]
def Instr.run (env : ⟪Γ⟫) : Instr Γ → EffectM ⟪Γ⟫
  | const v dst => pure (env.write dst (.value v))
  | unop op dst a => pure (env.write dst (op.compute (env.read a)))
  | binop op dst a b => pure (env.write dst (op.compute (env.read a) (env.read b)))
  | ternop op dst a b c => pure (env.write dst (op.compute (env.read a) (env.read b) (env.read c)))
  | load dst p => Operation.load dst (env.read p) env
  | store p reg => Operation.store (env.read p) (env.read reg) env
  | alloca dst bytes =>
    modifyGetThe GlobalState fun s => (env.write dst (.value s.allocaPtr), s.alloca bytes)
  | call f args rets => do
    let vs ← f (args.read env)
    pure (env.writeMany rets vs)
  -- more defined than LLVM, where a dead object's bytes are undefined: sound for programs
  -- that only touch live objects
  | lifetimeStart _ _ | lifetimeEnd _ _ => pure env

/-- Jump to `jump.target`: read all arguments in `env` first, then write them into the target's
parameters `params jump.target`, so `br ^bb1(%b, %a)` swaps. -/
def Jump.run {blockTys : Fin n → List Ty} (params : (k : Fin n) → Dsts Γ (blockTys k)) (env : ⟪Γ⟫)
    (jump : Jump Γ blockTys) : ⟪Γ⟫ × (Vals tRets ⊕ Fin n) :=
  (env.writeMany (params jump.target) (jump.args.read env), .inr jump.target)

/-- The target of the first case whose value is `x`, else `default`. -/
def switchTarget {bt : Fin n → List Ty} (x : ⟦t⟧ᵣ) (default : Jump Γ bt) :
    List (⟦t⟧ᵣ × Jump Γ bt) → Jump Γ bt
  | [] => default
  | (v, j) :: cases => if x = v then j else switchTarget x default cases

@[mlir_instr]
def Exit.run {blockTys : Fin n → List Ty} (params : (k : Fin n) → Dsts Γ (blockTys k)) (env : ⟪Γ⟫) :
    Exit Γ tRets blockTys → EffectM (⟪Γ⟫ × (Vals tRets ⊕ Fin n))
  | ret regs => pure (env, .inl (regs.read env))
  | br target => pure (target.run params env)
  | condBr cond ttrue tfalse => do
    let .value cond := env.read cond | throwUB
    return if cond == 1#1 then ttrue.run params env else tfalse.run params env
  | switch cond default branches => do
    let .value cond := env.read cond | throwUB
    return (switchTarget (cond) default branches).run params env

end

end MLIR
