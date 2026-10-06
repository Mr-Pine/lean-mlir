module

public import SSA.Projects.RIR.Instruction
public import SSA.Projects.RIR.Semantics.Effectful.EffectM
public import SSA.Projects.RIR.Semantics.Effectful.Memory.Operations
public import SSA.Projects.RIR.Semantics.Env
public import SSA.Projects.RIR.Semantics.Regs
public import SSA.Projects.RIR.Semantics.Operations.Scalar
public import SSA.Projects.RIR.Semantics.Operations.Memory
public import SSA.Projects.RIR.Semantics.Operations.Vector
public import SSA.Projects.RIR.SimpSets

namespace LeanMLIR.RIR

@[expose] public section

@[mlir_instr]
def UnOp.compute : UnOp t₁ t → ⟦t₁⟧ → ⟦t⟧
  | extractvalue path => path.get
  | gepConst byteOff => Operation.gep (.value byteOff)
  | trunc flags => Operation.trunc flags
  | zext nneg => Operation.zext nneg
  | sext => Operation.sext
  | vector op => fun a => Vector.ofFn (fun i => op.compute a[i])
  | bswap => Operation.bswap
  | bitcast h => Operation.bitcast h

@[mlir_instr]
def BinOp.compute : BinOp t₁ t₂ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t⟧
  | insertvalue path => path.set
  | and => Operation.and
  | or disjoint => Operation.or disjoint
  | xor => Operation.xor
  | add flags => Operation.add flags
  | sub flags => Operation.sub flags
  | mul flags => Operation.mul flags
  | shl flags => Operation.shl flags
  | lshr exact => Operation.lshr exact
  | ashr exact => Operation.ashr exact
  | smin => Operation.smin
  | icmp p => Operation.icmp p
  | vector op => Vector.zipWith op.compute
  | extractelement => Operation.extractelement
  | shufflevector perm => Operation.shufflevector perm

@[mlir_instr]
def TernOp.compute : TernOp t₁ t₂ t₃ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t₃⟧ → ⟦t⟧
  | select => Operation.select
  | insertelement => Operation.insertelement
  | vpermi2var => Operation.vpermi2var
  | vpmadd52l => Operation.vpmadd52l
  | vpmadd52h => Operation.vpmadd52h
  | fshl => Operation.fshl
  | fshr => Operation.fshr
  | vector op => fun a b c => Vector.ofFn (fun i => op.compute a[i] b[i] c[i])

/-- Write `vs` into `ds`, first to last. -/
def Env.writeMany (env : ⟪Γ⟫) : Dsts Γ ts → Vals ts → ⟪Γ⟫
  | .nil, .nil => env
  | .cons d ds, .cons v vs => (env.write d v).writeMany ds vs

def GepIndex.offset (env : ⟪Γ⟫) : GepIndex Γ → PoisonOr (BitVec 64)
  | .constant off => .value (BitVec.ofInt 64 off)
  | .scaled stride index => Operation.gepIndex stride (env.read index)

@[mlir_instr]
def Instr.run (env : ⟪Γ⟫) : Instr Γ → EffectM ⟪Γ⟫
  | gep dst base indices =>
    pure (env.write dst (Operation.gepUnflagged (env.read base) (indices.map (·.offset env))))
  | const v dst => pure (env.write dst (Ty.wrap v))
  | poison dst => pure (env.write dst (Ty.poisoned _))
  | unop op dst a => pure (env.write dst (op.compute (env.read a)))
  | binop op dst a b => pure (env.write dst (op.compute (env.read a) (env.read b)))
  | ternop op dst a b c => pure (env.write dst (op.compute (env.read a) (env.read b) (env.read c)))
  | load dst p => Operation.load dst (env.read p) env
  | store p reg => Operation.store (env.read p) (env.read reg) env
  | memset dst v len => Operation.memset (env.read dst) (env.read v) (env.read len) env
  | memcpy dst src len => Operation.memcpy (env.read dst) (env.read src) (env.read len) env
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
    let .value cond := Ty.unwrap (env.read cond) | throwUB
    return (switchTarget (cond) default branches).run params env

end

end LeanMLIR.RIR
