module

public import MLIR.Instruction
public import MLIR.Semantics.Effectful.EffectM
public import MLIR.Semantics.Effectful.Memory.Operations
public import MLIR.Semantics.Env
public import MLIR.Semantics.Regs
public import MLIR.Semantics.Operations.Scalar
public import MLIR.Semantics.Operations.Memory
public import MLIR.Semantics.Operations.Vector
public import MLIR.Semantics.Operations.Container
public import MLIR.SimpSets

namespace MLIR

@[expose] public section

@[mlir_instr]
def UnOp.compute : UnOp t₁ t → ⟦t₁⟧ → ⟦t⟧
  | gepConst flags byteOff =>
    if 0 ≤ byteOff then Operation.gep flags (.value byteOff.toNat)
    else Operation.gepBack flags byteOff.natAbs
  | trunc flags => Operation.trunc flags
  | zext nneg => Operation.zext nneg
  | sext => Operation.sext
  | bswap => Operation.bswap
  | copy => id
  | cttz isZeroPoison => Operation.cttz isZeroPoison
  | reduceOr => Operation.reduceOr
  | reduceAnd => Operation.reduceAnd
  | bitcast h => Operation.bitcast h
  | extractvalue indices tCont tVal h => Operation.extractvalue indices tCont tVal h
  | vector op => fun a => Vector.ofFn (fun i => op.compute a[i])

@[mlir_instr]
def BinOp.compute : BinOp t₁ t₂ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t⟧
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
  | smax => Operation.smax
  | umin => Operation.umin
  | umax => Operation.umax
  | scmp => Operation.scmp
  | ucmp => Operation.ucmp
  | icmp p => Operation.icmp p
  | ptrcmp ne => Operation.ptrcmp ne
  | gepDyn flags byteOff stride => Operation.gepDyn flags byteOff stride
  | vector op => Vector.zipWith op.compute
  | extractelement => Operation.extractelement
  | shufflevector perm => Operation.shufflevector perm
  | insertvalue indices tCont tElem h => Operation.insertvalue indices tCont tElem h

@[mlir_instr]
def TernOp.compute : TernOp t₁ t₂ t₃ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t₃⟧ → ⟦t⟧
  | select => Operation.select
  | insertelement => Operation.insertelement
  | vpermi2var => Operation.vpermi2var
  | vpmadd52l => Operation.vpmadd52l
  | vpmadd52h => Operation.vpmadd52h
  | pblendvb => Operation.pblendvb
  | subborrow => Operation.subborrow
  | fshl => Operation.fshl
  | fshr => Operation.fshr
  | vector op => fun a b c => Vector.ofFn (fun i => op.compute a[i] b[i] c[i])

/-- Write `vs` into `ds`, first to last. -/
def Env.writeMany (env : ⟪Γ⟫) : Dsts Γ ts → Vals ts → ⟪Γ⟫
  | .nil, .nil => env
  | .cons d ds, .cons v vs => (env.write d v).writeMany ds vs

@[mlir_instr]
def Instr.run (env : ⟪Γ⟫) : Instr Γ → EffectM ⟪Γ⟫
  | const v dst => pure (env.write dst (Ty.wrap v))
  | poison dst => pure (env.write dst (Ty.poisoned _))
  | unop op dst a => pure (env.write dst (op.compute (env.read a)))
  | binop op dst a b => pure (env.write dst (op.compute (env.read a) (env.read b)))
  | ternop op dst a b c => pure (env.write dst (op.compute (env.read a) (env.read b) (env.read c)))
  | load dst p => Operation.load dst (env.read p) env
  | store p reg => Operation.store (env.read p) (env.read reg) env
  | memset dst v len => Operation.memset (env.read dst) (env.read v) (env.read len) env
  | memcpy dst src len => Operation.memcpy (env.read dst) (env.read src) (env.read len) env
  | memmove dst src len => Operation.memmove (env.read dst) (env.read src) (env.read len) env
  | ptrtoaddr dst p => do
    let s ← get
    pure (env.write dst (Operation.ptrtoaddr s.mem.addr (env.read p)))
  | alloca dst bytes dead =>
    modifyGetThe GlobalState fun s => (env.write dst (.value s.allocaPtr), s.alloca bytes dead)
  | lifetimeStart p _ => Operation.lifetimeStart (env.read p) env
  | lifetimeEnd p _ => Operation.lifetimeEnd (env.read p) env
  | assume c => Operation.assume (env.read c) env
  | call f args rets => do
    let vs ← f (args.read env)
    pure (env.writeMany rets vs)
  | addressof sym dst => do
    let s ← get
    let some (b, _) := s.mem.globals sym | throwUB
    pure (env.write dst (.value ⟨b, 0⟩))

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
  | unreachable => throwUB
  | br target => pure (target.run params env)
  | condBr cond ttrue tfalse => do
    let .value cond := env.read cond | throwUB
    return if cond == 1#1 then ttrue.run params env else tfalse.run params env
  | switch cond default branches => do
    let .value cond := Ty.unwrap (env.read cond) | throwUB
    return (switchTarget (cond) default branches).run params env

end

end MLIR
