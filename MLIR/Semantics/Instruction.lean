module

public import MLIR.Instruction
public import MLIR.Semantics.Effectful.EffectM
public import MLIR.Semantics.Effectful.Memory.Operations
public import MLIR.Semantics.Env
public import MLIR.Semantics.Vals
public import MLIR.Semantics.Operations.Scalar
public import MLIR.Semantics.Operations.Memory
public import MLIR.SimpSets

namespace MLIR

@[expose] public section

@[mlir_instr]
def UnOp.compute : UnOp t₁ t → ⟦t₁⟧ → ⟦t⟧
  | gepConst byteOff => Operation.gep (.value byteOff)

@[mlir_instr]
def BinOp.compute : BinOp t₁ t₂ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t⟧
  | and => Operation.and
  | add flags => Operation.add flags
  | sub flags => Operation.sub flags
  | mul flags => Operation.mul flags
  | lshr exact => Operation.lshr exact
  | smin => Operation.smin
  | icmp p => Operation.icmp p

@[mlir_instr]
def TernOp.compute : TernOp t₁ t₂ t₃ t → ⟦t₁⟧ → ⟦t₂⟧ → ⟦t₃⟧ → ⟦t⟧
  | select => Operation.select

@[mlir_instr]
def Instr.run (env : ⟪Γ⟫) : Instr Γ → EffectM ⟪Γ⟫
  | const v dst => pure (env.write dst (.value v))
  | unop op dst a => pure (env.write dst (op.compute (env.read a)))
  | binop op dst a b => pure (env.write dst (op.compute (env.read a) (env.read b)))
  | ternop op dst a b c => pure (env.write dst (op.compute (env.read a) (env.read b) (env.read c)))
  | load dst p => Operation.load dst (env.read p) env
  | store p reg => Operation.store (env.read p) (env.read reg) env

def Env.setMany (env : ⟪Γ⟫) :
    (targets : List (Fin Γ.vals.length)) → Vals ts → Γ.types targets = ts → ⟪Γ⟫
  | (t :: ts), (Vals.cons v vs), hts =>
    env.write ⟨t, (List.cons.inj hts).left⟩ v |>.setMany ts vs (List.cons.inj hts).right
  | [], _, _ => env

def Jump.run (env : ⟪Γ⟫) (jump : Jump (n := n) Γ blockParams) : ⟪Γ⟫ × (Vals tRets ⊕ Fin n) :=
  (env.setMany (blockParams jump.target) (jump.args.read env) rfl, .inr jump.target)

/-- The target of the first case whose value is `x`, else `default`. -/
def switchTarget {bp : Fin n → List (Fin Γ.vals.length)} (x : ⟦t⟧ᵣ) (default : Jump Γ bp) :
    List (⟦t⟧ᵣ × Jump Γ bp) → Jump Γ bp
  | [] => default
  | (v, j) :: cases => if x = v then j else switchTarget x default cases

@[mlir_instr]
def Exit.run (env : ⟪Γ⟫) : Exit (n := n) Γ tRets blockParams → EffectM (⟪Γ⟫ × (Vals tRets ⊕ Fin n))
  | ret regs => pure (env, .inl (regs.read env))
  | br target => pure (target.run env)
  | condBr cond ttrue tfalse => do
    let .value cond := env.read cond | throwUB
    return if cond == 1#1 then ttrue.run env else tfalse.run env
  | switch cond default branches => do
    let .value cond := env.read cond | throwUB
    return (switchTarget (cond) default branches).run env

end

end MLIR
