module

public import SSA.Projects.RIR.Instruction
public import SSA.Projects.RIR.Semantics.Effectful.EffectM
public import SSA.Projects.RIR.Semantics.Effectful.Memory.Operations
public import SSA.Projects.RIR.Semantics.Env
public import SSA.Projects.RIR.Semantics.Vals
public import SSA.Projects.RIR.Semantics.Operations.Scalar
public import SSA.Projects.RIR.Semantics.Operations.Memory
public import SSA.Projects.RIR.SimpSets

namespace LeanMLIR.RIR

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

@[mlir_instr]
def Exit.run (env : ⟪Γ⟫) : Exit Γ tRets blockParams → EffectM (Vals tRets ⊕ Fin n)
  | ret regs => pure (.inl (regs.read env))

end

end LeanMLIR.RIR
