import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Program
import SSA.Projects.RIR.Run.Tactic

/-! Instruction-index cut points retain the original block, exit, and recursive
CFG continuation. They do not replace any instruction by a specification. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR

namespace Cutpoint

/-- Resume the actual body suffix and then execute the original terminator. -/
noncomputable def resume (f : Func) (block : Fin f.n) (pc : Nat)
    (E : ⟪f.Γ⟫) : EffectM (Vals f.tRets) := do
  let E' ← (f.blocks block).runBodyFrom E pc
  let (E'', exit) ← (f.blocks block).exit.run f.blockParams E'
  Func.continue (func := f) E'' exit

theorem zero (f : Func) (block : Fin f.n) (E : ⟪f.Γ⟫) (s : GlobalState) :
    resume f block 0 E s = f.runFrom E block s := by
  rw [Func.runFrom_eq, BasicBlock.run_eq]
  simp only [resume, EffectM.bind_eq, bind_assoc]

/-- A proved instruction execution advances exactly one original instruction. -/
theorem step (f : Func) (block : Fin f.n) (pc : Nat)
    (E E' : ⟪f.Γ⟫) (s s' : GlobalState)
    (hpc : pc < (f.blocks block).body.length)
    (hstep : Instr.run E ((f.blocks block).body[pc]'hpc) s = .value (E', s')) :
    resume f block pc E s = resume f block (pc + 1) E' s' := by
  simp only [resume, EffectM.bind_eq,
    BasicBlock.runBodyFrom_step_of_run hpc hstep]

/-- A body-suffix equation composes with its original terminator without a
premise about any later branch or final decoder result. -/
theorem of_body (f : Func) (block : Fin f.n) (pc : Nat)
    (E E' : ⟪f.Γ⟫) (s s' : GlobalState)
    (hbody : (f.blocks block).runBodyFrom E pc s = .value (E', s')) :
    resume f block pc E s = (do
      let ((E'', exit), t) ← (f.blocks block).exit.run f.blockParams E' s'
      Func.continue (func := f) E'' exit t) := by
  simp only [resume, EffectM.bind_eq, hbody, PoisonOr.value_bind]

/-- Execute a finite original instruction slice, retaining its exact environment. -/
def segment (f : Func) (block : Fin f.n) (first count : Nat) (E : ⟪f.Γ⟫) :
    EffectM ⟪f.Γ⟫ :=
  List.foldlM Instr.run E (((f.blocks block).body.drop first).take count)

/-- A checked finite slice joins directly to the remaining original body. -/
theorem after_segment (f : Func) (block : Fin f.n) (first count : Nat)
    (E E' : ⟪f.Γ⟫) (s s' : GlobalState)
    (hsegment : segment f block first count E s = .value (E', s')) :
    resume f block first E s = resume f block (first + count) E' s' := by
  have hbody : (f.blocks block).runBodyFrom E first = (do
      let middle ← segment f block first count E
      (f.blocks block).runBodyFrom middle (first + count)) := by
    unfold BasicBlock.runBodyFrom segment
    conv =>
      lhs
      rw [← List.take_append_drop count ((f.blocks block).body.drop first)]
    rw [List.foldlM_append, List.drop_drop]
  simp only [resume, hbody, EffectM.bind_eq, bind_assoc, hsegment, PoisonOr.value_bind]

end Cutpoint

namespace Decode

noncomputable def resume (p : Primitives) (g : Globals) (block : Fin 3) (pc : Nat)
    (E : ⟪program.Γ⟫) : EffectM (Vals []) :=
  Cutpoint.resume (program p g) block pc E

/-- There is one failure/success decision in the outer decompressor. Its
predicate is the sqrt helper's byte result, rather than canonical-Y validity. -/
theorem decide_path (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (flag : BitVec 8)
    (hflag : E.read (%93) = .value flag)
    (hzero : E.read (%20) = .value 0#8)
    (htag : E.read (%14) = .value 0#64) :
    resume p g 0 137 E s =
      if flag = 0#8 then
        (program p g).runFrom (E[%96 := .value (BitVec.ofBool (flag == 0#8)),
          %141 := .value 0#64]) 2 s
      else
        (program p g).runFrom
          (E[%96 := .value (BitVec.ofBool (flag == 0#8))]) 1 s := by
  unfold resume Cutpoint.resume
  have hb : (program p g).blocks 0 = program.bb0 p g := rfl
  by_cases h : flag = 0#8 <;>
    simp [hb, BasicBlock.runBodyFrom, program.bb0, program.blockParams,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, Operation.icmp,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
      Exit.run, Jump.run, Regs.read_nil, Regs.read_cons,
      Env.writeMany_nil, Env.writeMany_cons, Func.continue, hflag, hzero, htag,
      h, ofBool_eq_one_iff] <;> rfl

end Decode
end Agave.Ed25519.Encoding.Decompress.Execution
