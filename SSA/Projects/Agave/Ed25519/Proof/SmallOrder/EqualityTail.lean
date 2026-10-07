import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.Linked
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekBlackBoxPrimitive

/-! Execution of the original AND/black-box/return suffix. Its entry premises
are the two byte comparisons' Choice results. Allocation, four field products,
four inline serializers, and both byte comparisons precede this suffix. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR Verifier.Execution
open PointConstantTimeEq
open Dalek (choiceByte ReadOnlyFrame)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

/-- Instruction 821 is the exact `%669 = llvm.and(%668, %361)` in the
unchanged one-block equality body. No instructions are reconstructed here. -/
abbrev equalityTail (p : Primitives) : Func :=
  { program p with blocks := fun _ =>
      { program.entry p with body := (program.entry p).body.drop 821 } }

theorem equalityTail_body (p : Primitives) :
    ((equalityTail p).blocks 0).body = (program.entry p).body.drop 821 := rfl

/-- Kernel-checked shape of the source slice. Proving this once keeps the
execution simplifier from unfolding all 821 preceding instructions. -/
theorem equalityTail_body_exact (p : Primitives) :
    (program.entry p).body.drop 821 =
      [.binop .and (%669) (%668) (%361),
       .call p.blackBoxByte (.cons (%669) .nil) (.cons (%670) .nil),
       .lifetimeEnd (%51) 40, .lifetimeEnd (%52) 40,
       .lifetimeEnd (%53) 40, .lifetimeEnd (%54) 40] := rfl

theorem equalityTail_exit (p : Primitives) :
    ((equalityTail p).blocks 0).exit = .ret (.cons (%670) .nil) := rfl

/-- The exact tail returns the conjunction byte and keeps the black-box call's
true state transition. This theorem assumes only that single lower call. -/
theorem equalityTail_run (p : Primitives) (E : Env program.Γ)
    (s t : GlobalState) (x y : Bool)
    (hx : E.read (%361) = .value (choiceByte x))
    (hy : E.read (%668) = .value (choiceByte y))
    (hb : p.blackBoxByte (.cons (.value (choiceByte (x && y))) .nil) s =
      .value (.cons (.value (choiceByte (x && y))) .nil, t)) :
    (equalityTail p).runFrom E 0 s =
      .value (.cons (.value (choiceByte (x && y))) .nil, t) := by
  let E' := E[%669 := .value (choiceByte (x && y)),
    %670 := .value (choiceByte (x && y))]
  have hblock : ((equalityTail p).blocks 0).run program.blockParams E s =
      .value ((E', .inl (.cons (.value (choiceByte (x && y))) .nil)), t) := by
    simp [BasicBlock.run, equalityTail_body_exact, equalityTail_exit, E',
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, Operation.and,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
      mlir_env, Exit.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil, hx, hy, choice_conjunction, hb]
  rw [Func.runFrom_eq, hblock]
  rfl

/-- Install the already proved exact volatile black-box body in this suffix;
no abstract arithmetic or memory operation remains in the suffix contract. -/
theorem linked_equalityTail_run (E : Env program.Γ) (s : GlobalState) (x y : Bool)
    (hwf : s.WF)
    (hx : E.read (%361) = .value (choiceByte x))
    (hy : E.read (%668) = .value (choiceByte y)) :
    ∃ t, (equalityTail equalityPrimitives).runFrom E 0 s =
      .value (.cons (.value (choiceByte (x && y))) .nil, t) ∧
      ReadOnlyFrame s t := by
  obtain ⟨t, hb, hf⟩ := Dalek.BytePrimitives.blackBox_contract (choiceByte (x && y)) s hwf
  exact ⟨t, equalityTail_run equalityPrimitives E s t x y hx hy hb, hf⟩

end Agave.Ed25519.SmallOrder.Execution
