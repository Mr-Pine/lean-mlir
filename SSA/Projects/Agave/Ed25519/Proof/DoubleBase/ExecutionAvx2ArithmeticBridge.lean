import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2DoubleBridge
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2MulContracts
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2DalekAdapterContract
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.AdditionBridge
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionProgram

/-! Compose the five exact point-operation blocks. The multiplier is linked to
its checked body; square execution remains an explicit helper contract. The
local hypotheses concern only registers, live scratch/cache memory, separation,
and preservation of the caller context under the concrete scratch stores. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Tables (F)
open Conformance.BackendExecution (readPoint)
open Verifier Verifier.Execution
set_option maxRecDepth 10000

/-- Ordinary local inputs for all five arithmetic sites. Neither field assumes
block execution or a point-arithmetic result. -/
structure ArithmeticInputs (ctx : LocalContext) (a b : Nat) (da db : Pointer)
    (table : TableIndex → Extended F) : Prop where
  additions : AdditionInputs ctx a b da db table
  doubling : ∀ E s pos, LadderReady ctx a b da db E s pos →
    ∃ u v r, DoubleInputs ctx E s da db u v r

/-- All five execution obligations follow from the checked point blocks and
actual multiplier. Square is the only functional arithmetic premise. -/
theorem arithmeticBlocks_of_local_inputs (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (hmulLink : p.call2 = Avx2FieldMul.program.call)
    (hsquare : SquareContract p.call1) (hs : ContextStable ctx)
    (hinputs : ArithmeticInputs ctx a b da db table) :
    ArithmeticBlocks p g ctx a b da db table := by
  have hmul : MulContract p.call2 := by
    rw [hmulLink]
    exact imported_mul_contract
  exact arithmeticBlocks_of_imported_double hsquare hmul hs
    (additionBlocks_of_imported_mul p g hmulLink hs hinputs.additions) hinputs.doubling

/-- The ordinary local inputs specialized to the actual invocation's framed
context. `CallerFrame` is preserved along with the scratch/cache invariants. -/
def FramedArithmeticInputs (i : Conformance.BackendExecution.Invocation) (initial : GlobalState) : Prop :=
  ArithmeticInputs (DalekContext i initial)
    (initial.mem.readAt i.scalarA 256).toNat (initial.mem.readAt i.scalarB 256).toNat
    (avx2StackPtr initial 29) (avx2StackPtr initial 28)
    (finiteTable (Tables.avx2DoubleBaseTable (readPoint initial i.pointA)))

theorem framedArithmeticBlocks_of_local_inputs
    (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (hmulLink : p.call2 = Avx2FieldMul.program.call)
    (hsquare : SquareContract p.call1) (i : Conformance.BackendExecution.Invocation) (initial : GlobalState)
    (hinputs : FramedArithmeticInputs i initial) :
    ArithmeticBlocks p g (DalekContext i initial)
      (initial.mem.readAt i.scalarA 256).toNat (initial.mem.readAt i.scalarB 256).toNat
      (avx2StackPtr initial 29) (avx2StackPtr initial 28)
      (finiteTable (Tables.avx2DoubleBaseTable (readPoint initial i.pointA))) :=
  arithmeticBlocks_of_local_inputs p g hmulLink hsquare (dalekContext_stable i initial) hinputs

/-- Exact Dalek output and caller frame with all five point-block execution
premises discharged. The remaining semantic helper premises are the dynamic
table constructor and the actual imported square/negative-square body. Local
register/cache/frame inputs remain explicit ordinary readiness obligations. -/
theorem doubleBaseContractUnder_of_imported_arithmetic
    (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (hmulLink : p.call2 = Avx2FieldMul.program.call)
    (hsquareLink : p.call1 = Avx2SquareNegateD.Execution.program.call)
    (hsquare : SquareContract Avx2SquareNegateD.Execution.program.call)
    (cofactor : ValidPoint → ValidPoint)
    (ready : Pointer → Pointer → Pointer → Pointer → GlobalState → Prop)
    (htable : TableContract p.call0)
    (hinputs : ∀ (i : Conformance.BackendExecution.Invocation) (initial : GlobalState),
      ready i.output i.scalarA i.pointA i.scalarB initial → Input i initial →
      FramedArithmeticInputs i initial) :
    Dalek.DoubleBaseContractUnder ready (avx2Kernel p g).call
      (ValidPoint.layout cofactor) ValidPoint.doubleBase := by
  have hsquare' : SquareContract p.call1 := by
    rw [hsquareLink]
    exact hsquare
  apply doubleBaseContractUnder_of_blocks p g cofactor ready htable
  intro i initial hr hi
  exact framedArithmeticBlocks_of_local_inputs p g hmulLink hsquare' i initial
    (hinputs i initial hr hi)

end Agave.Ed25519.DoubleBase.ExecutionAvx2
