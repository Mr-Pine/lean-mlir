import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleTrace
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointMemory
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorValidPoint

namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR SerialPoint SerialPoint.Execution SerialFieldMul
open Reduce64.Execution (SmallRange)

/-- The exact field multiplication state update, without any arithmetic
precondition: the machine theorem is valid for arbitrary 64-bit inputs. -/
def mulState (s : GlobalState) (out a b : Pointer) : GlobalState :=
  {s with mem := storeLimbs s.mem out (machine (readLimbs s a) (readLimbs s b))}

def doubleState (s : GlobalState) (out input : Pointer) : GlobalState :=
  pointPost s out (doubleWordTrace (readPointWords s input)) 5

def copyState (s : GlobalState) (out input : Pointer) (n : Nat) : GlobalState :=
  {s with mem := s.mem.storeAt out (s.mem.readAt input (8*n))}

/-- Entry copies each projective coordinate separately, in Y, Z, X order. -/
def initialState (s : GlobalState) (out input : Pointer) : GlobalState :=
  let s := copyState s (out.add 40#64) (input.add 40#64) 40
  let s := copyState s (out.add 80#64) (input.add 80#64) 40
  copyState s out input 40

/-- One loop iteration materializes XYZ, then copies those exact 120 bytes. -/
def loopState (s : GlobalState) (completed projective temporary : Pointer) : GlobalState :=
  let s := doubleState s completed projective
  let s := mulState s temporary completed (completed.add 120#64)
  let s := mulState s (temporary.add 40#64) (completed.add 40#64) (completed.add 80#64)
  let s := mulState s (temporary.add 80#64) (completed.add 80#64) (completed.add 120#64)
  copyState s projective temporary 120

/-- The final block materializes all four extended coordinates. -/
def finalState (s : GlobalState) (out completed projective : Pointer) : GlobalState :=
  let s := doubleState s completed projective
  let s := mulState s out completed (completed.add 120#64)
  let s := mulState s (out.add 40#64) (completed.add 40#64) (completed.add 80#64)
  let s := mulState s (out.add 80#64) (completed.add 80#64) (completed.add 120#64)
  mulState s (out.add 120#64) completed (completed.add 40#64)

/-- Concrete finite memory schedule of the k=3 call, including its four
private objects, three doubles, ten products, copies, and final frame erase. -/
def cofactorState (s : GlobalState) (out input : Pointer) : GlobalState :=
  let completedFinal := s.allocaPtr
  let s₁ := s.alloca 160
  let temporary := s₁.allocaPtr
  let s₂ := s₁.alloca 120
  let projective := s₂.allocaPtr
  let s₃ := s₂.alloca 120
  let completedLoop := s₃.allocaPtr
  let s₄ := s₃.alloca 160
  let s₇ := initialState s₄ projective input
  let s₈ := loopState s₇ completedLoop projective temporary
  let s₉ := loopState s₈ completedLoop projective temporary
  let s₁₀ := finalState s₉ out completedFinal projective
  {s₁₀ with mem := s₁₀.mem.eraseFrom s.alloc.nextFreeBlock}

theorem cofactorState_alloc (s : GlobalState) (out input : Pointer) :
    (cofactorState s out input).alloc.nextFreeBlock = s.alloc.nextFreeBlock + 19 := by
  simp only [cofactorState, initialState, loopState, finalState, doubleState, mulState, copyState,
    pointPost, GlobalState.alloca_alloc]

end Agave.Ed25519.SmallOrder.Execution
