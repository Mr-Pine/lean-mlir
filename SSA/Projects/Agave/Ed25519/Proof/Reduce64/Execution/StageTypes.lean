import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Program
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Output
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.ScalarSafety

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

attribute [local implicit_reducible] Ty.width
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Apply one word-level expression independently to the four loaded columns. -/
def laneWord (z : Columns4) (f : Word.Columns → BitVec 64) : V4 :=
  Vector.ofFn fun lane => f (fun j => (z j)[lane])

theorem add_left_comm64 (a b c : BitVec 64) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

/-- Only constants used after the 54-instruction setup prefix are retained. -/
def KernelConstants (E : Env program.Γ) : Prop :=
  E ⊨ [%0 := .value 32#64,
    %1 := Ty.wrap (Vector.replicate 4 26#64),
    %2 := Ty.wrap (Vector.replicate 4 67108863#64),
    %3 := .value 128#64,
    %4 := .value 160#64,
    %5 := .value 64#64,
    %6 := Ty.wrap (Vector.replicate 4 25#64),
    %7 := Ty.wrap (Vector.replicate 4 33554431#64),
    %8 := .value 192#64,
    %9 := .value 96#64,
    %10 := .value 224#64,
    %11 := .value 256#64,
    %12 := .value 288#64,
    %13 := Ty.wrap (Vector.replicate 4 51#64),
    %14 := Ty.wrap (Vector.replicate 4 19#64),
    %33 := halfMask 67108863#32,
    %51 := halfMask 33554431#32]

def CarryA (E : Env program.Γ) (z : Columns4) : Prop :=
  E ⊨ [%56 := Ty.wrap (laneWord z Word.t1),
    %57 := Ty.wrap (laneWord z (fun w => w 0 &&& 67108863#64)),
    %63 := Ty.wrap (laneWord z Word.t5),
    %64 := Ty.wrap (laneWord z (fun w => w 4 &&& 67108863#64))]

def CarryB (E : Env program.Γ) (z : Columns4) : Prop :=
  E ⊨ [%57 := Ty.wrap (laneWord z (fun w => w 0 &&& 67108863#64)),
    %64 := Ty.wrap (laneWord z (fun w => w 4 &&& 67108863#64)),
    %68 := Ty.wrap (laneWord z Word.t2),
    %69 := Ty.wrap (laneWord z (fun w => Word.t1 w &&& 33554431#64)),
    %73 := Ty.wrap (laneWord z Word.t6),
    %74 := Ty.wrap (laneWord z (fun w => Word.t5 w &&& 33554431#64)),
    %78 := Ty.wrap (laneWord z Word.t3),
    %82 := Ty.wrap (laneWord z Word.t7)]

def ReducedRegisters (E : Env program.Γ) (z : Columns4) : Prop :=
  E ⊨ [%68 := Ty.wrap (laneWord z Word.t2),
    %73 := Ty.wrap (laneWord z Word.t6),
    %78 := Ty.wrap (laneWord z Word.t3),
    %82 := Ty.wrap (laneWord z Word.t7),
    %84 := Ty.wrap (laneWord z Word.t4),
    %88 := Ty.wrap (laneWord z Word.t8),
    %90 := Ty.wrap (laneWord z Word.u5),
    %94 := Ty.wrap (laneWord z Word.t9),
    %100 := Ty.wrap (laneWord z Word.u0),
    %103 := Ty.wrap (laneWord z Word.u1)]

def PackedRegisters (E : Env program.Γ) (z : Columns4) : Prop :=
  E ⊨ [%107 := Ty.wrap (packedOutput z 0),
    %112 := Ty.wrap (packedOutput z 1),
    %116 := Ty.wrap (packedOutput z 2),
    %121 := Ty.wrap (packedOutput z 3),
    %126 := Ty.wrap (packedOutput z 4)]


end Agave.Ed25519.Reduce64.Execution
