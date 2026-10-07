import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ExecutionProgram
import SSA.Projects.RIR.Run.BasicBlock

/-! Execute the actual constant/global-address and stack-allocation prefixes.
These phases precede every input read and retain the exact allocation sizes.
They are concrete RIR execution equations, not arithmetic specifications. -/

set_option maxRecDepth 100000

namespace Agave.Ed25519.Verifier.Execution

open LeanMLIR.RIR

namespace ScalarWide

def startupState (state : GlobalState) : GlobalState :=
  let s1 := state.alloca 8
  let s2 := s1.alloca 8
  let s3 := s2.alloca 8
  let s4 := s3.alloca 8
  let s5 := s4.alloca 8
  let s6 := s5.alloca 40
  let s7 := s6.alloca 40
  let s8 := s7.alloca 40
  let s9 := s8.alloca 40
  let s10 := s9.alloca 40
  let s11 := s10.alloca 40
  let s12 := s11.alloca 8
  let s13 := s12.alloca 8
  let s14 := s13.alloca 8
  let s15 := s14.alloca 8
  let s16 := s15.alloca 8
  let s17 := s16.alloca 8
  let s18 := s17.alloca 8
  let s19 := s18.alloca 8
  let s20 := s19.alloca 8
  let s21 := s20.alloca 8
  let s22 := s21.alloca 8
  let s23 := s22.alloca 8
  let s24 := s23.alloca 8
  s24

def startupEnv (E : Env program.Γ) (g : Globals) (state : GlobalState) : Env program.Γ :=
  let s0 := state
  let s1 := s0.alloca 8
  let s2 := s1.alloca 8
  let s3 := s2.alloca 8
  let s4 := s3.alloca 8
  let s5 := s4.alloca 8
  let s6 := s5.alloca 40
  let s7 := s6.alloca 40
  let s8 := s7.alloca 40
  let s9 := s8.alloca 40
  let s10 := s9.alloca 40
  let s11 := s10.alloca 40
  let s12 := s11.alloca 8
  let s13 := s12.alloca 8
  let s14 := s13.alloca 8
  let s15 := s14.alloca 8
  let s16 := s15.alloca 8
  let s17 := s16.alloca 8
  let s18 := s17.alloca 8
  let s19 := s18.alloca 8
  let s20 := s19.alloca 8
  let s21 := s20.alloca 8
  let s22 := s21.alloca 8
  let s23 := s22.alloca 8
  E[%0 := .value (BitVec.ofInt 32 (1)),
    %1 := .value (BitVec.ofInt 64 (4)),
    %2 := .value (BitVec.ofInt 64 (32)),
    %3 := .value (BitVec.ofInt 64 (5)),
    %4 := .value (BitVec.ofInt 64 (40)),
    %5 := .value (BitVec.ofInt 64 (6)),
    %6 := .value (BitVec.ofInt 64 (48)),
    %7 := .value (BitVec.ofInt 64 (7)),
    %8 := .value (BitVec.ofInt 64 (56)),
    %9 := .value (BitVec.ofInt 64 (8)),
    %10 := .value (BitVec.ofInt 64 (12)),
    %11 := .value (BitVec.ofInt 64 (13)),
    %12 := .value (BitVec.ofInt 64 (14)),
    %13 := .value (BitVec.ofInt 64 (16)),
    %14 := .value (BitVec.ofInt 64 (18)),
    %15 := .value (BitVec.ofInt 64 (19)),
    %16 := .value (BitVec.ofInt 64 (24)),
    %17 := .value (BitVec.ofInt 64 (20)),
    %18 := .value (BitVec.ofInt 64 (22)),
    %19 := .value (BitVec.ofInt 64 (25)),
    %20 := .value (BitVec.ofInt 64 (26)),
    %21 := .value (BitVec.ofInt 64 (28)),
    %22 := .value (BitVec.ofInt 64 (30)),
    %23 := .value (BitVec.ofInt 64 (33)),
    %24 := .value (BitVec.ofInt 64 (34)),
    %25 := .value (BitVec.ofInt 64 (36)),
    %26 := .value (BitVec.ofInt 64 (38)),
    %27 := .value (BitVec.ofInt 64 (44)),
    %28 := .value (BitVec.ofInt 64 (45)),
    %29 := .value (BitVec.ofInt 64 (46)),
    %30 := .value (BitVec.ofInt 64 (50)),
    %31 := .value (BitVec.ofInt 64 (51)),
    %32 := .value (BitVec.ofInt 64 (52)),
    %33 := .value (BitVec.ofInt 64 (54)),
    %34 := .value (BitVec.ofInt 64 (58)),
    %35 := .value (BitVec.ofInt 64 (59)),
    %36 := .value (BitVec.ofInt 64 (60)),
    %37 := .value (BitVec.ofInt 64 (62)),
    %38 := .value (BitVec.ofInt 64 (4503599627370495)),
    %39 := .value g.address0,
    %40 := .value g.address1,
    %41 := .value (BitVec.ofInt 64 (-671914833335277)),
    %42 := .value (BitVec.ofInt 64 (63)),
    %43 := .value (BitVec.ofInt 64 (-3916664325105025)),
    %44 := .value (BitVec.ofInt 64 (-1367801)),
    %45 := .value (BitVec.ofInt 64 (-17592186044416)),
    %46 := .value (BitVec.ofInt 64 (0)),
    %47 := .value (BitVec.ofInt 64 (671914833335277)),
    %48 := .value (BitVec.ofInt 64 (3916664325105025)),
    %49 := .value (BitVec.ofInt 64 (1367801)),
    %50 := .value (BitVec.ofInt 64 (17592186044416)),
    %51 := .value (BitVec.ofInt 8 (0)),
    %52 := .value (BitVec.ofInt 64 (1)),
    %53 := .value (BitVec.ofInt 64 (2)),
    %54 := .value (BitVec.ofInt 64 (3)),
    %55 := .value (BitVec.ofInt 64 (9)),
    %56 := .value (BitVec.ofInt 64 (10)),
    %57 := .value (BitVec.ofInt 64 (11)),
    %58 := .value (BitVec.ofInt 64 (15)),
    %59 := .value (BitVec.ofInt 64 (17)),
    %60 := .value (BitVec.ofInt 64 (21)),
    %61 := .value (BitVec.ofInt 64 (23)),
    %62 := .value (BitVec.ofInt 64 (27)),
    %63 := .value (BitVec.ofInt 64 (29)),
    %64 := .value (BitVec.ofInt 64 (31)),
    %65 := .value s0.allocaPtr,
    %66 := .value s1.allocaPtr,
    %67 := .value s2.allocaPtr,
    %68 := .value s3.allocaPtr,
    %69 := .value s4.allocaPtr,
    %70 := .value s5.allocaPtr,
    %71 := .value s6.allocaPtr,
    %72 := .value s7.allocaPtr,
    %73 := .value s8.allocaPtr,
    %74 := .value s9.allocaPtr,
    %75 := .value s10.allocaPtr,
    %76 := .value s11.allocaPtr,
    %77 := .value s12.allocaPtr,
    %78 := .value s13.allocaPtr,
    %79 := .value s14.allocaPtr,
    %80 := .value s15.allocaPtr,
    %81 := .value s16.allocaPtr,
    %82 := .value s17.allocaPtr,
    %83 := .value s18.allocaPtr,
    %84 := .value s19.allocaPtr,
    %85 := .value s20.allocaPtr,
    %86 := .value s21.allocaPtr,
    %87 := .value s22.allocaPtr,
    %88 := .value s23.allocaPtr]

/-- The first 89 actual instructions install constants, global pointers, and
allocate 24 exact private stack objects. No callee premise is used. -/
theorem startup_run (p : Primitives) (g : Globals) (E : Env program.Γ) (state : GlobalState) :
    List.foldlM Instr.run E ((program.entry p g).body.take 89) state =
      .value (startupEnv E g state, startupState state) := by
  rfl

theorem startup_allocation_count (state : GlobalState) :
    (startupState state).alloc.nextFreeBlock = state.alloc.nextFreeBlock + 24 := by
  simp [startupState, GlobalState.alloca, Nat.add_assoc]

end ScalarWide

namespace ScalarMontgomeryMul

def startupState (state : GlobalState) : GlobalState :=
  let s1 := state.alloca 16
  let s2 := s1.alloca 16
  let s3 := s2.alloca 16
  let s4 := s3.alloca 16
  let s5 := s4.alloca 16
  let s6 := s5.alloca 16
  let s7 := s6.alloca 16
  let s8 := s7.alloca 16
  let s9 := s8.alloca 16
  s9

def startupEnv (E : Env program.Γ) (state : GlobalState) : Env program.Γ :=
  let s0 := state
  let s1 := s0.alloca 16
  let s2 := s1.alloca 16
  let s3 := s2.alloca 16
  let s4 := s3.alloca 16
  let s5 := s4.alloca 16
  let s6 := s5.alloca 16
  let s7 := s6.alloca 16
  let s8 := s7.alloca 16
  E[%0 := .value (BitVec.ofInt 32 (1)),
    %1 := .value (BitVec.ofInt 64 (8)),
    %2 := .value (BitVec.ofInt 64 (16)),
    %3 := .value (BitVec.ofInt 64 (24)),
    %4 := .value (BitVec.ofInt 64 (32)),
    %5 := .value (BitVec.ofInt 64 (1439961107955227)),
    %6 := .value (BitVec.ofInt 64 (4503599627370495)),
    %7 := .value (BitVec.ofInt 128 (671914833335277)),
    %8 := .value (BitVec.ofInt 128 (52)),
    %9 := .value (BitVec.ofInt 128 (3916664325105025)),
    %10 := .value (BitVec.ofInt 128 (1367801)),
    %11 := .value (BitVec.ofInt 128 (44)),
    %12 := .value (BitVec.ofInt 64 (-671914833335277)),
    %13 := .value (BitVec.ofInt 64 (63)),
    %14 := .value (BitVec.ofInt 64 (-3916664325105025)),
    %15 := .value (BitVec.ofInt 64 (-1367801)),
    %16 := .value (BitVec.ofInt 64 (-17592186044416)),
    %17 := .value (BitVec.ofInt 64 (0)),
    %18 := .value (BitVec.ofInt 64 (671914833335277)),
    %19 := .value (BitVec.ofInt 64 (3916664325105025)),
    %20 := .value (BitVec.ofInt 64 (52)),
    %21 := .value (BitVec.ofInt 64 (1367801)),
    %22 := .value (BitVec.ofInt 64 (17592186044416)),
    %23 := .value (BitVec.ofInt 128 (0)),
    %24 := .value s0.allocaPtr,
    %25 := .value s1.allocaPtr,
    %26 := .value s2.allocaPtr,
    %27 := .value s3.allocaPtr,
    %28 := .value s4.allocaPtr,
    %29 := .value s5.allocaPtr,
    %30 := .value s6.allocaPtr,
    %31 := .value s7.allocaPtr,
    %32 := .value s8.allocaPtr]

/-- The first 33 actual instructions install constants, global pointers, and
allocate 9 exact private stack objects. No callee premise is used. -/
theorem startup_run (p : Primitives) (E : Env program.Γ) (state : GlobalState) :
    List.foldlM Instr.run E ((program.entry p).body.take 33) state =
      .value (startupEnv E state, startupState state) := by
  rfl

theorem startup_allocation_count (state : GlobalState) :
    (startupState state).alloc.nextFreeBlock = state.alloc.nextFreeBlock + 9 := by
  simp [startupState, GlobalState.alloca, Nat.add_assoc]

end ScalarMontgomeryMul

end Agave.Ed25519.Verifier.Execution
