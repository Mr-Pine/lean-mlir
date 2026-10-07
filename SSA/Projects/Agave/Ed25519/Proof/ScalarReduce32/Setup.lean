import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Phases

/-! Exact execution of the 62 constant instructions and 33 private allocations.
These setup theorems retain the true allocation counter and each fresh pointer. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000

def constantsEnv (E : Env program.Γ) : Env program.Γ :=
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
    %18 := .value (BitVec.ofInt 64 (25)),
    %19 := .value (BitVec.ofInt 64 (26)),
    %20 := .value (BitVec.ofInt 64 (30)),
    %21 := .value (BitVec.ofInt 64 (0)),
    %22 := .value (BitVec.ofInt 64 (36)),
    %23 := .value (BitVec.ofInt 64 (4503599627370495)),
    %24 := .value (BitVec.ofInt 128 (4302102966953709)),
    %25 := .value (BitVec.ofInt 128 (1049714374468698)),
    %26 := .value (BitVec.ofInt 128 (4503599278581019)),
    %27 := .value (BitVec.ofInt 128 (4503599627370495)),
    %28 := .value (BitVec.ofInt 128 (17592186044415)),
    %29 := .value (BitVec.ofInt 64 (1439961107955227)),
    %30 := .value (BitVec.ofInt 128 (671914833335277)),
    %31 := .value (BitVec.ofInt 128 (52)),
    %32 := .value (BitVec.ofInt 128 (3916664325105025)),
    %33 := .value (BitVec.ofInt 128 (1367801)),
    %34 := .value (BitVec.ofInt 128 (44)),
    %35 := .value (BitVec.ofInt 64 (-671914833335277)),
    %36 := .value (BitVec.ofInt 64 (63)),
    %37 := .value (BitVec.ofInt 64 (-3916664325105025)),
    %38 := .value (BitVec.ofInt 64 (-1367801)),
    %39 := .value (BitVec.ofInt 64 (-17592186044416)),
    %40 := .value (BitVec.ofInt 64 (671914833335277)),
    %41 := .value (BitVec.ofInt 64 (3916664325105025)),
    %42 := .value (BitVec.ofInt 64 (52)),
    %43 := .value (BitVec.ofInt 64 (1367801)),
    %44 := .value (BitVec.ofInt 64 (17592186044416)),
    %45 := .value (BitVec.ofInt 64 (28)),
    %46 := .value (BitVec.ofInt 64 (44)),
    %47 := .value (BitVec.ofInt 64 (1)),
    %48 := .value (BitVec.ofInt 64 (2)),
    %49 := .value (BitVec.ofInt 64 (3)),
    %50 := .value (BitVec.ofInt 64 (9)),
    %51 := .value (BitVec.ofInt 64 (10)),
    %52 := .value (BitVec.ofInt 64 (11)),
    %53 := .value (BitVec.ofInt 64 (15)),
    %54 := .value (BitVec.ofInt 64 (17)),
    %55 := .value (BitVec.ofInt 64 (21)),
    %56 := .value (BitVec.ofInt 64 (22)),
    %57 := .value (BitVec.ofInt 64 (23)),
    %58 := .value (BitVec.ofInt 64 (27)),
    %59 := .value (BitVec.ofInt 64 (29)),
    %60 := .value (BitVec.ofInt 64 (31)),
    %61 := .value (BitVec.ofInt 128 (0))]

theorem constants_execute (E : Env program.Γ) (s : GlobalState) :
    List.foldlM Instr.run E constants s = .value (constantsEnv E, s) := by rfl

/-- Both the environment and state produced by the exact allocation sequence. -/
def allocationSchedule (E : Env program.Γ) (s : GlobalState) :
    Env program.Γ × GlobalState :=
  let E0 := E
  let s0 := s
  let E1 := E0[%62 := .value s0.allocaPtr]
  let s1 := s0.alloca 8
  let E2 := E1[%63 := .value s1.allocaPtr]
  let s2 := s1.alloca 8
  let E3 := E2[%64 := .value s2.allocaPtr]
  let s3 := s2.alloca 8
  let E4 := E3[%65 := .value s3.allocaPtr]
  let s4 := s3.alloca 8
  let E5 := E4[%66 := .value s4.allocaPtr]
  let s5 := s4.alloca 8
  let E6 := E5[%67 := .value s5.allocaPtr]
  let s6 := s5.alloca 8
  let E7 := E6[%68 := .value s6.allocaPtr]
  let s7 := s6.alloca 8
  let E8 := E7[%69 := .value s7.allocaPtr]
  let s8 := s7.alloca 8
  let E9 := E8[%70 := .value s8.allocaPtr]
  let s9 := s8.alloca 8
  let E10 := E9[%71 := .value s9.allocaPtr]
  let s10 := s9.alloca 8
  let E11 := E10[%72 := .value s10.allocaPtr]
  let s11 := s10.alloca 8
  let E12 := E11[%73 := .value s11.allocaPtr]
  let s12 := s11.alloca 8
  let E13 := E12[%74 := .value s12.allocaPtr]
  let s13 := s12.alloca 8
  let E14 := E13[%75 := .value s13.allocaPtr]
  let s14 := s13.alloca 8
  let E15 := E14[%76 := .value s14.allocaPtr]
  let s15 := s14.alloca 8
  let E16 := E15[%77 := .value s15.allocaPtr]
  let s16 := s15.alloca 8
  let E17 := E16[%78 := .value s16.allocaPtr]
  let s17 := s16.alloca 8
  let E18 := E17[%79 := .value s17.allocaPtr]
  let s18 := s17.alloca 8
  let E19 := E18[%80 := .value s18.allocaPtr]
  let s19 := s18.alloca 8
  let E20 := E19[%81 := .value s19.allocaPtr]
  let s20 := s19.alloca 16
  let E21 := E20[%82 := .value s20.allocaPtr]
  let s21 := s20.alloca 16
  let E22 := E21[%83 := .value s21.allocaPtr]
  let s22 := s21.alloca 16
  let E23 := E22[%84 := .value s22.allocaPtr]
  let s23 := s22.alloca 16
  let E24 := E23[%85 := .value s23.allocaPtr]
  let s24 := s23.alloca 16
  let E25 := E24[%86 := .value s24.allocaPtr]
  let s25 := s24.alloca 16
  let E26 := E25[%87 := .value s25.allocaPtr]
  let s26 := s25.alloca 16
  let E27 := E26[%88 := .value s26.allocaPtr]
  let s27 := s26.alloca 16
  let E28 := E27[%89 := .value s27.allocaPtr]
  let s28 := s27.alloca 16
  let E29 := E28[%90 := .value s28.allocaPtr]
  let s29 := s28.alloca 8
  let E30 := E29[%91 := .value s29.allocaPtr]
  let s30 := s29.alloca 8
  let E31 := E30[%92 := .value s30.allocaPtr]
  let s31 := s30.alloca 8
  let E32 := E31[%93 := .value s31.allocaPtr]
  let s32 := s31.alloca 8
  let E33 := E32[%94 := .value s32.allocaPtr]
  let s33 := s32.alloca 8
  (E33, s33)

theorem allocations_execute (E : Env program.Γ) (s : GlobalState) :
    List.foldlM Instr.run E allocations s = .value (allocationSchedule E s) := by rfl

/-- Exact allocation count before unpacking and the embedded black_box call. -/
theorem allocationSchedule_count (E : Env program.Γ) (s : GlobalState) :
    (allocationSchedule E s).2.alloc.nextFreeBlock = s.alloc.nextFreeBlock + 33 := by
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
