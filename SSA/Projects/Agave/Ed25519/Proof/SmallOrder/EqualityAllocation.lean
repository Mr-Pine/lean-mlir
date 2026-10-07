import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityPhases
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PrivateFrame

/-! Execute the equality body's exact 47 constants and eight allocations.
All buffer bounds, caller-live-range preservation, and cleanup memory are
derived from the initial state's WF; no allocation-result premise is needed. -/
namespace Agave.Ed25519.SmallOrder.Execution.EqualityAllocation
open LeanMLIR.RIR Verifier.Execution.PointConstantTimeEq
open Reduce64.Execution (SmallRange)
open SerialPoint.Execution (smallRange_alloca smallRange_alloca_self)
set_option maxRecDepth 16000

abbrev state0 (s : GlobalState) := s
def state1 (s : GlobalState) : GlobalState := (state0 s).alloca 32
def state2 (s : GlobalState) : GlobalState := (state1 s).alloca 32
def state3 (s : GlobalState) : GlobalState := (state2 s).alloca 32
def state4 (s : GlobalState) : GlobalState := (state3 s).alloca 32
def state5 (s : GlobalState) : GlobalState := (state4 s).alloca 40
def state6 (s : GlobalState) : GlobalState := (state5 s).alloca 40
def state7 (s : GlobalState) : GlobalState := (state6 s).alloca 40
def state8 (s : GlobalState) : GlobalState := (state7 s).alloca 40

abbrev allocated := state8

def slot0 (s : GlobalState) : Pointer := (state0 s).allocaPtr
def slot1 (s : GlobalState) : Pointer := (state1 s).allocaPtr
def slot2 (s : GlobalState) : Pointer := (state2 s).allocaPtr
def slot3 (s : GlobalState) : Pointer := (state3 s).allocaPtr
def slot4 (s : GlobalState) : Pointer := (state4 s).allocaPtr
def slot5 (s : GlobalState) : Pointer := (state5 s).allocaPtr
def slot6 (s : GlobalState) : Pointer := (state6 s).allocaPtr
def slot7 (s : GlobalState) : Pointer := (state7 s).allocaPtr

def preparedEnv (E : Env program.Γ) (s : GlobalState) : Env program.Γ :=
  E[%0 := .value 1#32,
    %1 := .value 80#64,
    %2 := .value 8#64,
    %3 := .value 16#64,
    %4 := .value 24#64,
    %5 := .value 32#64,
    %6 := .value 51#64,
    %7 := .value 2251799813685247#64,
    %8 := .value 19#64,
    %9 := .value 1#64,
    %10 := .value 2#64,
    %11 := .value 3#64,
    %12 := .value 4#64,
    %13 := .value 40#64,
    %14 := .value 5#64,
    %15 := .value 48#64,
    %16 := .value 7#64,
    %17 := .value 6#64,
    %18 := .value 13#64,
    %19 := .value 21#64,
    %20 := .value 9#64,
    %21 := .value 29#64,
    %22 := .value 10#64,
    %23 := .value 37#64,
    %24 := .value 11#64,
    %25 := .value 45#64,
    %26 := .value 12#64,
    %27 := .value 14#64,
    %28 := .value 18#64,
    %29 := .value 15#64,
    %30 := .value 26#64,
    %31 := .value 34#64,
    %32 := .value 17#64,
    %33 := .value 42#64,
    %34 := .value 50#64,
    %35 := .value 20#64,
    %36 := .value 23#64,
    %37 := .value 22#64,
    %38 := .value 31#64,
    %39 := .value 39#64,
    %40 := .value 47#64,
    %41 := .value 25#64,
    %42 := .value 27#64,
    %43 := .value 28#64,
    %44 := .value 36#64,
    %45 := .value 30#64,
    %46 := .value 44#64,
    %47 := .value (slot0 s),
    %48 := .value (slot1 s),
    %49 := .value (slot2 s),
    %50 := .value (slot3 s),
    %51 := .value (slot4 s),
    %52 := .value (slot5 s),
    %53 := .value (slot6 s),
    %54 := .value (slot7 s)]

/-- Direct reduction of the unchanged preparation slice. -/
theorem prepare_run (p : Primitives) (E : Env program.Γ) (s : GlobalState) :
    List.foldlM Instr.run E (EqualityPhases.prepare p) s =
      .value (preparedEnv E s, allocated s) := rfl

theorem state0_wf (hwf : s.WF) : (state0 s).WF := hwf
theorem state1_wf (hwf : s.WF) : (state1 s).WF := (state0_wf hwf).alloca
theorem state2_wf (hwf : s.WF) : (state2 s).WF := (state1_wf hwf).alloca
theorem state3_wf (hwf : s.WF) : (state3 s).WF := (state2_wf hwf).alloca
theorem state4_wf (hwf : s.WF) : (state4 s).WF := (state3_wf hwf).alloca
theorem state5_wf (hwf : s.WF) : (state5 s).WF := (state4_wf hwf).alloca
theorem state6_wf (hwf : s.WF) : (state6 s).WF := (state5_wf hwf).alloca
theorem state7_wf (hwf : s.WF) : (state7 s).WF := (state6_wf hwf).alloca
theorem state8_wf (hwf : s.WF) : (state8 s).WF := (state7_wf hwf).alloca

theorem state0_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state0 s).mem q n := hr
theorem state1_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state1 s).mem q n := smallRange_alloca (state0_wf hwf) (state0_live hwf hr)
theorem state2_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state2 s).mem q n := smallRange_alloca (state1_wf hwf) (state1_live hwf hr)
theorem state3_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state3 s).mem q n := smallRange_alloca (state2_wf hwf) (state2_live hwf hr)
theorem state4_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state4 s).mem q n := smallRange_alloca (state3_wf hwf) (state3_live hwf hr)
theorem state5_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state5 s).mem q n := smallRange_alloca (state4_wf hwf) (state4_live hwf hr)
theorem state6_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state6 s).mem q n := smallRange_alloca (state5_wf hwf) (state5_live hwf hr)
theorem state7_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state7 s).mem q n := smallRange_alloca (state6_wf hwf) (state6_live hwf hr)
theorem state8_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state8 s).mem q n := smallRange_alloca (state7_wf hwf) (state7_live hwf hr)

theorem slot0_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot0 s) 32 :=
  smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca (state4_wf hwf) (smallRange_alloca (state3_wf hwf) (smallRange_alloca (state2_wf hwf) (smallRange_alloca (state1_wf hwf) (smallRange_alloca_self (state0 s) 32 (by decide))))))))

theorem slot1_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot1 s) 32 :=
  smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca (state4_wf hwf) (smallRange_alloca (state3_wf hwf) (smallRange_alloca (state2_wf hwf) (smallRange_alloca_self (state1 s) 32 (by decide)))))))

theorem slot2_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot2 s) 32 :=
  smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca (state4_wf hwf) (smallRange_alloca (state3_wf hwf) (smallRange_alloca_self (state2 s) 32 (by decide))))))

theorem slot3_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot3 s) 32 :=
  smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca (state4_wf hwf) (smallRange_alloca_self (state3 s) 32 (by decide)))))

theorem slot4_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot4 s) 40 :=
  smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca_self (state4 s) 40 (by decide))))

theorem slot5_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot5 s) 40 :=
  smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca_self (state5 s) 40 (by decide)))

theorem slot6_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot6 s) 40 :=
  smallRange_alloca (state7_wf hwf) (smallRange_alloca_self (state6 s) 40 (by decide))

theorem slot7_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot7 s) 40 :=
  smallRange_alloca_self (state7 s) 40 (by decide)

theorem state0_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state0 s).mem.readAt q width = s.mem.readAt q width := rfl

theorem state1_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state1 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state0 s).alloca 32).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state0_wf hwf) (state0_live hwf hr).fits]

theorem state2_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state2 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state1 s).alloca 32).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state1_wf hwf) (state1_live hwf hr).fits]
  exact state1_read s hwf q n width hr

theorem state3_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state3 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state2 s).alloca 32).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state2_wf hwf) (state2_live hwf hr).fits]
  exact state2_read s hwf q n width hr

theorem state4_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state4 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state3 s).alloca 32).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state3_wf hwf) (state3_live hwf hr).fits]
  exact state3_read s hwf q n width hr

theorem state5_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state5 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state4 s).alloca 40).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state4_wf hwf) (state4_live hwf hr).fits]
  exact state4_read s hwf q n width hr

theorem state6_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state6 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state5 s).alloca 40).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state5_wf hwf) (state5_live hwf hr).fits]
  exact state5_read s hwf q n width hr

theorem state7_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state7 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state6 s).alloca 40).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state6_wf hwf) (state6_live hwf hr).fits]
  exact state6_read s hwf q n width hr

theorem state8_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state8 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state7 s).alloca 40).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state7_wf hwf) (state7_live hwf hr).fits]
  exact state7_read s hwf q n width hr

theorem allocated_frame (s : GlobalState) (hwf : s.WF) : PrivateFrame s (allocated s) :=
  ((((((((PrivateFrame.refl s hwf).alloca 32).alloca 32).alloca 32).alloca 32).alloca 40).alloca 40).alloca 40).alloca 40

end Agave.Ed25519.SmallOrder.Execution.EqualityAllocation
