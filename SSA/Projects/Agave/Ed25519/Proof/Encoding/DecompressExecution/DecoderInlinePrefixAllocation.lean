import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ParseInput
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Ready
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PrivateFrame

/-! Exact original decoder instructions bb0:0--44. Allocation results,
constant registers and live ranges are derived from the invocation state. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialPoint.Execution (smallRange_alloca smallRange_alloca_self)
open SmallOrder.Execution (PrivateFrame)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

abbrev state0 (s : GlobalState) := s
def state1 (s : GlobalState) : GlobalState := (state0 s).alloca 48
def state2 (s : GlobalState) : GlobalState := (state1 s).alloca 40
def state3 (s : GlobalState) : GlobalState := (state2 s).alloca 40
def state4 (s : GlobalState) : GlobalState := (state3 s).alloca 40
def state5 (s : GlobalState) : GlobalState := (state4 s).alloca 40
def state6 (s : GlobalState) : GlobalState := (state5 s).alloca 40
def state7 (s : GlobalState) : GlobalState := (state6 s).alloca 160
def state8 (s : GlobalState) : GlobalState := (state7 s).alloca 80
def state9 (s : GlobalState) : GlobalState := (state8 s).alloca 40
def state10 (s : GlobalState) : GlobalState := (state9 s).alloca 40

abbrev allocated := state10

def slot0 (s : GlobalState) : Pointer := (state0 s).allocaPtr
def slot1 (s : GlobalState) : Pointer := (state1 s).allocaPtr
def slot2 (s : GlobalState) : Pointer := (state2 s).allocaPtr
def slot3 (s : GlobalState) : Pointer := (state3 s).allocaPtr
def slot4 (s : GlobalState) : Pointer := (state4 s).allocaPtr
def slot5 (s : GlobalState) : Pointer := (state5 s).allocaPtr
def slot6 (s : GlobalState) : Pointer := (state6 s).allocaPtr
def slot7 (s : GlobalState) : Pointer := (state7 s).allocaPtr
def slot8 (s : GlobalState) : Pointer := (state8 s).allocaPtr
def slot9 (s : GlobalState) : Pointer := (state9 s).allocaPtr

def allocatedEnv (g : Globals) (E : Env program.Γ) (s : GlobalState) : Env program.Γ :=
  E[%0 := .value 1#32,
    %1 := .value 2251799813685247#64,
    %2 := .value 6#64,
    %3 := .value 3#64,
    %4 := .value 12#64,
    %5 := .value 19#64,
    %6 := .value 1#64,
    %7 := .value 24#64,
    %8 := .value 8#64,
    %9 := .value 16#64,
    %10 := .value 32#64,
    %11 := Ty.wrap #v[36028797018963663#64, 36028797018963952#64],
    %12 := Ty.wrap (Vector.replicate 2 36028797018963952#64),
    %13 := Ty.wrap (Vector.replicate 2 51#64),
    %14 := .value 0#64,
    %15 := Ty.wrap (Vector.replicate 2 2251799813685247#64),
    %16 := .value 51#64,
    %17 := .value g.address0,
    %18 := Ty.wrap #v[1#64, 0#64],
    %19 := .value 40#64,
    %20 := .value 0#8,
    %21 := .value 31#64,
    %22 := .value 7#8,
    %23 := .value 2251799813684944#64,
    %24 := Ty.wrap #v[36028797018963664#64, 36028797018963952#64],
    %25 := Ty.poisoned (.vec 2 64),
    %26 := .value 120#64,
    %27 := .value 80#64,
    %28 := .value 88#64,
    %29 := .value 160#64,
    %30 := .value (slot0 s),
    %31 := .value (slot1 s),
    %32 := .value (slot2 s),
    %33 := .value (slot3 s),
    %34 := .value (slot4 s),
    %35 := .value (slot5 s),
    %36 := .value (slot6 s),
    %37 := .value (slot7 s),
    %38 := .value (slot8 s),
    %39 := .value (slot9 s)]

theorem allocation_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) :
    Cutpoint.segment (program p g) 0 0 45 E s =
      .value (allocatedEnv g E s, allocated s) := rfl

theorem state0_wf (hwf : s.WF) : (state0 s).WF := hwf
theorem state1_wf (hwf : s.WF) : (state1 s).WF := (state0_wf hwf).alloca
theorem state2_wf (hwf : s.WF) : (state2 s).WF := (state1_wf hwf).alloca
theorem state3_wf (hwf : s.WF) : (state3 s).WF := (state2_wf hwf).alloca
theorem state4_wf (hwf : s.WF) : (state4 s).WF := (state3_wf hwf).alloca
theorem state5_wf (hwf : s.WF) : (state5 s).WF := (state4_wf hwf).alloca
theorem state6_wf (hwf : s.WF) : (state6 s).WF := (state5_wf hwf).alloca
theorem state7_wf (hwf : s.WF) : (state7 s).WF := (state6_wf hwf).alloca
theorem state8_wf (hwf : s.WF) : (state8 s).WF := (state7_wf hwf).alloca
theorem state9_wf (hwf : s.WF) : (state9 s).WF := (state8_wf hwf).alloca
theorem state10_wf (hwf : s.WF) : (state10 s).WF := (state9_wf hwf).alloca

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
theorem state9_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state9 s).mem q n := smallRange_alloca (state8_wf hwf) (state8_live hwf hr)
theorem state10_live (hwf : s.WF) (hr : SmallRange s.mem q n) :
    SmallRange (state10 s).mem q n := smallRange_alloca (state9_wf hwf) (state9_live hwf hr)

theorem slot0_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot0 s) 48 :=
  smallRange_alloca (state9_wf hwf) (smallRange_alloca (state8_wf hwf) (smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca (state4_wf hwf) (smallRange_alloca (state3_wf hwf) (smallRange_alloca (state2_wf hwf) (smallRange_alloca (state1_wf hwf) (smallRange_alloca_self (state0 s) 48 (by decide))))))))))

theorem slot1_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot1 s) 40 :=
  smallRange_alloca (state9_wf hwf) (smallRange_alloca (state8_wf hwf) (smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca (state4_wf hwf) (smallRange_alloca (state3_wf hwf) (smallRange_alloca (state2_wf hwf) (smallRange_alloca_self (state1 s) 40 (by decide)))))))))

theorem slot2_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot2 s) 40 :=
  smallRange_alloca (state9_wf hwf) (smallRange_alloca (state8_wf hwf) (smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca (state4_wf hwf) (smallRange_alloca (state3_wf hwf) (smallRange_alloca_self (state2 s) 40 (by decide))))))))

theorem slot3_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot3 s) 40 :=
  smallRange_alloca (state9_wf hwf) (smallRange_alloca (state8_wf hwf) (smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca (state4_wf hwf) (smallRange_alloca_self (state3 s) 40 (by decide)))))))

theorem slot4_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot4 s) 40 :=
  smallRange_alloca (state9_wf hwf) (smallRange_alloca (state8_wf hwf) (smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca (state5_wf hwf) (smallRange_alloca_self (state4 s) 40 (by decide))))))

theorem slot5_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot5 s) 40 :=
  smallRange_alloca (state9_wf hwf) (smallRange_alloca (state8_wf hwf) (smallRange_alloca (state7_wf hwf) (smallRange_alloca (state6_wf hwf) (smallRange_alloca_self (state5 s) 40 (by decide)))))

theorem slot6_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot6 s) 160 :=
  smallRange_alloca (state9_wf hwf) (smallRange_alloca (state8_wf hwf) (smallRange_alloca (state7_wf hwf) (smallRange_alloca_self (state6 s) 160 (by decide))))

theorem slot7_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot7 s) 80 :=
  smallRange_alloca (state9_wf hwf) (smallRange_alloca (state8_wf hwf) (smallRange_alloca_self (state7 s) 80 (by decide)))

theorem slot8_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot8 s) 40 :=
  smallRange_alloca (state9_wf hwf) (smallRange_alloca_self (state8 s) 40 (by decide))

theorem slot9_live (s : GlobalState) (hwf : s.WF) :
    SmallRange (allocated s).mem (slot9 s) 40 :=
  smallRange_alloca_self (state9 s) 40 (by decide)

theorem state0_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state0 s).mem.readAt q width = s.mem.readAt q width := rfl

theorem state1_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state1 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state0 s).alloca 48).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state0_wf hwf) (state0_live hwf hr).fits]

theorem state2_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state2 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state1 s).alloca 40).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state1_wf hwf) (state1_live hwf hr).fits]
  exact state1_read s hwf q n width hr

theorem state3_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state3 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state2 s).alloca 40).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state2_wf hwf) (state2_live hwf hr).fits]
  exact state2_read s hwf q n width hr

theorem state4_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state4 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state3 s).alloca 40).mem.readAt q width = _
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
  change ((state6 s).alloca 160).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state6_wf hwf) (state6_live hwf hr).fits]
  exact state6_read s hwf q n width hr

theorem state8_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state8 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state7 s).alloca 80).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state7_wf hwf) (state7_live hwf hr).fits]
  exact state7_read s hwf q n width hr

theorem state9_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state9 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state8 s).alloca 40).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state8_wf hwf) (state8_live hwf hr).fits]
  exact state8_read s hwf q n width hr

theorem state10_read (s : GlobalState) (hwf : s.WF) (q : Pointer) (n width : Nat)
    (hr : SmallRange s.mem q n) : (state10 s).mem.readAt q width = s.mem.readAt q width := by
  change ((state9 s).alloca 40).mem.readAt q width = _
  rw [MemoryState.readAt_alloca (state9_wf hwf) (state9_live hwf hr).fits]
  exact state9_read s hwf q n width hr

theorem allocation_frame (s : GlobalState) (hwf : s.WF) : PrivateFrame s (allocated s) :=
  ((((((((((PrivateFrame.refl s hwf).alloca 48).alloca 40).alloca 40).alloca 40).alloca 40).alloca 40).alloca 160).alloca 80).alloca 40).alloca 40

theorem allocation_ready (h : Ready g sg s) (hwf : s.WF) : Ready g sg (allocated s) :=
  ((((((((((h).alloca (state0_wf hwf) 48).alloca (state1_wf hwf) 40).alloca (state2_wf hwf) 40).alloca (state3_wf hwf) 40).alloca (state4_wf hwf) 40).alloca (state5_wf hwf) 40).alloca (state6_wf hwf) 160).alloca (state7_wf hwf) 80).alloca (state8_wf hwf) 40).alloca (state9_wf hwf) 40

@[simp] theorem slot0_id (s : GlobalState) :
    (slot0 s).id.id = s.alloc.nextFreeBlock + 0 := by
  simp [slot0, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot1_id (s : GlobalState) :
    (slot1 s).id.id = s.alloc.nextFreeBlock + 1 := by
  simp [slot1, state1, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot2_id (s : GlobalState) :
    (slot2 s).id.id = s.alloc.nextFreeBlock + 2 := by
  simp [slot2, state2, state1, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot3_id (s : GlobalState) :
    (slot3 s).id.id = s.alloc.nextFreeBlock + 3 := by
  simp [slot3, state3, state2, state1, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot4_id (s : GlobalState) :
    (slot4 s).id.id = s.alloc.nextFreeBlock + 4 := by
  simp [slot4, state4, state3, state2, state1, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot5_id (s : GlobalState) :
    (slot5 s).id.id = s.alloc.nextFreeBlock + 5 := by
  simp [slot5, state5, state4, state3, state2, state1, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot6_id (s : GlobalState) :
    (slot6 s).id.id = s.alloc.nextFreeBlock + 6 := by
  simp [slot6, state6, state5, state4, state3, state2, state1, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot7_id (s : GlobalState) :
    (slot7 s).id.id = s.alloc.nextFreeBlock + 7 := by
  simp [slot7, state7, state6, state5, state4, state3, state2, state1, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot8_id (s : GlobalState) :
    (slot8 s).id.id = s.alloc.nextFreeBlock + 8 := by
  simp [slot8, state8, state7, state6, state5, state4, state3, state2, state1, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

@[simp] theorem slot9_id (s : GlobalState) :
    (slot9 s).id.id = s.alloc.nextFreeBlock + 9 := by
  simp [slot9, state9, state8, state7, state6, state5, state4, state3, state2, state1, state0, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
