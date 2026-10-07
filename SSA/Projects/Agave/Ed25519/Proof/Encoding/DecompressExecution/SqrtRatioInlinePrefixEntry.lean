import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioExecutionComposition
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Ready

/-! Actual entry instructions of sqrt_ratio_i. The first 86 instructions only
initialize constants and twenty-two private allocations. This module executes
that slice without a prefix-success or global-memory premise, and transports
invocation readiness through its allocations. Arithmetic begins at pc86.
-/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Total model of the initialization instruction forms. It is used only for
the checked entry slice, whose exact execution is established below. -/
def initInstruction (pair : ⟪program.Γ⟫ × GlobalState)
    (inst : Instr program.Γ) : ⟪program.Γ⟫ × GlobalState :=
  match inst with
  | .const v dst => (pair.1.write dst (Ty.wrap v), pair.2)
  | .poison dst => (pair.1.write dst (Ty.poisoned _), pair.2)
  | .alloca dst bytes =>
    (pair.1.write dst (.value pair.2.allocaPtr), pair.2.alloca bytes)
  | _ => pair

def allocationSizes : List Nat :=
  [32,32,32,32,32,32,40,80,40,40,40,40,40,40,40,40,40,40,40,40,40,40]

def allocate (s : GlobalState) : List Nat → GlobalState
  | [] => s
  | n :: ns => allocate (s.alloca n) ns

noncomputable def entryResult (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState) :
    ⟪program.Γ⟫ × GlobalState :=
  ((program.entry sqrtRatioPrimitives g).body.take 86).foldl initInstruction (E, s)

set_option maxRecDepth 10000 in
/-- This is the original 86-instruction source slice, with no replacement calls. -/
theorem entry_segment (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 86 E s =
      .value (entryResult g E s) := by
  rfl

set_option maxRecDepth 10000 in
theorem entry_state (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState) :
    (entryResult g E s).2 = allocate s allocationSizes := by
  rfl

theorem allocate_counter (s : GlobalState) (ns : List Nat) :
    (allocate s ns).alloc.nextFreeBlock = s.alloc.nextFreeBlock + ns.length := by
  induction ns generalizing s with
  | nil => simp [allocate]
  | cons n ns ih => simp only [allocate, ih, GlobalState.alloca_alloc, List.length_cons]; omega

theorem allocate_wf (s : GlobalState) (hwf : s.WF) (ns : List Nat) :
    (allocate s ns).WF := by
  induction ns generalizing s with
  | nil => exact hwf
  | cons n ns ih => exact ih (s.alloca n) (by simpa using hwf.alloca (n := n))

theorem allocate_ready (dg : Decode.Globals) (sg : Globals) (s : GlobalState)
    (hwf : s.WF) (hready : Ready dg sg s) (ns : List Nat) :
    Ready dg sg (allocate s ns) := by
  induction ns generalizing s with
  | nil => exact hready
  | cons n ns ih =>
    exact ih (s.alloca n) (by simpa using hwf.alloca (n := n)) (hready.alloca hwf n)

theorem entry_ready (dg : Decode.Globals) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (hwf : s.WF) (hready : Ready dg g s) :
    (entryResult g E s).2.WF ∧ Ready dg g (entryResult g E s).2 ∧
      (entryResult g E s).2.alloc.nextFreeBlock = s.alloc.nextFreeBlock + 22 := by
  rw [entry_state]
  exact ⟨allocate_wf s hwf _, allocate_ready dg g s hwf hready _,
    allocate_counter s allocationSizes⟩

theorem alloca_live (s : GlobalState) (hwf : s.WF) (p : Pointer)
    (h : SmallRange s.mem p bytes) (n : Nat) : SmallRange (s.alloca n).mem p bytes := by
  have hne := GlobalState.ne_allocaPtr_of_fits hwf h.fits
  obtain ⟨b, hb, hs, hz⟩ := h
  exact ⟨b, (GlobalState.getElem?_alloca hne).trans hb, hs, hz⟩

/-- Every caller range remains live throughout the actual entry allocations. -/
theorem allocate_live (s : GlobalState) (hwf : s.WF) (ns : List Nat)
    {p : Pointer} {bytes : Nat} (h : SmallRange s.mem p bytes) : SmallRange (allocate s ns).mem p bytes := by
  induction ns generalizing s with
  | nil => exact h
  | cons n ns ih =>
    exact ih (s.alloca n) hwf.alloca (alloca_live s hwf p h n)

theorem allocate_read (s : GlobalState) (hwf : s.WF) (ns : List Nat)
    {p : Pointer} {width : Nat} (h : Fits s.mem p width) :
    (allocate s ns).mem.readAt p width = s.mem.readAt p width := by
  induction ns generalizing s with
  | nil => rfl
  | cons n ns ih =>
    exact (ih (s.alloca n) hwf.alloca (h.alloca hwf)).trans
      (MemoryState.readAt_alloca hwf h)

theorem allocate_erase (s : GlobalState) (ns : List Nat) (mark : Nat)
    (hmark : mark ≤ s.alloc.nextFreeBlock) :
    (allocate s ns).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  induction ns generalizing s with
  | nil => rfl
  | cons n ns ih =>
    change (allocate (s.alloca n) ns).mem.eraseFrom mark = _
    rw [ih (s.alloca n) (by simpa only [GlobalState.alloca_alloc] using Nat.le_trans hmark (Nat.le_add_right _ 1)),
      GlobalState.eraseFrom_alloca_of_le hmark]

theorem entry_public (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState) (hwf : s.WF) :
    (entryResult g E s).2.mem.eraseFrom s.alloc.nextFreeBlock = s.mem := by
  rw [entry_state, allocate_erase s allocationSizes _ (Nat.le_refl _)]
  exact congrArg GlobalState.mem (GlobalState.eraseFrom_self hwf)

/-- Scratch registers 62 through 83 are allocated consecutively. -/
def slot (s : GlobalState) (i : Nat) : Pointer :=
  (allocate s (allocationSizes.take i)).allocaPtr

def slotRegister : Fin 22 → Reg program.Γ .ptr :=
  ![(%62), (%63), (%64), (%65), (%66), (%67), (%68), (%69), (%70), (%71), (%72), (%73), (%74), (%75), (%76), (%77), (%78), (%79), (%80), (%81), (%82), (%83)]

set_option maxRecDepth 10000 in
theorem entry_slot (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState) (i : Fin 22) :
    (entryResult g E s).1.read (slotRegister i) = .value (slot s i) := by
  fin_cases i <;> rfl

private theorem initInstruction_args (pair : ⟪program.Γ⟫ × GlobalState)
    (inst : Instr program.Γ) : (initInstruction pair inst).1.args = pair.1.args := by
  cases inst <;> rfl

private theorem fold_args (insts : List (Instr program.Γ))
    (pair : ⟪program.Γ⟫ × GlobalState) :
    (insts.foldl initInstruction pair).1.args = pair.1.args := by
  induction insts generalizing pair with
  | nil => rfl
  | cons inst insts ih => exact (ih _).trans (initInstruction_args pair inst)

theorem entry_args (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState) :
    (entryResult g E s).1.args = E.args := fold_args _ _

set_option maxRecDepth 10000 in
theorem entry_first_count (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState) :
    (entryResult g E s).1.read (%0) = .value 1#32 := by rfl

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
