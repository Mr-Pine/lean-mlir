import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseRepresentation
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseTable

/-! Concrete memory states shared by the four add/subtract blocks. Every state
is a finite list of actual stores or the actual 160-byte copy. The helper
boundaries are consequences of MulContract; no block execution is assumed. -/
namespace Agave.Ed25519.Avx2PointAdd.Phases
open LeanMLIR.RIR Avx2FieldMul.Execution Reduce64.Execution

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

structure Scratch where
  output : Pointer
  prepared : Pointer
  product : Pointer
  left : Pointer
  right : Pointer
  negative : Pointer

def Scratch.address (q : Scratch) (cached : Pointer) : Fin 7 → Pointer :=
  ![q.output, q.prepared, q.product, q.left, q.right, q.negative, cached]

def Scratch.written (q : Scratch) : Fin 6 → Pointer :=
  ![q.output, q.prepared, q.product, q.left, q.right, q.negative]

structure MemoryReady (s : GlobalState) (q : Scratch) (cached : Pointer) : Prop where
  wf : s.WF
  live : ∀ i, SmallRange s.mem (q.address cached i) 160
  distinct : Function.Injective (fun i => (q.address cached i).id)

theorem MemoryReady.ne (h : MemoryReady s q cached) (i j : Fin 7) (hij : i ≠ j) :
    (q.address cached i).id ≠ (q.address cached j).id := fun heq => hij (h.distinct heq)

def chosenCache (negative : Bool) (C : Point) : Point := if negative then negate C else C
def cachePointer (negative : Bool) (q : Scratch) (cached : Pointer) : Pointer :=
  if negative then q.negative else cached
def productPoint (negative : Bool) (P C : Point) : Point :=
  multiply (prepare P) (chosenCache negative C)
def differencePoint (negative : Bool) (P C : Point) : Point :=
  diffSum (shuffleABDC (productPoint negative P C))
def leftPoint (negative : Bool) (P C : Point) : Point :=
  shuffleADDA (differencePoint negative P C)
def rightPoint (negative : Bool) (P C : Point) : Point :=
  shuffleCBCB (differencePoint negative P C)
def resultPoint (negative : Bool) (P C : Point) : Point :=
  multiply (leftPoint negative P C) (rightPoint negative P C)

theorem resultPoint_eq (negative : Bool) (P C : Point) :
    resultPoint negative P C = if negative then sub P C else add P C := by
  cases negative <;> rfl

theorem pointReduced_wide {P : Point} (h : pointReduced P) : pointWide P :=
  ⟨reduced_wide h.1, reduced_wide h.2.1, reduced_wide h.2.2.1, reduced_wide h.2.2.2⟩

theorem chosenCache_wide (negative : Bool) {C : Point} (hC : pointReduced C) :
    pointWide (chosenCache negative C) := by
  cases negative
  · exact pointReduced_wide hC
  · exact negate_wide (pointReduced_wide hC)

theorem productPoint_reduced (negative : Bool) {P C : Point}
    (hP : pointReduced P) (hC : pointReduced C) :
    pointReduced (productPoint negative P C) :=
  multiply_reduced (prepare_wide hP) (chosenCache_wide negative hC)

theorem differencePoint_wide (negative : Bool) {P C : Point}
    (hP : pointReduced P) (hC : pointReduced C) :
    pointWide (differencePoint negative P C) := by
  have h := productPoint_reduced negative hP hC
  exact diffSum_wide ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

theorem leftPoint_wide (negative : Bool) {P C : Point}
    (hP : pointReduced P) (hC : pointReduced C) : pointWide (leftPoint negative P C) := by
  have h := differencePoint_wide negative hP hC
  exact ⟨h.1, h.2.2.2, h.2.2.2, h.1⟩

theorem rightPoint_wide (negative : Bool) {P C : Point}
    (hP : pointReduced P) (hC : pointReduced C) : pointWide (rightPoint negative P C) := by
  have h := differencePoint_wide negative hP hC
  exact ⟨h.2.2.1, h.2.1, h.2.2.1, h.2.1⟩

theorem resultPoint_reduced (negative : Bool) {P C : Point}
    (hP : pointReduced P) (hC : pointReduced C) : pointReduced (resultPoint negative P C) :=
  multiply_reduced (leftPoint_wide negative hP hC) (rightPoint_wide negative hP hC)

def writePoint (s : GlobalState) (p : Pointer) (P : Point) : GlobalState :=
  {s with mem := storeBlocks s.mem p (packPoint P)}

/-- Stage 0 is entry; 1 optional cache negation; 2 preparation; 3 first
product; 4 copied product; 5/6 factor stores; 7 final product. -/
def pipelineState (s : GlobalState) (q : Scratch) (negative : Bool) (P C : Point) :
    Fin 8 → GlobalState :=
  let s1 := if negative then writePoint s q.negative (negate C) else s
  let s2 := writePoint s1 q.prepared (prepare P)
  let s3 := writePoint s2 q.product (productPoint negative P C)
  let s4 := {s3 with mem := copyPointBytes s3.mem q.prepared q.product}
  let s5 := writePoint s4 q.left (leftPoint negative P C)
  let s6 := writePoint s5 q.right (rightPoint negative P C)
  let s7 := writePoint s6 q.output (resultPoint negative P C)
  ![s, s1, s2, s3, s4, s5, s6, s7]

theorem pipelineState_wf (s : GlobalState) (q : Scratch) (negative : Bool) (P C : Point)
    (hs : s.WF) (stage : Fin 8) : (pipelineState s q negative P C stage).WF := by
  fin_cases stage <;> cases negative <;>
    simpa [pipelineState, writePoint, storeBlocks, copyPointBytes, GlobalState.WF_storeAt] using hs

theorem pipelineState_live (s : GlobalState) (q : Scratch) (negative : Bool) (P C : Point)
    {ptr : Pointer} {bytes : Nat} (h : SmallRange s.mem ptr bytes) (stage : Fin 8) :
    SmallRange (pipelineState s q negative P C stage).mem ptr bytes := by
  have h1 : SmallRange (pipelineState s q negative P C 1).mem ptr bytes := by
    cases negative
    · exact h
    · exact storeBlocks_live h q.negative (packPoint (negate C))
  have h2 := storeBlocks_live h1 q.prepared (packPoint (prepare P))
  have h3 := storeBlocks_live h2 q.product (packPoint (productPoint negative P C))
  have h4 := copyPointBytes_live h3 q.prepared q.product
  have h5 := storeBlocks_live h4 q.left (packPoint (leftPoint negative P C))
  have h6 := storeBlocks_live h5 q.right (packPoint (rightPoint negative P C))
  have h7 := storeBlocks_live h6 q.output (packPoint (resultPoint negative P C))
  fin_cases stage
  · exact h
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

theorem prepared_read (s : GlobalState) (q : Scratch) (negative : Bool) (P C : Point)
    (h : SmallRange s.mem q.prepared 160) :
    readBlocks (pipelineState s q negative P C 2).mem q.prepared = packPoint (prepare P) :=
  readBlocks_storeBlocks _ _ _ (pipelineState_live s q negative P C h 1)

theorem cache_read (s : GlobalState) (q : Scratch) (negative : Bool) (cached : Pointer)
    (P C : Point) (h : MemoryReady s q cached) (hc : readBlocks s.mem cached = packPoint C) :
    readBlocks (pipelineState s q negative P C 2).mem (cachePointer negative q cached) =
      packPoint (chosenCache negative C) := by
  have hn : q.prepared.id ≠ q.negative.id := h.ne 1 5 (by decide)
  have ht : q.prepared.id ≠ cached.id := h.ne 1 6 (by decide)
  cases negative
  · change readBlocks (storeBlocks s.mem q.prepared (packPoint (prepare P))) cached = _
    rw [readBlocks_storeBlocks_ne _ _ _ _ ht]
    exact hc
  · change readBlocks (storeBlocks (storeBlocks s.mem q.negative (packPoint (negate C)))
        q.prepared (packPoint (prepare P))) q.negative = _
    rw [readBlocks_storeBlocks_ne _ _ _ _ hn]
    exact readBlocks_storeBlocks _ _ _ (h.live 5)

theorem product_read (s : GlobalState) (q : Scratch) (negative : Bool) (P C : Point)
    (h : SmallRange s.mem q.product 160) :
    readBlocks (pipelineState s q negative P C 3).mem q.product =
      packPoint (productPoint negative P C) :=
  readBlocks_storeBlocks _ _ _ (pipelineState_live s q negative P C h 2)

theorem copied_read (s : GlobalState) (q : Scratch) (negative : Bool) (P C : Point)
    (hp : SmallRange s.mem q.prepared 160) (hm : SmallRange s.mem q.product 160) :
    readBlocks (pipelineState s q negative P C 4).mem q.prepared =
      packPoint (productPoint negative P C) := by
  exact (copyPointBytes_readBlocks _ _ _ (pipelineState_live s q negative P C hp 3)
    (pipelineState_live s q negative P C hm 3)).trans (product_read s q negative P C hm)

theorem factors_read (s : GlobalState) (q : Scratch) (negative : Bool) (cached : Pointer)
    (P C : Point) (h : MemoryReady s q cached) :
    readBlocks (pipelineState s q negative P C 6).mem q.left = packPoint (leftPoint negative P C) ∧
    readBlocks (pipelineState s q negative P C 6).mem q.right = packPoint (rightPoint negative P C) := by
  constructor
  · change readBlocks (storeBlocks (pipelineState s q negative P C 5).mem q.right
        (packPoint (rightPoint negative P C))) q.left = _
    have hne : q.right.id ≠ q.left.id := h.ne 4 3 (by decide)
    rw [readBlocks_storeBlocks_ne _ _ _ _ hne]
    exact readBlocks_storeBlocks _ _ _ (pipelineState_live s q negative P C (h.live 3) 4)
  · exact readBlocks_storeBlocks _ _ _ (pipelineState_live s q negative P C (h.live 4) 5)

theorem result_read (s : GlobalState) (q : Scratch) (negative : Bool) (P C : Point)
    (h : SmallRange s.mem q.output 160) :
    readBlocks (pipelineState s q negative P C 7).mem q.output =
      packPoint (resultPoint negative P C) :=
  readBlocks_storeBlocks _ _ _ (pipelineState_live s q negative P C h 6)

/-- The complete caller-visible memory frame. Any digit array, global/table,
input or output object in a different allocation from these scratch objects
retains every byte, with arbitrary read width. -/
structure OutputFrame (q : Scratch) (before after : GlobalState) : Prop where
  allocation : after.alloc = before.alloc
  wellFormed : after.WF
  live : ∀ (ptr : Pointer) (bytes : Nat),
    SmallRange before.mem ptr bytes → SmallRange after.mem ptr bytes
  read : ∀ (ptr : Pointer) (width : Nat),
    (∀ i, (q.written i).id ≠ ptr.id) →
    after.mem.readAt ptr width = before.mem.readAt ptr width

theorem pipelineState_frame (s : GlobalState) (q : Scratch) (negative : Bool) (P C : Point)
    (hs : s.WF) (stage : Fin 8) : OutputFrame q s (pipelineState s q negative P C stage) := by
  refine ⟨?_, pipelineState_wf s q negative P C hs stage, ?_, ?_⟩
  · fin_cases stage <;> cases negative <;> rfl
  · intro ptr bytes hlive
    exact pipelineState_live s q negative P C hlive stage
  · intro ptr width hne
    have h0 : q.output.id ≠ ptr.id := hne 0
    have h1 : q.prepared.id ≠ ptr.id := hne 1
    have h2 : q.product.id ≠ ptr.id := hne 2
    have h3 : q.left.id ≠ ptr.id := hne 3
    have h4 : q.right.id ≠ ptr.id := hne 4
    have h5 : q.negative.id ≠ ptr.id := hne 5
    fin_cases stage <;> cases negative <;>
      simp [pipelineState, writePoint, readAt_storeBlocks_ne _ _ _ _ _ h0,
      readAt_storeBlocks_ne _ _ _ _ _ h1, readAt_storeBlocks_ne _ _ _ _ _ h2,
      readAt_storeBlocks_ne _ _ _ _ _ h3, readAt_storeBlocks_ne _ _ _ _ _ h4,
      readAt_storeBlocks_ne _ _ _ _ _ h5, readAt_copyPointBytes_ne _ _ _ _ _ h1]

end Agave.Ed25519.Avx2PointAdd.Phases
