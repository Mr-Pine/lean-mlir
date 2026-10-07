import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceInitContract
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Initialize

/-! A call-observation adapter between independently executed source CFGs.
Only the context block and its offset are related. Block identifiers, unrelated
allocations, globals, and full final machine states need not agree. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM
open Agave.Ed25519.Reduce64.Execution
attribute [local irreducible] init append core finish initMemory initBlock storeBlock Init.memory
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The byte/length observation shared by the two memory models. -/
def ofRirBlock (b : RIR.MemoryBlock) : LiveBlock := ⟨b.length, b.bytes⟩

theorem rir_storeAt_block (m : RIR.MemoryState) (p : RIR.Pointer) (value : BitVec w) :
    ((m.storeAt p value)[p.id]?).map ofRirBlock =
      storeBlock ((m[p.id]?).map ofRirBlock) p.offset value := by
  cases h : m[p.id]? with
  | none => simp only [RIR.MemoryState.storeAt, h, Option.map_none, storeBlock]
  | some b =>
    rw [RIR.MemoryState.getElem?_storeAt_self h]
    unfold storeBlock
    rfl

theorem rir_initMemory_block (m : RIR.MemoryState) (p : RIR.Pointer) :
    ((Init.memory m p)[p.id]?).map ofRirBlock =
      initBlock ((m[p.id]?).map ofRirBlock) p.offset := by
  simp only [Init.memory, initBlock, rir_storeAt_block, RIR.Pointer.add]

/-- Observe whether init returns its context pointer, and the complete context
allocation after that actual call. `none` records poison or a wrong pointer. -/
noncomputable def initObserve (s : GlobalState) (p : Pointer) : Option (Option LiveBlock) :=
  match StateT.run (runFunction (init.denote (Ctxt.Valuation.singleton (.value p)))) s with
  | .poison => none
  | .value ([.poison]ₕ, _) => none
  | .value ([.value ret]ₕ, after) => if ret = p then some (after.mem.live? p.id) else none

def rirInitObserve (s : RIR.GlobalState) (p : RIR.Pointer) : Option (Option LiveBlock) :=
  match Init.program.call (Init.program.args (.value p)) s with
  | .poison => none
  | .value (.cons .poison .nil, _) => none
  | .value (.cons (.value ret) .nil, after) =>
      if ret = p then some ((after.mem[p.id]?).map ofRirBlock) else none

theorem initObserve_eq (s : GlobalState) (p : Pointer) (hwf : s.WF)
    (hr : Fits s.mem p (224 * 8)) :
    initObserve s p = some (initBlock (s.mem.live? p.id) p.offset) := by
  unfold initObserve
  rw [init_call p s hr]
  change (if p = p then some (((initMemory s.mem p).killFrom s.alloc.nextFreeBlock).live? p.id) else none) = _
  rw [ite_eq_left rfl]
  rw [live?_killFrom_of_lt (Firedancer.lt_nextFreeBlock_of_fits hwf hr), initMemory_block]

theorem rirInitObserve_eq (s : RIR.GlobalState) (p : RIR.Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem p 224) :
    rirInitObserve s p = some (initBlock ((s.mem[p.id]?).map ofRirBlock) p.offset) := by
  unfold rirInitObserve
  rw [Init.call s p hwf hr]
  change (if p = p then some (((Init.memory s.mem p)[p.id]?).map ofRirBlock) else none) = _
  rw [ite_eq_left rfl]
  rw [rir_initMemory_block]

/-- Initializer source calls have equal visible context blocks from equal
input blocks/offsets and each dialect's own addressability conditions.
Neither execution, return pointer, nor memory frame is a hypothesis. -/
theorem init_call_observation_eq
    (s : GlobalState) (p : Pointer) (r : RIR.GlobalState) (q : RIR.Pointer)
    (hs : s.WF) (hr : Fits s.mem p (224 * 8))
    (hrs : r.WF) (hrr : SmallRange r.mem q 224)
    (hblock : s.mem.live? p.id = (r.mem[q.id]?).map ofRirBlock)
    (hoff : p.offset = q.offset) :
    initObserve s p = rirInitObserve r q := by
  rw [initObserve_eq s p hs hr, rirInitObserve_eq r q hrs hrr, hblock, hoff]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
