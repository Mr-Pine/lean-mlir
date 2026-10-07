import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.WordRefinement

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

/-- The concrete five-store poststate of a field call, reused at each point
conversion cut point. Its inputs are read before any output store. -/
def mulPost (s : GlobalState) (r a b : Pointer) : GlobalState :=
  { s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b)) }

theorem mulPost_call (s : GlobalState) (r a b : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40) :
    kernel.call (kernel.args (.value r) (.value a) (.value b)) s =
      .value (.nil, mulPost s r a b) :=
  kernel_call r a b s hwf hr ha hb

@[mlir_transport] theorem mulPost_wf (s : GlobalState) (r a b : Pointer)
    (hwf : s.WF) : (mulPost s r a b).WF :=
  wf_storeLimbs hwf r _

@[mlir_transport] theorem mulPost_smallRange (s : GlobalState) (r a b q : Pointer)
    (h : SmallRange s.mem q n) : SmallRange (mulPost s r a b).mem q n :=
  smallRange_storeLimbs h r _

@[mlir_read] theorem mulPost_readback (s : GlobalState) (r a b : Pointer)
    (hr : SmallRange s.mem r 40) :
    readLimbs (mulPost s r a b) r = machine (readLimbs s a) (readLimbs s b) :=
  readLimbs_storeLimbs s r _ hr

theorem mulPost_frame (s : GlobalState) (r a b q : Pointer) (bits : Nat)
    (hr : SmallRange s.mem r 40)
    (hd : (Range.of q bits).Disjoint (Range.of r 320)) :
    (mulPost s r a b).mem.readAt q bits = s.mem.readAt q bits :=
  readAt_storeLimbs_frame s.mem r q _ bits hr hd

theorem mulPost_field_frame (s : GlobalState) (r a b q : Pointer)
    (hr : SmallRange s.mem r 40) (hq : SmallRange s.mem q 40)
    (hd : (Range.of q 320).Disjoint (Range.of r 320)) :
    readLimbs (mulPost s r a b) q = readLimbs s q :=
  readLimbs_storeLimbs_frame s r q _ hr hq hd

/-- A point conversion's next multiplication gets an actual readable result,
its tight bound, and all disjoint memory unchanged. No callee contract premise
is needed: the call is the imported compiler field kernel. -/
theorem mulPost_correct (s : GlobalState) (r a b : Pointer)
    (hr : SmallRange s.mem r 40)
    (hA : Bounded (unsigned (readLimbs s a)))
    (hB : Bounded (unsigned (readLimbs s b))) :
    unsigned (readLimbs (mulPost s r a b) r) =
        mul (unsigned (readLimbs s a)) (unsigned (readLimbs s b)) ∧
      Tight (unsigned (readLimbs (mulPost s r a b) r)) := by
  rw [mulPost_readback s r a b hr]
  exact ⟨machine_unsigned_mul _ _ hA hB, machine_unsigned_tight _ _ hA hB⟩

end Agave.Ed25519.SerialPoint.Execution
