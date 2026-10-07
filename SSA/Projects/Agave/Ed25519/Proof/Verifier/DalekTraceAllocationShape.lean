import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekPrefixAllocationShape
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekPrefixTrace

/-! Actual prefix traces preserve allocation lengths, independently of scalar
and point values. This supplies structural information absent from byte frames. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace AllocationShape

theorem identityStores (s : GlobalState) (out : Pointer) :
    AllocationShape s (identityStoreState s out) := by
  intro id
  simp only [identityStoreState, SerialPoint.Execution.storeAt_allocationShape]

theorem optionCopies (s : GlobalState) (out slot29 slot30 point : Pointer) :
    AllocationShape s (optionCopyState s out slot29 slot30 point) := by
  intro id
  simp only [optionCopyState, copyPointState, SerialPoint.Execution.storeAt_allocationShape]

theorem scalarCopy (s : GlobalState) (signature scalar : Pointer) (first : BitVec 8) :
    AllocationShape s (scalarCopyState s signature scalar first) := by
  intro id
  simp only [scalarCopyState, SerialPoint.Execution.storeAt_allocationShape]

end AllocationShape

theorem pointTrace_allocationShape (p : Primitives) (q : PointPointers) (before after : GlobalState)
    (hcofactor : p.pointMulByPow2 = SmallOrder.Execution.cofactorProgram.call)
    (hequality : p.pointConstantTimeEq = SmallOrder.Execution.equalityProgram.call)
    (hwf : before.WF) (hp : SmallRange before.mem q.point 160)
    (hc : SmallRange before.mem q.cofactor 160) (hi : SmallRange before.mem q.identity 160)
    (ht : PointCallTrace p q before after) : AllocationShape before after := by
  obtain ⟨middle, returned, hm, he⟩ := ht
  rw [hcofactor] at hm
  rw [hequality] at he
  let copied := optionCopyState before q.option q.slot29 q.slot30 q.point
  have hwc : copied.WF := option_copy_wf before _ _ _ _ hwf
  have hpc : SmallRange copied.mem q.point 160 := option_copy_live before _ _ _ _ _ _ hp
  have hcc : SmallRange copied.mem q.cofactor 160 := option_copy_live before _ _ _ _ _ _ hc
  have hic : SmallRange copied.mem q.identity 160 := option_copy_live before _ _ _ _ _ _ hi
  have hp120 : SmallRange copied.mem q.point 120 := by
    simpa only [Pointer.add_zero] using smallRange_add hpc (k := 0) (count := 120) (by decide)
  have hs := cofactor_allocationShape q.cofactor q.point copied middle hwc hcc hp120 hm
  have hmEq := returnedState_eq_of_call hm
    (SmallOrder.Execution.cofactor_call_three q.cofactor q.point copied hwc hcc hp120)
  have hf : OutputFrame copied middle q.cofactor 160 := by
    rw [hmEq]
    exact SmallOrder.Execution.cofactorState_frame copied q.cofactor q.point hwc hcc hp120
  have hid := identity_frame middle q.identity hf.wellFormed (hf.live _ _ hic)
  have heShape := pointEq_allocationShape q.cofactor q.identity _ after returned hid.wellFormed
    (hid.live _ _ (hf.live _ _ hcc)) (hid.live _ _ (hf.live _ _ hic)) he
  exact (AllocationShape.optionCopies before _ _ _ _).trans
    (hs.trans ((AllocationShape.identityStores middle q.identity).trans heShape))

theorem scalarTrace_allocationShape (p : Primitives) (signature scratch : Pointer)
    (before after : GlobalState)
    (hblack : p.blackBoxByte = Encoding.Decompress.Execution.BlackBox.program.call)
    (hscalar : p.scalarReduce = ScalarReduce32.Execution.program.call)
    (hequality : p.bytesConstantTimeEq = (Encoding.Decompress.Execution.BytesEq.program
      Encoding.Decompress.Execution.bytesEqPrimitives).call)
    (hwf : before.WF) (hsig : SmallRange before.mem signature 64)
    (hout : SmallRange before.mem scratch 32)
    (ht : ScalarCallTrace p signature scratch before after) : AllocationShape before after := by
  obtain ⟨first, reduced, equal, equalValue, hbf, hr, he, hbl⟩ := ht
  rw [hblack] at hbf hbl
  rw [hscalar] at hr
  rw [hequality] at he
  have hfirst := returnedState_eq_of_call hbf
    (Encoding.Decompress.Execution.BlackBox.program_call _ before hwf)
  subst first
  let bits := before.mem.readAt (signature.add 32#64) 256
  have hi : SmallRange before.mem (signature.add 32#64) 32 :=
    smallRange_add hsig (k := 32) (count := 32) (by decide)
  have hred := returnedState_eq_of_call hr (ScalarReduce32.Execution.call scratch (signature.add 32#64)
    {before with alloc := ⟨before.alloc.nextFreeBlock + 1⟩} bits hwf.add_blocks hout ⟨hi, rfl⟩)
  subst reduced
  have hf := ScalarReduce32.Execution.resultState_frame
    {before with alloc := ⟨before.alloc.nextFreeBlock + 1⟩} scratch
    (reduceScalarBytes bits) 34 hwf.add_blocks hout
  have heq := returnedState_eq_of_call he (Encoding.Decompress.Execution.BytesEq.program_exact
    (signature.add 32#64) scratch _ hf.wellFormed (hf.live _ _ hi) (hf.live _ _ hout))
  subst equal
  have hlast := returnedState_eq_of_call hbl
    (Encoding.Decompress.Execution.BlackBox.program_call _ _ hf.wellFormed.add_blocks)
  subst after
  intro id
  simp only [ScalarReduce32.Execution.resultState, ScalarReduce32.Execution.storeBytes,
    SerialPoint.Execution.storeAt_allocationShape]

end Agave.Ed25519.Verifier.Execution.Dalek
