import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixPoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixSignReadback

/-! Whole original success prefix and derived readiness for the checked output
suffix, with the actual black-box and multiplication calls included. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000

def successByte (q : GlobalState) (input : Pointer) : BitVec 8 :=
  q.mem.readAt (input.add 31#64) 8

noncomputable def successSignedEnv (g : Globals) (s t q : GlobalState)
    (out input : Pointer) : Env program.Γ :=
  signAllSelectedEnv (signEnv g s t out input (successByte q input))
    (slot9 s) (successByte q input) (readLimbs q (slot9 s))

def successSignedState (s q : GlobalState) (input : Pointer) : GlobalState :=
  signedState (signState q) (slot9 s) (successByte q input)

noncomputable def successPrefixEnv (g : Globals) (s t q : GlobalState)
    (out input : Pointer) : Env program.Γ := pointEnv (successSignedEnv g s t q out input) (slot6 s)

def successPrefixState (s q : GlobalState) (input : Pointer) : GlobalState :=
  pointTState (successSignedState s q input) (slot6 s) (slot9 s) (slot8 s)

theorem success_point_registers (g : Globals) (s t q : GlobalState) (out input : Pointer) :
    PointRegisters (successSignedEnv g s t q out input) (slot6 s) (slot9 s) (slot8 s) := by
  constructor <;> rfl

theorem success_signed_live (s q : GlobalState) (input p : Pointer)
    (h : SmallRange q.mem p n) : SmallRange (successSignedState s q input).mem p n :=
  signed_live (signState q) (slot9 s) p _ h

theorem sign_state_wf (q : GlobalState) (hwf : q.WF) : (signState q).WF :=
  hwf.add_blocks

theorem success_signed_wf (s q : GlobalState) (input : Pointer) (hwf : q.WF) :
    (successSignedState s q input).WF :=
  (sign_state_wf q hwf).storeAt.storeAt.storeAt

theorem success_prefix_segment (g : Globals) (sg : SqrtRatio.Globals)
    (s t q : GlobalState) (out input : Pointer) (hwf : q.WF)
    (hin : SmallRange q.mem input 32) (h6 : SmallRange q.mem (slot6 s) 160)
    (h8 : SmallRange q.mem (slot8 s) 40) (h9 : SmallRange q.mem (slot9 s) 40) :
    outerSuccessPrefix (decodePrimitives sg) g (successEntryEnv g s t out input) q =
      .value (successPrefixEnv g s t q out input, successPrefixState s q input) := by
  unfold outerSuccessPrefix
  rw [show 50 = 9 + 41 from rfl,segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,
    sign_entry_segment g sg s t q out input hwf hin,PoisonOr.value_bind]
  rw [show 41 = 38 + 3 from rfl,segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,
    sign_network_segment (decodePrimitives sg) g (signEnv g s t out input (q.mem.readAt (input.add 31#64) 8))
      (signState q) (slot9 s) (q.mem.readAt (input.add 31#64) 8) h9
      (sign_registers g s t out input (q.mem.readAt (input.add 31#64) 8)),PoisonOr.value_bind]
  exact point_segment g sg (successSignedEnv g s t q out input)
    (successSignedState s q input) (slot6 s) (slot9 s) (slot8 s)
    (success_signed_wf s q input hwf)
    (success_signed_live s q input _ h6) (success_signed_live s q input _ h9)
    (success_signed_live s q input _ h8)
    (by intro h; have := congrArg BlockId.id h; simp only [slot6_id,slot9_id] at this; omega)
    (success_point_registers g s t q out input)

theorem success_prefix_live (s q : GlobalState) (input p : Pointer)
    (h : SmallRange q.mem p n) : SmallRange (successPrefixState s q input).mem p n :=
  smallRange_storeLimbs ((success_signed_live s q input p h).storeAt _ _) _ _

theorem success_prefix_frame (s q : GlobalState) (input : Pointer)
    (frame : PrivateFrame s q) : PrivateFrame s (successPrefixState s q input) := by
  have hf : PrivateFrame s (signState q) := frame.advance 1
  have hs : PrivateFrame s (successSignedState s q input) :=
    ((hf.storeAt _ _ (by simp only [Pointer.add_id,slot9_id]; omega)).storeAt _ _
      (by simp only [slot9_id]; omega)).storeAt _ _
      (by simp only [Pointer.add_id,slot9_id]; omega)
  exact (hs.storeAt _ _ (by simp only [slot6_id]; omega)).storeLimbs _ _
    (by simp only [Pointer.add_id,slot6_id]; omega)

theorem success_prefix_ready (g : Globals) (s t q : GlobalState)
    (out input : Pointer) (hwf : s.WF) (hout : SmallRange s.mem out 168)
    (frame : PrivateFrame s q) (h6 : SmallRange q.mem (slot6 s) 160)
    (h8 : SmallRange q.mem (slot8 s) 40) :
    OuterSuccessReady (successPrefixEnv g s t q out input) (successPrefixState s q input)
      out ⟨slot6 s,slot8 s⟩ := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    success_prefix_live s q input _ h6, success_prefix_live s q input _ h8,
    success_prefix_live s q input _ (private_live frame hwf hout), ?_, ?_⟩
  · left; intro h
    have := congrArg BlockId.id h
    simp only [Range.of,Pointer.add_id,slot6_id,slot8_id] at this
    omega
  · left; intro h
    have hold := hwf.lt hout.fits.mem
    have := congrArg BlockId.id h
    simp only [Range.of,Pointer.add_id,slot6_id] at this
    omega

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
