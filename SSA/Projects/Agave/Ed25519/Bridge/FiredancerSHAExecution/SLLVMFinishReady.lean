import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishDigest

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open FinishExecution FinishDigest
namespace FinishCorrect
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure Ready (s : GlobalState) (p o kp : Pointer) : Prop where
  wf : s.WF
  contextRange : Core.SmallRange s.mem p 224
  outputRange : Core.SmallRange s.mem o 64
  constantsRange : Core.SmallRange s.mem kp 640
  constantsPtr : GlobalPtr s "fd_sha512_core_ref.K" kp
  constantsValue : Core.readBits s.mem kp 5120 = constantsBytes
  constantsSeparate : p.id ≠ kp.id
  outputSeparate : o.id ≠ p.id

theorem Ready.store {s : GlobalState} {p o kp : Pointer} (h : Ready s p o kp)
    (off : BitVec 64) (x : BitVec w) :
    Ready {s with mem := s.mem.splice (p.withOffset off) x} p o kp := by
  refine ⟨h.wf.splice, h.contextRange.splice _ _, h.outputRange.splice _ _,
    h.constantsRange.splice _ _, h.constantsPtr, ?_, h.constantsSeparate, h.outputSeparate⟩
  rw [Core.readBits_splice_ne x (show (p.withOffset off).id ≠ kp.id from h.constantsSeparate)]
  exact h.constantsValue

theorem Ready.marker {s : GlobalState} {p o kp : Pointer} (h : Ready s p o kp) (used : Nat) :
    Ready {s with mem := markerMemory s.mem p used} p o kp := h.store _ _

theorem Ready.long {s : GlobalState} {p o kp : Pointer} (h : Ready s p o kp) (used : Nat) :
    Ready {s with mem := longMemory s.mem p used} p o kp := h.store _ _

theorem Ready.last {s : GlobalState} {p o kp : Pointer} (h : Ready s p o kp)
    (n : Nat) (lo hi : Word) : Ready {s with mem := lastMemory s.mem p n lo hi} p o kp :=
  ((h.store _ _).store _ _).store _ _

theorem Ready.core {s : GlobalState} {p o kp : Pointer} (h : Ready s p o kp) :
    Core.Ready s kp (p.withOffset 128#64) p 1#64 := by
  refine ⟨h.wf, h.contextRange.add (by decide), h.contextRange.mono (by decide),
    h.constantsRange, by decide, h.constantsPtr, h.constantsValue, h.constantsSeparate, ?_⟩
  right; right
  have hoff := h.contextRange.offset_lt
  simp only [Pointer.withOffset, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem Ready.after_core {s after : GlobalState} {p o kp : Pointer}
    (h : Ready s p o kp) (hwf : after.WF) (hg : after.globals = s.globals)
    (he : ∀ b, after.mem.live? b = (s.mem.splice (p.withOffset 128#64)
      (Core.result s (p.withOffset 128#64) p 1#64)).live? b) : Ready after p o kp := by
  refine ⟨hwf, (h.contextRange.splice _ _).of_live_eq (he _),
    (h.outputRange.splice _ _).of_live_eq (he _),
    (h.constantsRange.splice _ _).of_live_eq (he _), ?_, ?_, h.constantsSeparate, h.outputSeparate⟩
  · simpa only [GlobalPtr, hg] using h.constantsPtr
  · rw [Core.readBits_of_live_eq (he _), Core.readBits_splice_ne _
      (show (p.withOffset 128#64).id ≠ kp.id from h.constantsSeparate)]
    exact h.constantsValue

end FinishCorrect
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
