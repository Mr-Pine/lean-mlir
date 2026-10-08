import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageFill
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreMemory
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Arithmetic

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace MessageExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem aligned_plus_remainder (size : BitVec 64) :
    (size &&& 18446744073709551488#64).toNat + (size &&& 127#64).toNat = size.toNat := by
  have ha : size &&& 18446744073709551488#64 = ((size >>> (7 : Nat)) <<< (7 : Nat)) := append_aligned_mask size
  have hr : (size &&& 127#64).toNat = size.toNat % 128 := append_remainder size
  rw [ha, hr]
  have hn := size.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  norm_num at *
  omega

/-- Concrete memory and constants readiness for the third verifier append. -/
structure Ready (s : GlobalState) (p data kp : Pointer) (n : BitVec 64) : Prop where
  wf : s.WF
  contextRange : Core.SmallRange s.mem p 224
  messageRange : Core.SmallRange s.mem data n.toNat
  constantsRange : Core.SmallRange s.mem kp 640
  constantsPtr : GlobalPtr s "fd_sha512_core_ref.K" kp
  constantsValue : Core.readBits s.mem kp 5120 = constantsBytes
  constantsSeparate : p.id ≠ kp.id
  inputSeparate : p.id ≠ data.id

theorem Ready.store {s : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) (off : BitVec 64) (x : BitVec w) :
    Ready {s with mem := s.mem.splice (p.withOffset off) x} p data kp n := by
  refine ⟨h.wf.splice, h.contextRange.splice _ _, h.messageRange.splice _ _,
    h.constantsRange.splice _ _, h.constantsPtr, ?_, h.constantsSeparate, h.inputSeparate⟩
  rw [Core.readBits_of_live_eq (live?_splice_ne (show (p.withOffset off).id ≠ kp.id from h.constantsSeparate))]
  exact h.constantsValue

theorem Ready.filled {s : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) :
    Ready {s with mem := appendMessageFilledMemory s.mem p data n} p data kp n :=
  ((h.store _ _).store _ _).store _ _

theorem Ready.buffered_core {s : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) : Core.Ready s kp (p.withOffset 128#64) p 1#64 := by
  refine ⟨h.wf, h.contextRange.add (by decide), h.contextRange.mono (by decide),
    h.constantsRange, by decide, h.constantsPtr, h.constantsValue, h.constantsSeparate, ?_⟩
  right; right
  have hoff := h.contextRange.offset_lt
  simp only [Pointer.withOffset, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem Ready.after_core {s after : GlobalState} {p data kp src : Pointer} {n count : BitVec 64}
    (h : Ready s p data kp n) (hwf : after.WF) (hg : after.globals = s.globals)
    (he : ∀ b, after.mem.live? b = (s.mem.splice (p.withOffset 128#64)
      (Core.result s (p.withOffset 128#64) src count)).live? b) : Ready after p data kp n := by
  refine ⟨hwf, (h.contextRange.splice _ _).of_live_eq (he _),
    (h.messageRange.splice _ _).of_live_eq (he _),
    (h.constantsRange.splice _ _).of_live_eq (he _), ?_, ?_, h.constantsSeparate, h.inputSeparate⟩
  · simpa only [GlobalPtr, hg] using h.constantsPtr
  · rw [Core.readBits_of_live_eq (he _), Core.readBits_of_live_eq
      (live?_splice_ne (show (p.withOffset 128#64).id ≠ kp.id from h.constantsSeparate))]
    exact h.constantsValue

theorem Ready.rest_range {s : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) (hn : 64 ≤ n.toNat) :
    Core.SmallRange s.mem (data.withOffset 64#64) (n - 64#64).toNat := by
  have hr : (n - 64#64).toNat = n.toNat - 64 := BitVec.toNat_sub_of_le hn
  exact h.messageRange.add (by rw [hr]; omega)

theorem Ready.direct_core {s : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) (hn : 192 ≤ n.toNat) :
    Core.Ready s kp (p.withOffset 128#64) (data.withOffset 64#64) ((n - 64#64) >>> (7 : Nat)) := by
  have hr : (n - 64#64).toNat = n.toNat - 64 := BitVec.toNat_sub_of_le (by change 64 ≤ n.toNat; omega)
  have hq : ((n - 64#64) >>> (7 : Nat)).toNat = (n - 64#64).toNat / 128 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  refine ⟨h.wf, h.contextRange.add (by decide),
    (h.rest_range (by omega)).mono ?_, h.constantsRange, ?_, h.constantsPtr,
    h.constantsValue, h.constantsSeparate, Or.inl h.inputSeparate⟩
  · rw [hq]; omega
  · rw [hq, hr]; omega

theorem Ready.tail_fits {s : GlobalState} {p data kp : Pointer} {n : BitVec 64}
    (h : Ready s p data kp n) (hn : 64 ≤ n.toNat) :
    Fits s.mem ((data.withOffset 64#64).withOffset ((n - 64#64) &&& 18446744073709551488#64))
      (8 * ((n - 64#64) &&& 127#64).toNat) := by
  have hp := aligned_plus_remainder (n - 64#64)
  have hh := (h.rest_range hn).add (le_of_eq hp)
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hh.fits

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
