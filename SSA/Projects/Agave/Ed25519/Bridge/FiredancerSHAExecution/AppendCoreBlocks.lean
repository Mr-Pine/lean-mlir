import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendBlocks

/-! The two actual compression-call sites and the trailing copy. The local
hypotheses identify only the callee call, not an append execution conclusion. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem word_gep_index (x : Word) (h : x.toNat < 2^63) :
    Operation.gepInboundsIndex 1 (.value x) = .value (x.toNat : Int) := by
  have hi : x.toInt = (x.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hsmall : x.toNat < 9223372036854775808 := h
  have h64 : x.toNat < 18446744073709551616 := x.isLt
  have hint : (x.toNat : Int) % 18446744073709551616 < 18446744073709551616 :=
    Int.emod_lt_of_pos _ (by decide)
  simp [Operation.gepInboundsIndex, Operation.GepSignedRange, hi, hsmall, h64, hint]

theorem word_gep (m : MemoryState) (p : Pointer) (n : Nat) (x : Word)
    (hr : SmallRange m p n) (hx : x.toNat ≤ n) :
    Operation.gepInboundsLive m (.value p) [.value (x.toNat : Int)] =
      .value (p.add x) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr.gep hx

def filledEnv (E : Env program.Γ) (data : Pointer) (used size : Word) : Env program.Γ :=
  E[%31 := .value (data.add (128#64 - used)), %32 := .value (size - (128#64 - used))]

theorem fill_body (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (E : Env program.Γ) (s after : GlobalState) (context data : Pointer)
    (used size : Word) (h : CommonReady E context)
    (hd : E.read (%arg1) = .value data) (hs : E.read (%arg2) = .value size)
    (hp : E.read (%29) = .value (context.add used))
    (hf : E.read (%27) = .value (128#64 - used))
    (hc : SmallRange s.mem context 224) (hi : SmallRange s.mem data size.toNat)
    (hu : used.toNat < 128) (hl : (128#64 - used).toNat ≤ size.toNat)
    (hne : context.id ≠ data.id)
    (hcall : core (.cons (.value (context.add 128#64)) (.cons (.value context)
      (.cons (.value 1#64) .nil)))
      {s with mem := copyMemory s.mem (context.add used) data (128#64 - used)} =
        .value (.nil, after)) :
    List.foldlM Instr.run E (program.bb4 core).body s =
      .value (filledEnv E data used size, after) := by
  have hcarg : E.args 0 = .value context := h.argContext
  change E.args 1 = .value data at hd
  change E.args 2 = .value size at hs
  have hfill : (128#64 - used).toNat = 128 - used.toNat := by
    exact BitVec.toNat_sub_of_le (by change used.toNat ≤ 128; omega)
  have hfcopy := hc.fits_add (k := used.toNat) (count := (128#64 - used).toNat) (by omega)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hfcopy
  have hsrc := (smallRange_mono hi hl).fits
  have hdis : (Range.of (context.add used) (8 * (128#64 - used).toNat)).Disjoint
      (Range.of data (8 * (128#64 - used).toNat)) := Or.inl hne
  have hindex := word_gep_index (128#64 - used) (by omega)
  have hg := word_gep _ _ _ (128#64 - used)
    (hi.storeAt (context.add used) (s.mem.readAt data (8 * (128#64 - used).toNat))) hl
  have hsub : Operation.sub {nuw := true} (.value size) (.value (128#64 - used)) =
      .value (size - (128#64 - used)) := by
    have hov : size.usubOverflow (128#64 - used) = false := by
      simp only [BitVec.usubOverflow, decide_eq_false_iff_not]; omega
    simp [Operation.sub, hov]
  simp only [copyMemory] at hcall
  simp at hfcopy hsrc hdis hg hcall hindex
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run, filledEnv,
    hcarg, hd, hs, hp, hf, h.chain, h.one, Operation.memcpy,
    hfcopy, hsrc, hdis, hindex, hg, hsub, hcall,
    GepIndex.inboundsOffset, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]


theorem bulk_body (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (E : Env program.Γ) (s after : GlobalState) (context data : Pointer)
    (size : Word) (h : CommonReady E context)
    (hd : E.read (%36) = .value data) (hs : E.read (%37) = .value size)
    (hcall : core (.cons (.value (context.add 128#64)) (.cons (.value data)
      (.cons (.value (size >>> 7)) .nil))) s = .value (.nil, after)) :
    List.foldlM Instr.run E (program.bb7 core).body s =
      .value (E[%39 := .value (size >>> 7)], after) := by
  simp [program.bb7, List.foldlM_cons, List.foldlM_nil, Instr.run,
    hd, hs, h.chain, h.shift, Operation.lshr, hcall, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]


def tailMemory (m : MemoryState) (context data : Pointer) (size : Word) : MemoryState :=
  countMemory (copyMemory m context (data.add (size &&& 18446744073709551488#64)) (size &&& 127#64))
    context (size &&& 127#64)

def tailEnv (E : Env program.Γ) (data : Pointer) (size : Word) : Env program.Γ :=
  E[%42 := .value (size &&& 18446744073709551488#64),
    %43 := .value (data.add (size &&& 18446744073709551488#64))]

theorem aligned_le (size : Word) : (size &&& 18446744073709551488#64).toNat ≤ size.toNat := by
  exact Nat.and_le_left

theorem aligned_plus_remainder (size : Word) :
    (size &&& 18446744073709551488#64).toNat + (size &&& 127#64).toNat = size.toNat := by
  have ha : size &&& 18446744073709551488#64 = ((size >>> 7) <<< 7) := by
    simpa using append_aligned_mask size
  have hr : (size &&& 127#64).toNat = size.toNat % 128 := by
    simpa using append_remainder size
  rw [ha, hr]
  have hn := size.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  norm_num at *
  omega

theorem tail_body (E : Env program.Γ) (s : GlobalState) (context data : Pointer)
    (size : Word) (h : CommonReady E context)
    (hd : E.read (%36) = .value data) (hs : E.read (%37) = .value size)
    (hr : E.read (%40) = .value (size &&& 127#64))
    (hc : SmallRange s.mem context 224) (hi : SmallRange s.mem data size.toNat)
    (hne : context.id ≠ data.id) :
    List.foldlM Instr.run E program.bb9.body s =
      .value (tailEnv E data size, {s with mem := tailMemory s.mem context data size}) := by
  have hcarg : E.args 0 = .value context := h.argContext
  have hoff := aligned_le size
  have hlength := hi.offset_lt
  have hindex := word_gep_index (size &&& 18446744073709551488#64) (by omega)
  have hg := word_gep _ _ _ (size &&& 18446744073709551488#64) hi hoff
  have hrem : (size &&& 127#64).toNat < 128 := by simpa using append_remainder_bound size
  have hfcopy := (smallRange_mono hc (show (size &&& 127#64).toNat ≤ 224 by omega)).fits
  have hsrc := smallRange_add hi (le_of_eq (aligned_plus_remainder size))
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hsrc
  have hdis : (Range.of context (8 * (size &&& 127#64).toNat)).Disjoint
      (Range.of (data.add (size &&& 18446744073709551488#64)) (8 * (size &&& 127#64).toNat)) := Or.inl hne
  have hfcount := (hc.storeAt context
    (s.mem.readAt (data.add (size &&& 18446744073709551488#64)) (8 * (size &&& 127#64).toNat))).fits_add
    (k := 200) (count := 8) (by decide)
  simp at hfcopy hsrc hdis hfcount hg hindex
  simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
    tailEnv, tailMemory, copyMemory, countMemory,
    hcarg, hd, hs, hr, h.high, h.count, Operation.and, Operation.memcpy, Operation.store,
    hfcopy, hsrc.fits, hdis, hfcount, hindex, hg, GepIndex.inboundsOffset, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
