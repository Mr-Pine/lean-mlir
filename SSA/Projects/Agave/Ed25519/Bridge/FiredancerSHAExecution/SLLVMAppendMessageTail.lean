import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageFill
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Arithmetic

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] core
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] Fits

private theorem fits_bound {m : MemoryState} {p : Pointer} {n : Nat} {b : LiveBlock}
    (h : Fits m p n) (hb : m[p.id]? = some (.live b)) :
    p.offsetInBits + n ≤ b.lengthInBits := by
  obtain ⟨b', hb', hn⟩ := h
  have : b' = b := Block.live.inj (Option.some.inj (hb'.symm.trans hb))
  exact this ▸ hn


def appendMessageTailMemory (m : MemoryState) (p rest : Pointer) (tail : BitVec 64) : MemoryState :=
  let m := m.splice (p.withOffset 200#64) (0#64)
  let m := m.splice p (sourceRead m rest (8 * tail.toNat))
  m.splice (p.withOffset 200#64) tail

/-- A message that fills the buffered block and leaves fewer than 128 bytes
executes one real core call, then copies the trailing message bytes. -/
theorem append_message_fill_tail_body (p data : Pointer) (s after : GlobalState) (n : BitVec 64)
    (hn : 64 < n.toNat) (hn192 : n.toNat < 192)
    (hr : Fits s.mem p (224 * 8)) (hd : Fits s.mem data (8 * n.toNat))
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64)
    (ha : Fits after.mem p (224 * 8))
    (hafterRest : Fits after.mem (data.withOffset 64#64) (8 * (n - 64#64).toNat))
    (hcore : StateT.run (runFunction (core.denote
        (Ctxt.Valuation.ofHVector [.value (1#64), .value p, .value (p.withOffset 128#64)]ₕ)))
      {s with mem := appendMessageFilledMemory s.mem p data n} =
        .value (.nil, after)) :
    StateT.run (append.denote
      (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ)) s =
      .value ([.value p]ₕ, {after with mem := appendMessageTailMemory after.mem p (data.withOffset 64#64) (n - 64#64)})  := by
  have hnzero : (n == 0#64) = false := by simp [beq_eq_false_iff_ne]; intro h; subst n; simp at hn
  have hnlt : (n <ᵤ 64#64) = false := by simp [BitVec.ult]; omega
  have hnsub : n.usubOverflow 64#64 = false := by simp [BitVec.usubOverflow]; omega
  have hremNat : (n - 64#64).toNat = n.toNat - 64 := by
    exact BitVec.toNat_sub_of_le (by change 64 ≤ n.toNat; omega)
  have hremLt : ((n - 64#64) <ᵤ 128#64) = true := by simp [BitVec.ult, hremNat]; omega
  have hrem : (n - 64#64) &&& 127#64 = n - 64#64 := by
    apply BitVec.eq_of_toNat_eq
    exact (append_remainder (n - 64#64)).trans (Nat.mod_eq_of_lt (by rw [hremNat]; omega))
  have hremZero : ((n - 64#64) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    simp only [hremNat, BitVec.toNat_ofNat] at this
    omega
  have hoff : (n - 64#64) &&& 18446744073709551488#64 = 0#64 := by
    rw [show (18446744073709551488#64) = (-128 : BitVec 64) by decide, append_aligned_mask]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [hremNat]
    norm_num <;> omega
  simp only [Cfg.denote]
  denote_expose
  denote_step_reduce v 11 [LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10
  simp only [hv11, BlockCom.denote_term, Terminator.denote_condBr,
    simp_denote, simp_sllvm,
    hnzero, show (64#64 == 0#64) = false by decide,
    show (64#64 <ᵤ 128#64) = true by decide,
    show (64#64 &&& 127#64) = 64#64 by decide,
    BitVec.ofBool_true, BitVec.ofBool_false,
    show (0 : BitVec 1) ≠ 1 by decide, show (1 : BitVec 1) = 1 from rfl,
    ite_false, ite_true]
  denote_enter_block
  simp (config := {failIfUnchanged := false}) only [Target.denote, simp_spine, Ctxt.Valuation.cons_last, show (0 : BitVec 1) ≠ 1 by decide, show (0#1 : BitVec 1) ≠ 1 by decide, show (1#1 : BitVec 1) = 1 by decide, ite_eq_right, ite_eq_left, ↓reduceIte]
  obtain ⟨blk, hblk, hlen⟩ := hr
  have hr : Fits s.mem p (224 * 8) := ⟨blk, hblk, hlen⟩
  peel_gep 128 with p, hr, s as chain
  peel_gep 200 with p, hr, s as used
  have hcblk : s.mem[used.id]? = some (.live blk) := hblk
  have hclen : used.offsetInBits + 192 ≤ blk.lengthInBits := fits_bound hused hcblk
  peel_load (.bitvec (.concrete 64)), blk, used, hcblk, s
  peel_gep 208 with p, hr, s as low
  have hlblk : s.mem[low.id]? = some (.live blk) := hblk
  have hllen : low.offsetInBits + 128 ≤ blk.lengthInBits := fits_bound hlow hlblk
  peel_load (.bitvec (.concrete 64)), blk, low, hlblk, s
  peel_gep 216 with p, hr, s as high
  have hhblk : s.mem[high.id]? = some (.live blk) := hblk
  have hhlen : high.offsetInBits + 64 ≤ blk.lengthInBits := fits_bound hhigh hhblk
  peel_load (.bitvec (.concrete 64)), blk, high, hhblk, s
  denote_number_from 19
  denote_step_reduce v 25 [LLVM.shl, LLVM.shl?, LLVM.add, LLVM.add?, LLVM.lshr, LLVM.lshr?,
    LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.zext, LLVM.zext?]
  have hlive : s.mem.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  have hl : sourceRead s.mem low 64 = blk.bytes.extractLsb' low.offsetInBits 64 := by
    simp only [sourceRead, show low.id = p.id from rfl, hlive]
  have hh : sourceRead s.mem high 64 = blk.bytes.extractLsb' high.offsetInBits 64 := by
    simp only [sourceRead, show high.id = p.id from rfl, hlive]
  let lo := sourceRead s.mem low 64
  let hi := sourceRead s.mem high 64
  let nextLo := lo + (n <<< 3)
  let nextHi := (hi + (n >>> 61)) + (if nextLo <ᵤ lo then 1#64 else 0#64)
  have h20 : v20 = .value nextLo := by simp [hv20, hv19, nextLo, lo, hl]
  have h25 : v25 = .value nextHi := by
    simp only [hv25, hv22, hv21, hv24, hv23, h20, simp_sllvm]
    have hext (b : Bool) : (BitVec.ofBool b).setWidth 64 = (if b then 1#64 else 0#64) := by
      cases b <;> rfl
    simp only [nextHi, nextLo, lo, hi, hl, hh, BitVec.add_zero, hext]
    rfl
  subst h20 h25
  peel_store nextLo, low, hlow, s
  let s1 : GlobalState := {s with mem := s.mem.splice low nextLo}
  have hfhi : Fits s1.mem high 64 := fits_splice hhigh
  peel_store nextHi, high, hfhi, s1
  let s2 : GlobalState := {s1 with mem := s1.mem.splice high nextHi}
  denote_number_from 26
  denote_step_reduce v 26 [LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  have hc : blk.bytes.extractLsb' used.offsetInBits 64 = 64#64 := by
    have hh : sourceRead s.mem used 64 = blk.bytes.extractLsb' used.offsetInBits 64 := by
      simp only [sourceRead, show used.id = p.id from rfl, hlive]
    rw [← hh]
    exact hcount
  simp only [hv26, hc, BlockCom.denote_term, Terminator.denote_condBr,
    simp_denote, simp_sllvm,
    hnzero, show (64#64 == 0#64) = false by decide,
    show (64#64 <ᵤ 128#64) = true by decide,
    show (64#64 &&& 127#64) = 64#64 by decide,
    BitVec.ofBool_true, BitVec.ofBool_false,
    show (0 : BitVec 1) ≠ 1 by decide, show (1 : BitVec 1) = 1 from rfl,
    ite_false, ite_true]
  denote_enter_block
  simp (config := {failIfUnchanged := false}) only [Target.denote, simp_spine, Ctxt.Valuation.cons_last, show (0 : BitVec 1) ≠ 1 by decide, show (0#1 : BitVec 1) ≠ 1 by decide, show (1#1 : BitVec 1) = 1 by decide, ite_eq_right, ite_eq_left, ↓reduceIte]
  denote_number_from 27
  denote_step_reduce v 28 [LLVM.sub, LLVM.sub?, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  have h27 : v27 = .value (64#64) := by simpa only [simp_sllvm] using hv27
  have h28 : v28 = .value (0#1) := by
    simp only [hv28, h27, simp_sllvm, hnlt]
    rfl
  subst h27 h28
  have hp2 : Fits s2.mem p (224 * 8) := fits_splice (fits_splice hr)
  peel_gep 64 with p, hp2, s2 as dst
  simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm]
  denote_enter_block
  simp (config := {failIfUnchanged := false}) only [Target.denote, simp_spine,
    Ctxt.Valuation.cons_last, show (0#1 : BitVec 1) ≠ 1 by decide, show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  have hd2full : Fits s2.mem data (8 * n.toNat) := fits_splice (fits_splice hd)
  have hd2 : Fits s2.mem data 512 := Fits.mono hd2full (by omega)
  have hdst2 : Fits s2.mem dst 512 := Fits.mono hdst (by decide)
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' :=
    {s2 with mem := s2.mem.splice dst (hd2.choose.bytes.extractLsb' data.offsetInBits 512)})
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      change (fun x : Unit × GlobalState => ((HVector.nil : HVector toType ([] : List SLLVM.Ty)), x.2)) <$>
        StateT.run (liftM (memcpy (.value dst) (.value data) (.value (64#64))) : EffectM Unit) s2 = _
      rw [run_liftM (run_memcpy (len := 64#64) hd2.choose_spec.1 hd2.choose_spec.2 hdst2)]
      rfl)]
  let s3 : GlobalState := {s2 with mem := s2.mem.splice dst (hd2.choose.bytes.extractLsb' data.offsetInBits 512)}
  have hd3 : Fits s3.mem data 512 := fits_splice hd2
  denote_number_from 31
  peel_gep 64 with data, hd3, s3 as rest
  denote_step_reduce v 32 [LLVM.sub, LLVM.sub?]
  have h32 : v32 = .value (n - 64#64) := by simpa only [simp_sllvm, hnsub, Bool.false_eq_true, ite_false] using hv32
  subst h32
  have hdread : sourceRead s2.mem data 512 = hd2.choose.bytes.extractLsb' data.offsetInBits 512 := by
    have hb : s2.mem.live? data.id = some hd2.choose := by
      exact congrArg (fun x : Option Block => match x with
        | some (.live v) => some v | _ => none) hd2.choose_spec.1
    simp only [sourceRead, hb]
  have hs3 : s3 = {s with mem := appendMessageFilledMemory s.mem p data n} := by
    simp only [s3, appendMessageFilledMemory, s2, s1, low, high, dst, nextLo, nextHi, lo, hi] at hdread ⊢
    congr 2
    exact hdread.symm
  change StateT.run _ s3 = _
  rw [hs3]
  peel_call hcore with chain
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  denote_enter_block
  simp (config := {failIfUnchanged := false}) only [Target.denote, simp_spine,
    Ctxt.Valuation.cons_last, show (0#1 : BitVec 1) ≠ 1 by decide, show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  have hua : Fits after.mem used 64 := by
    exact Fits.mono (remainingFits after.mem p ha (200#64) (by decide)) (by decide)
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := {after with mem := after.mem.splice used (0#64)})
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      change (fun x : Unit × GlobalState => ((HVector.nil : HVector toType ([] : List SLLVM.Ty)), x.2)) <$>
        StateT.run (liftM (store (.value used) (.bitvec (.concrete 64)) (.value (0#64))) : EffectM Unit) after = _
      rw [run_liftM (run_store (t := .bitvec (.concrete 64)) (x := PoisonOr.value (0#64)) rfl hua)]
      rfl)]
  simp only [BlockCom.denote_term]
  rw [Terminator.denote_condBr_value (b := 0#1) (by rfl)]
  simp only [simp_denote, simp_sllvm]
  denote_enter_block
  simp (config := {failIfUnchanged := false}) only [Target.denote, simp_spine,
    Ctxt.Valuation.cons_last, show (0#1 : BitVec 1) ≠ 1 by decide, show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  denote_number_from 38
  denote_step_reduce v 38 [LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  simp only [hv38, hremLt, BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm]
  denote_enter_block
  simp (config := {failIfUnchanged := false}) only [Target.denote, simp_spine,
    Ctxt.Valuation.cons_last, show (1#1 : BitVec 1) = 1 by decide, ↓reduceIte]
  denote_number_from 40
  denote_step_reduce v 41 [LLVM.and, LLVM.and?, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  simp only [hv41, hv40, hrem, hremZero, BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm]
  denote_enter_block
  simp (config := {failIfUnchanged := false}) only [Target.denote, simp_spine,
    Ctxt.Valuation.cons_last, show (0 : BitVec 1) ≠ 1 by decide,
    show (0#1 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  denote_number_from 42
  denote_step_reduce v 42 [LLVM.and, LLVM.and?]
  have h42 : v42 = .value (0#64) := by simpa only [simp_sllvm, hoff] using hv42
  subst h42
  let s4 : GlobalState := {after with mem := after.mem.splice used (0#64)}
  have hr4 : Fits s4.mem rest (8 * (n - 64#64).toNat) := fits_splice hafterRest
  peel_gep 0 with rest, hr4, s4 as src
  have hsrcEq : src = rest := by simp [src, Pointer.withOffset]
  subst src
  simp only [hsrcEq]
  have hp4 : Fits s4.mem p (8 * (n - 64#64).toNat) :=
    Fits.mono (fits_splice ha) (by rw [hremNat]; omega)
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' :=
    {s4 with mem := s4.mem.splice p (hr4.choose.bytes.extractLsb' rest.offsetInBits (8 * (n - 64#64).toNat))})
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      change (fun x : Unit × GlobalState => ((HVector.nil : HVector toType ([] : List SLLVM.Ty)), x.2)) <$>
        StateT.run (liftM (memcpy (.value p) (.value rest) (.value (n - 64#64))) : EffectM Unit) s4 = _
      rw [run_liftM (run_memcpy (len := n - 64#64) hr4.choose_spec.1 hr4.choose_spec.2 hp4)]
      rfl)]
  let s5 : GlobalState := {s4 with mem := s4.mem.splice p (hr4.choose.bytes.extractLsb' rest.offsetInBits (8 * (n - 64#64).toNat))}
  have hu5 : Fits s5.mem used 64 := fits_splice (fits_splice hua)
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := {s5 with mem := s5.mem.splice used (n - 64#64)})
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      change (fun x : Unit × GlobalState => ((HVector.nil : HVector toType ([] : List SLLVM.Ty)), x.2)) <$>
        StateT.run (liftM (store (.value used) (.bitvec (.concrete 64)) (.value (n - 64#64))) : EffectM Unit) s5 = _
      rw [run_liftM (run_store (t := .bitvec (.concrete 64)) (x := PoisonOr.value (n - 64#64)) rfl hu5)]
      rfl)]
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  denote_enter_block
  simp_return
  have hdread4 : sourceRead s4.mem rest (8 * (n - 64#64).toNat) =
      hr4.choose.bytes.extractLsb' rest.offsetInBits (8 * (n - 64#64).toNat) := by
    have hb : s4.mem.live? rest.id = some hr4.choose := by
      exact congrArg (fun x : Option Block => match x with
        | some (.live v) => some v | _ => none) hr4.choose_spec.1
    simp only [sourceRead, hb]
  constructor
  · rfl
  constructor
  · simp only [s5, s4, used, rest, appendMessageTailMemory] at hdread4 ⊢
    congr 2
    exact hdread4.symm
  · rfl

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
