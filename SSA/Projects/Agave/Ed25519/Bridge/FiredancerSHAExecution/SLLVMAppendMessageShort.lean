import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendShort

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


def appendMessageShortMemory (m : MemoryState) (p data : Pointer) (n : BitVec 64) : MemoryState :=
  let lo := sourceRead m (p.withOffset 208#64) 64
  let hi := sourceRead m (p.withOffset 216#64) 64
  let nextLo := lo + (n <<< 3)
  let nextHi := (hi + (n >>> 61)) + (if nextLo <ᵤ lo then 1#64 else 0#64)
  let m := (m.splice (p.withOffset 208#64) nextLo).splice (p.withOffset 216#64) nextHi
  let m := m.splice (p.withOffset 64#64) (sourceRead m data (8 * n.toNat))
  m.splice (p.withOffset 200#64) (64#64 + n)

/-- Actual third-call execution when the message fits in the remaining buffer. -/
theorem append_message_short_body (p data : Pointer) (s : GlobalState) (n : BitVec 64)
    (hn : 0 < n.toNat) (hn64 : n.toNat < 64)
    (hr : Fits s.mem p (224 * 8)) (hd : Fits s.mem data (8 * n.toNat))
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    StateT.run (append.denote
      (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ)) s =
      .value ([.value p]ₕ, {s with mem := appendMessageShortMemory s.mem p data n}) := by
  have hnzero : (n == 0#64) = false := by simp [beq_eq_false_iff_ne]; intro h; subst n; simp at hn
  have hnlt : (n <ᵤ 64#64) = true := by simpa [BitVec.ult] using hn64
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
  have h28 : v28 = .value (1#1) := by
    simp only [hv28, h27, simp_sllvm, hnlt]
  subst h27 h28
  have hp2 : Fits s2.mem p (224 * 8) := fits_splice (fits_splice hr)
  peel_gep 64 with p, hp2, s2 as dst
  simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm]
  denote_enter_block
  simp (config := {failIfUnchanged := false}) only [Target.denote, simp_spine,
    show (1#1 : BitVec 1) = 1 by decide, ↓reduceIte]
  have hd2 : Fits s2.mem data (8 * n.toNat) := fits_splice (fits_splice hd)
  have hdst2 : Fits s2.mem dst (8 * n.toNat) := Fits.mono hdst (by omega)
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' :=
    {s2 with mem := s2.mem.splice dst (hd2.choose.bytes.extractLsb' data.offsetInBits (8 * n.toNat))})
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      change (fun x : Unit × GlobalState => ((HVector.nil : HVector toType ([] : List SLLVM.Ty)), x.2)) <$>
        StateT.run (liftM (memcpy (.value dst) (.value data) (.value n)) : EffectM Unit) s2 = _
      rw [run_liftM (run_memcpy (len := n) hd2.choose_spec.1 hd2.choose_spec.2 hdst2)]
      rfl)]
  let copied := s2.mem.splice dst (hd2.choose.bytes.extractLsb' data.offsetInBits (8 * n.toNat))
  let s3 : GlobalState := {s2 with mem := copied}
  denote_number_from 30
  denote_step_reduce v 30 [LLVM.add, LLVM.add?]
  have h30 : v30 = .value (64#64 + n) := by simpa only [simp_sllvm] using hv30
  subst h30
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  denote_enter_block
  simp (config := {failIfUnchanged := false}) only [Target.denote, simp_spine,
    show (1#1 : BitVec 1) = 1 by decide, ↓reduceIte]
  have hu3 : Fits s3.mem used 64 := Fits.mono
    (fits_splice (fits_splice (fits_splice hused))) (by decide)
  reduce_cfg_indices
  rw [BlockCom.run_bind_denote_var_of_nil (s' := {s3 with mem := s3.mem.splice used (64#64 + n)})
    (by
      simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
      change (fun x : Unit × GlobalState => ((HVector.nil : HVector toType ([] : List SLLVM.Ty)), x.2)) <$>
        StateT.run (liftM (store (.value used) (.bitvec (.concrete 64)) (.value (64#64 + n))) : EffectM Unit) s3 = _
      rw [run_liftM (run_store (t := .bitvec (.concrete 64))
        (x := PoisonOr.value (64#64 + n)) rfl hu3)]
      rfl)]
  simp only [BlockCom.denote_term]
  rw [Terminator.denote_condBr_value (b := 1#1) (by rfl)]
  simp only [simp_denote, simp_sllvm]
  denote_enter_block
  simp_return
  have hdread : sourceRead s2.mem data (8 * n.toNat) = hd2.choose.bytes.extractLsb' data.offsetInBits (8 * n.toNat) := by
    have hb : s2.mem.live? data.id = some hd2.choose := by
      exact congrArg (fun x : Option Block => match x with
        | some (.live v) => some v | _ => none) hd2.choose_spec.1
    simp only [sourceRead, hb]
  constructor
  · rfl
  constructor
  · simp only [s3, copied, appendMessageShortMemory, s2, s1, low, high, used, dst, nextLo, nextHi, lo, hi] at hdread ⊢
    congr 2
    exact hdread.symm
  · rfl


attribute [local irreducible] append appendMessageShortMemory

theorem append_message_short_call (p data : Pointer) (s : GlobalState) (n : BitVec 64)
    (hn : 0 < n.toNat) (hn64 : n.toNat < 64)
    (hr : Fits s.mem p (224 * 8)) (hd : Fits s.mem data (8 * n.toNat))
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    StateT.run (runFunction (append.denote
      (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ))) s =
      .value ([.value p]ₕ, s.popFrame (appendMessageShortMemory s.mem p data n)) :=
  run_runFunction (append_message_short_body p data s n hn hn64 hr hd hcount)

theorem appendMessageShortMemory_other (m : MemoryState) (p data : Pointer)
    (n : BitVec 64) (q : BlockId) (hne : q ≠ p.id) :
    (appendMessageShortMemory m p data n).live? q = m.live? q := by
  simp only [appendMessageShortMemory, live?_splice_ne (Ne.symm hne : p.id ≠ q),
    live?_splice_ne (show (p.withOffset _).id ≠ q from Ne.symm hne)]

theorem append_message_short_frame (p data : Pointer) (s : GlobalState) (n : BitVec 64)
    (hwf : s.WF) (hn : 0 < n.toNat) (hn64 : n.toNat < 64)
    (hr : Fits s.mem p (224 * 8)) (hd : Fits s.mem data (8 * n.toNat))
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      after.WF ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ q, q ≠ p.id → after.mem.live? q = s.mem.live? q) ∧
      after.mem.live? p.id = (appendMessageShortMemory s.mem p data n).live? p.id := by
  refine ⟨s.popFrame (appendMessageShortMemory s.mem p data n),
    append_message_short_call p data s n hn hn64 hr hd hcount, ?_, rfl, rfl, ?_, ?_⟩
  · intro q hq
    exact live?_killFrom_of_le hq
  · intro q hq
    change ((appendMessageShortMemory s.mem p data n).killFrom s.alloc.nextFreeBlock).live? q = _
    by_cases hlt : q.id < s.alloc.nextFreeBlock
    · rw [live?_killFrom_of_lt hlt, appendMessageShortMemory_other _ _ _ _ _ hq]
    · rw [live?_killFrom_of_le (by omega), hwf q (by omega)]
  · exact live?_killFrom_of_lt (lt_nextFreeBlock_of_fits hwf hr)

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
