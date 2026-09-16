/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_validate
import SSA.Projects.Firedancer.Common.Proof.fd_ulong_load_8
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_curve25519_scalar_validate` conforms

Three paths, by the scalar's top byte: below `0x10` return `s`; at or above
`0x20` return `NULL`; in between load the four `ulong`s and compare against
`ℓ`, returning `s` or `NULL` by `select`. Each path's answer is `s < ℓ` by
`bv_decide` over the scalar's 256 bits. Every path only reads, so the state
comes back through four `fd_ulong_load_8` equivalences at most.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

-- reached only through its conformance theorem
attribute [local irreducible] fd_ulong_load_8

/-- `runFunction` peeled off a goal of the spec's shape: the body's own state
`t` becomes the popped frame, equivalent to `s` because `t` is. -/
private theorem wrap {body : EffectM (HVector (@TyDenote.toType SLLVM.Ty _) [SLLVM.Ty.ptr])}
    {s : GlobalState} {r : Pointer} (hs : s.WF)
    (h : ∃ t : GlobalState, StateT.run body s = .value ([.value r]ₕ, t) ∧ s ≈ t) :
    ∃ s' : GlobalState, StateT.run (runFunction body) s = .value ([.value r]ₕ, s') ∧ s ≈ s' :=
  let ⟨t, hb, he⟩ := h
  ⟨s.popFrame t.mem, run_runFunction hb,
    (GlobalState.killFrom_equiv t.mem hs fun q _ => (he.live q).symm).symm⟩

/-- `x < ℓ` as a 256-bit comparison. -/
private theorem lt_groupOrder_iff (x : BitVec 256) :
    x.toNat < groupOrder ↔ x < BitVec.ofNat 256 groupOrder := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]

/-- A top byte below `0x10` is below `ℓ`. -/
private theorem lt_groupOrder_of_top (x : BitVec 256) (h : (x.extractLsb' 248 8).ult 16#8) :
    x.toNat < groupOrder := by
  rw [lt_groupOrder_iff, groupOrder]; bv_decide

/-- A top byte at or above `0x20` is not. -/
private theorem not_lt_groupOrder_of_top (x : BitVec 256)
    (h : ¬(x.extractLsb' 248 8).ult 32#8 = true) : ¬x.toNat < groupOrder := by
  rw [lt_groupOrder_iff, groupOrder]; bv_decide

/-- `^bb2`'s limb comparison is `x < ℓ`. -/
private theorem limbs_iff (x : BitVec 256) :
    BitVec.ofBool ((x.extractLsb' 192 64).ult
        (if BitVec.ofBool (x.extractLsb' 128 64 == 0#64 && (x.extractLsb' 64 64).ult
            (if BitVec.ofBool ((x.extractLsb' 0 64).ult 6346243789798364141#64) = 1#1
            then 1503914060200516823#64 else 1503914060200516822#64)) = 1#1
        then 1152921504606846977#64 else 1152921504606846976#64)) = 1#1
      ↔ x.toNat < groupOrder := by
  rw [lt_groupOrder_iff, groupOrder]; bv_decide

/-- Bits `j` to `j + w` of the scalar, read from its block. -/
private theorem extractLsb'_eq_readBuf {m : MemoryState} {p : Pointer} (hp : IsByteBufPtr m p)
    {blk : LiveBlock} (hblk : m.live? p.id = some blk) {j w : Nat} (hj : j + w ≤ 256) :
    blk.bytes.extractLsb' (p.offsetInBits + j) w = (readBuf hp).extractLsb' j w := by
  simp only [readBuf, readBuf?, hblk, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.get_some]
  ext k hk
  simp only [BitVec.getElem_extractLsb', Nat.add_assoc]
  rw [BitVec.getLsbD_extractLsb', decide_eq_true (by omega : j + k < 256), Bool.true_and]

/-- A word read inside the scalar, at a state agreeing with `m` on its block. -/
private theorem readWord_eq_readBuf {m m' : MemoryState} {p q : Pointer}
    (hp : IsByteBufPtr m p) {w : Nat} (h : Fits m' q w) (hid : q.id = p.id)
    (hl : m'.live? p.id = m.live? p.id) {j : Nat} (ho : q.offsetInBits = p.offsetInBits + j)
    (hj : j + w ≤ 256) : readWord h = (readBuf hp).extractLsb' j w := by
  obtain ⟨blk, hblk, -⟩ := hp.1
  have hlive : m.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  apply readWord_eq_of
  simp only [readWord?, hid, hl, hlive, ho, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, extractLsb'_eq_readBuf hp hlive hj]

/-- `p + o` in bits, when the sum does not wrap. -/
private theorem offsetInBits_withOffset (p : Pointer) (o : BitVec 64)
    (h : p.offset.toNat + o.toNat < 2 ^ 64) :
    (p.withOffset o).offsetInBits = p.offsetInBits + 8 * o.toNat := by
  simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

set_option maxHeartbeats 1000000 in
theorem fd_curve25519_scalar_validate_conforms (p : Pointer) (s : GlobalState)
    (hs : s.WF) (hp : IsByteBufPtr s.mem p) :
    fd_curve25519_scalar_validate_spec p s hp := by
  simp only [fd_curve25519_scalar_validate_spec, Cfg.denote]

  refine wrap hs ?_

  denote_step_reduce v 8 [LLVM.const?]
  obtain ⟨blk, hblk, hlen⟩ := hp.left
  have hlive : s.mem.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  have hoff : p.offset.toNat + 32 ≤ 2 ^ 64 := hp.right
  -- `%9`: `s + 31`
  peel_gep 31 with p, hp.left, s as p31
  have hoff31 : p31.offsetInBits = p.offsetInBits + 248 :=
    offsetInBits_withOffset p 31 (by simp; omega)
  have hblk31 : s.mem[p31.id]? = some (.live blk) := hblk
  -- `%10`: the top byte
  peel_load (.bitvec (.concrete 8)), blk, p31, hblk31, s
  denote_step_reduce v 11 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv6]
  simp only [BlockCom.denote_term, Terminator.denote_condBr, hv11, simp_denote, simp_sllvm]
  -- the top byte, named once
  obtain ⟨top, htop⟩ : ∃ top : BitVec 8, blk.bytes.extractLsb' p31.offsetInBits 8 = top :=
    ⟨_, rfl⟩
  have htopx : top = (readBuf hp).extractLsb' 248 8 := by
    rw [← htop, hoff31, extractLsb'_eq_readBuf hp hlive (by decide)]
  rw [htop] at hv11
  subst hv11
  by_cases hlt16 : top <ᵤ 16#8
  case pos =>
    -- `^bb3(%arg0)`: below `0x10`, accept
    rw [if_pos (lt_groupOrder_of_top _ (htopx ▸ hlt16))]
    simp [hlt16, htop]
    denote_enter_block
    simp_return
    rfl

  simp [hlt16, htop]
  denote_enter_block
  -- `^bb1`: `%12 = top <u 32`
  denote_step_reduce v 12 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', htop, hv7]
  by_cases hlt32 : top <ᵤ 32#8
  case neg =>
    -- `^bb3(NULL)`: at or above `0x20`, reject
    rw [if_neg (not_lt_groupOrder_of_top _ (htopx ▸ hlt32))]
    simp [hv12, hlt32, BitVec.ofBool_false, BlockCom.denote_term,
      Terminator.denote_condBr_value, simp_denote, simp_sllvm]
    denote_enter_block
    simp_return
    simp [hv8, Ptr.null]
    rfl

  simp only [hv12, hlt32, BitVec.ofBool_true, BlockCom.denote_term,
    Terminator.denote_condBr_value, simp_denote, simp_sllvm]
  denote_enter_block
  -- `^bb2`: the four `fd_ulong_load_8` calls; the stepper restarts at the entry's depth, MLIR at `%13`.
  denote_number_from 13
  have hfit0 : Fits s.mem p 64 := Fits.mono hp.left (by omega)
  refine fd_ulong_load_8_conforms_cont p s hs hfit0 fun t0 hcall0 he0 => ?_
  peel_call hcall0
  -- the scalar still fits, at each state the calls leave behind
  have hfit0' : Fits t0.mem p (32 * 8) := fits_of_live?_eq (he0.live p.id).symm hp.left
  -- `%14`/`%15`: `s + 8`
  peel_gep 8 with p, hfit0', t0 as p8
  refine fd_ulong_load_8_conforms_cont p8 t0 (hs.of_equiv he0) (Fits.mono hp8 (by decide))
    fun t1 hcall1 he1 => ?_
  peel_call hcall1
  have hfit1' : Fits t1.mem p (32 * 8) := fits_of_live?_eq (he1.live p.id).symm hfit0'
  -- `%16`/`%17`: `s + 16`
  peel_gep 16 with p, hfit1', t1 as p16
  refine fd_ulong_load_8_conforms_cont p16 t1 ((hs.of_equiv he0).of_equiv he1)
    (Fits.mono hp16 (by decide)) fun t2 hcall2 he2 => ?_
  peel_call hcall2
  have hfit2' : Fits t2.mem p (32 * 8) := fits_of_live?_eq (he2.live p.id).symm hfit1'
  -- `%18`/`%19`: `s + 24`
  peel_gep 24 with p, hfit2', t2 as p24
  refine fd_ulong_load_8_conforms_cont p24 t2 (((hs.of_equiv he0).of_equiv he1).of_equiv he2)
    (Fits.mono hp24 (by decide)) fun t3 hcall3 he3 => ?_
  peel_call hcall3

  denote_step_reduce v 27 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, LLVM.and, LLVM.and?, htop, hv8, hv2, hv5, hv4, hv3, hv1, hv0, Ctxt.Valuation.singleton, ptrselect, Ptr.null] fold

  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  denote_enter_block
  simp_return
  have hl0 : t0.mem.live? p.id = s.mem.live? p.id := (he0.live p.id).symm
  have hl1 : t1.mem.live? p.id = s.mem.live? p.id := (he1.live p.id).symm.trans hl0
  have hl2 : t2.mem.live? p.id = s.mem.live? p.id := (he2.live p.id).symm.trans hl1
  rw [readWord_eq_readBuf hp hfit0 rfl rfl (j := 0) rfl (by decide),
    readWord_eq_readBuf (q := p8) (j := 64) hp _ rfl hl0
      (by rw [offsetInBits_withOffset _ _ (by simp; omega)]; rfl) (by decide),
    readWord_eq_readBuf (q := p16) (j := 128) hp _ rfl hl1
      (by rw [offsetInBits_withOffset _ _ (by simp; omega)]; rfl) (by decide),
    readWord_eq_readBuf (q := p24) (j := 192) hp _ rfl hl2
      (by rw [offsetInBits_withOffset _ _ (by simp; omega)]; rfl) (by decide)] at hv27
  simp only [limbs_iff] at hv27
  exact ⟨hv27, ((he0.trans he1).trans he2).trans he3⟩

end Firedancer.Common
