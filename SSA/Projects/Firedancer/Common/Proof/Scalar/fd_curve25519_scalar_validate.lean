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
`l`, returning `s` or `NULL` by `select`. Every path only reads, so the state
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
    {s : GlobalState} {p : Pointer} (hs : s.WF)
    (h : ∃ (t : GlobalState) (ret : Pointer), StateT.run body s = .value ([.value ret]ₕ, t)
      ∧ (ret = p ∨ ret = ⟨nullBlock, 0#64⟩) ∧ s ≈ t) :
    ∃ (s' : GlobalState) (ret : Pointer),
      StateT.run (runFunction body) s = .value ([.value ret]ₕ, s')
        ∧ (ret = p ∨ ret = ⟨nullBlock, 0#64⟩) ∧ s ≈ s' :=
  let ⟨t, ret, hb, hr, he⟩ := h
  ⟨s.popFrame t.mem, ret, run_runFunction hb, hr,
    (GlobalState.killFrom_equiv t.mem hs fun q _ => (he.live q).symm).symm⟩

/-- `p + o` in bits, when the sum does not wrap. -/
private theorem offsetInBits_withOffset (p : Pointer) (o : BitVec 64)
    (h : p.offset.toNat + o.toNat < 2 ^ 64) :
    (p.withOffset o).offsetInBits = p.offsetInBits + 8 * o.toNat := by
  simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

set_option maxHeartbeats 1000000 in
theorem fd_curve25519_scalar_validate_conforms (p : Pointer) (s : GlobalState)
    (hs : s.WF) (hp : IsScalarPtr s.mem p) :
    fd_curve25519_scalar_validate_spec p s := by
  simp only [fd_curve25519_scalar_validate_spec, Cfg.denote]

  refine wrap hs ?_

  denote_step_reduce v 8 [LLVM.const?]
  obtain ⟨blk, hblk, hlen⟩ := hp.left
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
  rw [htop] at hv11
  subst hv11
  by_cases hlt16 : top <ᵤ 16#8
  case pos =>
    -- `^bb3(%arg0)`: below `0x10`, accept
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
  obtain ⟨t0, hcall0, he0⟩ := fd_ulong_load_8_conforms p s hs hfit0
  peel_call hcall0
  -- the scalar still fits, at each state the calls leave behind
  have hfit0' : Fits t0.mem p (32 * 8) := fits_of_live?_eq (he0.live p.id).symm hp.left
  -- `%14`/`%15`: `s + 8`
  peel_gep 8 with p, hfit0', t0 as p8
  obtain ⟨t1, hcall1, he1⟩ :=
    fd_ulong_load_8_conforms p8 t0 (hs.of_equiv he0) (Fits.mono hp8 (by bv_omega))
  peel_call hcall1
  have hfit1' : Fits t1.mem p (32 * 8) := fits_of_live?_eq (he1.live p.id).symm hfit0'
  -- `%16`/`%17`: `s + 16`
  peel_gep 16 with p, hfit1', t1 as p16
  obtain ⟨t2, hcall2, he2⟩ :=
    fd_ulong_load_8_conforms p16 t1 ((hs.of_equiv he0).of_equiv he1) (Fits.mono hp16 (by bv_omega))
  peel_call hcall2
  have hfit2' : Fits t2.mem p (32 * 8) := fits_of_live?_eq (he2.live p.id).symm hfit1'
  -- `%18`/`%19`: `s + 24`
  peel_gep 24 with p, hfit2', t2 as p24
  obtain ⟨t3, hcall3, he3⟩ :=
    fd_ulong_load_8_conforms p24 t2 (((hs.of_equiv he0).of_equiv he1).of_equiv he2)
      (Fits.mono hp24 (by bv_omega))
  peel_call hcall3

  denote_step_reduce v 27 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, LLVM.and, LLVM.and?, htop, hv8, hv2, hv5, hv4, hv3, hv1, hv0, Ctxt.Valuation.singleton, ptrselect, Ptr.null] fold

  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  denote_enter_block
  simp_return
  obtain ⟨ret, hret⟩ : ∃ ret, v27 = .value ret := by simp [hv27]
  refine ⟨ret, hret, ?_⟩
  have : v27 = .value p ∨ v27 = .value { id := nullBlock, offset := 0#64 } := by
    split_ifs at hv27 <;> simp [hv27]
  simp [hret] at this
  simp [this]
  apply fun h => GlobalState.Equiv.trans h he3
  apply fun h => GlobalState.Equiv.trans h he2
  apply fun h => GlobalState.Equiv.trans h he1
  exact he0

end Firedancer.Common
