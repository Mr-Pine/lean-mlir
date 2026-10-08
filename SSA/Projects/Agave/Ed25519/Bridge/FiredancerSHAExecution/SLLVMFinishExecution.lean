import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceFinish
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace FinishExecution

def word (m : MemoryState) (p : Pointer) : BitVec 64 :=
  (readWord? p 64 m).getD 0

theorem word_live (m : MemoryState) (p : Pointer) (b : LiveBlock)
    (h : m[p.id]? = some (.live b)) :
    word m p = b.bytes.extractLsb' p.offsetInBits 64 := by
  simp [word, readWord?, MemoryState.live?, h]

def markerMemory (m : MemoryState) (p : Pointer) (used : Nat) :=
  m.splice (p.withOffset (BitVec.ofNat 64 used)) (128#8)

def longMemory (m : MemoryState) (p : Pointer) (used : Nat) :=
  m.splice (p.withOffset (BitVec.ofNat 64 (used+1))) (BitVec.replicate (127-used) (0#8))

def lastMemory (m : MemoryState) (p : Pointer) (n : Nat) (lo hi : BitVec 64) :=
  let m := m.splice (p.withOffset (BitVec.ofNat 64 n)) (BitVec.replicate (112-n) (0#8))
  let m := m.splice (p.withOffset 112#64) (bswapBV hi)
  m.splice (p.withOffset 120#64) (bswapBV lo)

def outputStep (m : MemoryState) (p o : Pointer) (i : Nat) :=
  m.splice (o.withOffset (BitVec.ofNat 64 (8*i)))
    (bswapBV (word m (p.withOffset (BitVec.ofNat 64 (128+8*i)))))

def outputMemory (m : MemoryState) (p o : Pointer) :=
  let m := outputStep m p o 0
  let m := outputStep m p o 1
  let m := outputStep m p o 2
  let m := outputStep m p o 3
  let m := outputStep m p o 4
  let m := outputStep m p o 5
  let m := outputStep m p o 6
  outputStep m p o 7

theorem sub_last (n : Nat) (hn : n ≤ 112) :
    LLVM.sub (.value 112#64) (.value (BitVec.ofNat 64 n)) {nsw := true, nuw := true} =
      .value (BitVec.ofNat 64 (112-n)) := by
  interval_cases n <;> decide

theorem sub_long (n : Nat) (hn : n < 128) :
    LLVM.sub (.value 127#64) (.value (BitVec.ofNat 64 n)) =
      .value (BitVec.ofNat 64 (127-n)) := by
  interval_cases n <;> decide

theorem global_eq (a b : GlobalState) (ha : a.alloc = b.alloc) (hm : a.mem = b.mem)
    (hg : a.globals = b.globals) : a = b := by
  cases a; cases b; simp_all

attribute [local irreducible] core markerMemory longMemory lastMemory outputMemory word

theorem short_body (p o : Pointer) (s after : GlobalState) (used : Nat)
    (lo hi : BitVec 64) (hn : used < 112) (hr : Fits s.mem p (224*8))
    (hu : word s.mem (p.withOffset 200#64) = BitVec.ofNat 64 used)
    (hlo : word s.mem (p.withOffset 208#64) = lo)
    (hhi : word s.mem (p.withOffset 216#64) = hi)
    (hc : Fits after.mem p (224*8)) (ho : Fits after.mem o (64*8))
    (hcore : StateT.run (runFunction (core.denote
        (.cons (.value 1#64) (.cons (.value p)
          (Ctxt.Valuation.singleton (.value (p.withOffset 128#64)))))))
      {s with mem := lastMemory (markerMemory s.mem p used) p (used+1) lo hi} =
        .value (.nil, after)) :
    StateT.run (finish.denote (.cons (.value o) (Ctxt.Valuation.singleton (.value p)))) s =
      .value ([.value o]ₕ, {after with mem := outputMemory after.mem p o}) := by
  simp only [Cfg.denote]
  denote_expose
  denote_number_from 0
  denote_step_all v 24
  denote_eval v 0 24
  have k0 : BitVec.ofInt 64 (128) = (128#64) := by decide
  have k1 : BitVec.ofInt 64 (200) = (200#64) := by decide
  have k2 : BitVec.ofInt 64 (208) = (208#64) := by decide
  have k3 : BitVec.ofInt 64 (216) = (216#64) := by decide
  have k4 : BitVec.ofInt 8 (-128) = (128#8) := by decide
  have k5 : BitVec.ofInt 64 (1) = (1#64) := by decide
  have k6 : BitVec.ofInt 64 (112) = (112#64) := by decide
  have k7 : BitVec.ofInt 64 (127) = (127#64) := by decide
  have k8 : BitVec.ofInt 8 (0) = (0#8) := by decide
  have k9 : BitVec.ofInt 64 (0) = (0#64) := by decide
  have k10 : BitVec.ofInt 64 (120) = (120#64) := by decide
  have k11 : BitVec.ofInt 64 (136) = (136#64) := by decide
  have k12 : BitVec.ofInt 64 (8) = (8#64) := by decide
  have k13 : BitVec.ofInt 64 (144) = (144#64) := by decide
  have k14 : BitVec.ofInt 64 (16) = (16#64) := by decide
  have k15 : BitVec.ofInt 64 (152) = (152#64) := by decide
  have k16 : BitVec.ofInt 64 (24) = (24#64) := by decide
  have k17 : BitVec.ofInt 64 (160) = (160#64) := by decide
  have k18 : BitVec.ofInt 64 (32) = (32#64) := by decide
  have k19 : BitVec.ofInt 64 (168) = (168#64) := by decide
  have k20 : BitVec.ofInt 64 (40) = (40#64) := by decide
  have k21 : BitVec.ofInt 64 (176) = (176#64) := by decide
  have k22 : BitVec.ofInt 64 (48) = (48#64) := by decide
  have k23 : BitVec.ofInt 64 (184) = (184#64) := by decide
  have k24 : BitVec.ofInt 64 (56) = (56#64) := by decide
  simp only [LLVM.const?, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24] at hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24
  peel_gep 128 with p, hr, s as chain
  peel_gep 200 with p, hr, s as count
  obtain ⟨bu, hbu, hlenbu⟩ := hcount
  change count.offsetInBits + 192 ≤ bu.lengthInBits at hlenbu
  peel_load (.bitvec (.concrete 64)), bu, count, hbu, s
  have hu' : bu.bytes.extractLsb' count.offsetInBits 64 = BitVec.ofNat 64 used :=
    (word_live s.mem count bu hbu).symm.trans hu
  rw [hu']
  peel_gep 208 with p, hr, s as low
  obtain ⟨bl, hbl, hlenbl⟩ := hlow
  change low.offsetInBits + 128 ≤ bl.lengthInBits at hlenbl
  peel_load (.bitvec (.concrete 64)), bl, low, hbl, s
  have hlo' : bl.bytes.extractLsb' low.offsetInBits 64 = lo :=
    (word_live s.mem low bl hbl).symm.trans hlo
  rw [hlo']
  peel_gep 216 with p, hr, s as high
  obtain ⟨bh, hbh, hlenbh⟩ := hhigh
  peel_load (.bitvec (.concrete 64)), bh, high, hbh, s
  have hhi' : bh.bytes.extractLsb' high.offsetInBits 64 = hi :=
    (word_live s.mem high bh hbh).symm.trans hhi
  rw [hhi']
  denote_step_reduce v 32 [gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?,
    LLVM.add?, LLVM.mul?, Pointer.withOffset]
  have hused : (BitVec.ofNat 64 used).toNat = used := by simp <;> omega
  have hmarker := remainingFits s.mem p hr (BitVec.ofNat 64 used) (by rw [hused]; omega)
  have hv32' : v32 = .value (p.withOffset (BitVec.ofNat 64 used)) := by
    simpa [Pointer.withOffset, Ctxt.Valuation.singleton, simp_denote, simp_sllvm] using hv32
  subst hv32'
  let s1 : GlobalState := {s with mem := markerMemory s.mem p used}
  have hs1 : s1 = {s with mem := s.mem.splice (p.withOffset (BitVec.ofNat 64 used)) (128#8)} := by unfold s1 markerMemory; rfl
  peel_store (128#8), (p.withOffset (BitVec.ofNat 64 used)), hmarker, s as s1 := hs1
  denote_step_reduce v 34 [LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?] fold
  have hnext : BitVec.ofNat 64 used + 1#64 = BitVec.ofNat 64 (used+1) := by
    simp [BitVec.ofNat_add]
  have hchoice : LLVM.icmp' LLVM.IntPred.ugt (BitVec.ofNat 64 used + 1#64) 112#64 = false := by
    simp [LLVM.icmp', BitVec.ult, BitVec.toNat_add, hused]
    omega
  simp only [hchoice] at hv34
  simp [hv34, hv33, hnext, BlockCom.denote_term, Terminator.denote_condBr, Target.denote,
    simp_denote, simp_sllvm]
  denote_enter_block
  denote_number_from 38
  have f1 : Fits s1.mem p (224*8) := by rw [hs1]; exact fits_splice hr
  denote_step_reduce v 39 [gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?,
    LLVM.add?, LLVM.mul?, Pointer.withOffset, Ctxt.Valuation.singleton] fold
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv38 hv39
  rw [sub_last (used+1) (by omega)] at hv39
  subst hv38 hv39
  have hn1 : (BitVec.ofNat 64 (used+1)).toNat = used+1 := by simp <;> omega
  have hlen : (BitVec.ofNat 64 (112-(used+1))).toNat = 112-(used+1) := by simp <;> omega
  have hclear : Fits s1.mem (p.withOffset (BitVec.ofNat 64 (used+1)))
      (8*(BitVec.ofNat 64 (112-(used+1))).toNat) := by
    have h := remainingFits s1.mem p f1 (BitVec.ofNat 64 (used+1)) (by rw [hn1]; omega)
    apply Fits.mono h
    rw [hn1, hlen]
    omega
  let s2 : GlobalState := {s1 with mem := s1.mem.splice (p.withOffset (BitVec.ofNat 64 (used+1))) (BitVec.replicate (112-(used+1)) (0#8))}
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s2) (by
    simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
    simp -failIfUnchanged only [simp_denote, simp_sllvm]
    have hm := run_liftM (s := s1) (run_memset (b := 0#8) (len := BitVec.ofNat 64 (112-(used+1))) hclear)
    simp only [Pointer.withOffset, BitVec.add_zero] at hm
    rw [hm]
    change PoisonOr.value ((HVector.nil : HVector TyDenote.toType ([] : List SLLVM.Ty)), {s1 with mem := s1.mem.splice (p.withOffset (BitVec.ofNat 64 (used+1))) (BitVec.replicate (BitVec.ofNat 64 (112-(used+1))).toNat (0#8))}) = .value (.nil, s2)
    rw [hlen])]
  have f2 : Fits s2.mem p (224*8) := fits_splice f1
  denote_step_reduce v 40 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv40
  subst hv40
  peel_gep 112 with p, f2, s2 as hiptr
  peel_store (bswapBV hi), hiptr, hhiptr, s2
  obtain ⟨s3, hs3⟩ : ∃ t : GlobalState, {s2 with mem := s2.mem.splice hiptr (bswapBV hi)} = t := ⟨_, rfl⟩
  rw [hs3]
  have f3 : Fits s3.mem p (224*8) := hs3 ▸ fits_splice f2
  denote_step_reduce v 42 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv42
  subst hv42
  peel_gep 120 with p, f3, s3 as loptr
  peel_store (bswapBV lo), loptr, hloptr, s3
  have hpre : {s3 with mem := s3.mem.splice loptr (bswapBV lo)} =
      {s with mem := lastMemory (markerMemory s.mem p used) p (used+1) lo hi} := by
    rw [← hs3]
    unfold s2 s1 lastMemory
    rfl
  rw [hpre]
  peel_call hcore with chain
  have fc0 : Fits after.mem chain 768 := by simpa [chain] using remainingFits after.mem p hc (128#64) (by decide)
  obtain ⟨ob0, hob0, holen0⟩ := fc0
  change chain.offsetInBits + 768 ≤ ob0.lengthInBits at holen0
  peel_load (.bitvec (.concrete 64)), ob0, chain, hob0, after
  rw [← word_live after.mem chain ob0 hob0]
  denote_step_reduce v 45 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv45
  subst hv45
  peel_store (bswapBV (word after.mem chain)), o, ho, after
  obtain ⟨out1, hout1⟩ : ∃ t : GlobalState, {after with mem := after.mem.splice o (bswapBV (word after.mem chain))} = t := ⟨_, rfl⟩
  rw [hout1]
  have hm1 : out1.mem = outputStep after.mem p o 0 := by
    rw [← hout1]
    simp [outputStep, chain, Pointer.withOffset]
  have fc1 : Fits out1.mem p (224*8) := hout1 ▸ fits_splice hc
  have fo1 : Fits out1.mem o (64*8) := hout1 ▸ fits_splice ho
  peel_gep 136 with p, fc1, out1 as cp1
  obtain ⟨ob1, hob1, holen1⟩ := hcp1
  change cp1.offsetInBits + 704 ≤ ob1.lengthInBits at holen1
  peel_load (.bitvec (.concrete 64)), ob1, cp1, hob1, out1
  rw [← word_live out1.mem cp1 ob1 hob1]
  denote_step_reduce v 48 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv48
  subst hv48
  peel_gep 8 with o, fo1, out1 as op1
  peel_store (bswapBV (word out1.mem cp1)), op1, hop1, out1
  obtain ⟨out2, hout2⟩ : ∃ t : GlobalState, {out1 with mem := out1.mem.splice op1 (bswapBV (word out1.mem cp1))} = t := ⟨_, rfl⟩
  rw [hout2]
  have hm2 : out2.mem = outputStep out1.mem p o 1 := by
    rw [← hout2]
    simp [outputStep, cp1, op1, Pointer.withOffset]
  have fc2 : Fits out2.mem p (224*8) := hout2 ▸ fits_splice fc1
  have fo2 : Fits out2.mem o (64*8) := hout2 ▸ fits_splice fo1
  peel_gep 144 with p, fc2, out2 as cp2
  obtain ⟨ob2, hob2, holen2⟩ := hcp2
  change cp2.offsetInBits + 640 ≤ ob2.lengthInBits at holen2
  peel_load (.bitvec (.concrete 64)), ob2, cp2, hob2, out2
  rw [← word_live out2.mem cp2 ob2 hob2]
  denote_step_reduce v 52 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv52
  subst hv52
  peel_gep 16 with o, fo2, out2 as op2
  peel_store (bswapBV (word out2.mem cp2)), op2, hop2, out2
  obtain ⟨out3, hout3⟩ : ∃ t : GlobalState, {out2 with mem := out2.mem.splice op2 (bswapBV (word out2.mem cp2))} = t := ⟨_, rfl⟩
  rw [hout3]
  have hm3 : out3.mem = outputStep out2.mem p o 2 := by
    rw [← hout3]
    simp [outputStep, cp2, op2, Pointer.withOffset]
  have fc3 : Fits out3.mem p (224*8) := hout3 ▸ fits_splice fc2
  have fo3 : Fits out3.mem o (64*8) := hout3 ▸ fits_splice fo2
  peel_gep 152 with p, fc3, out3 as cp3
  obtain ⟨ob3, hob3, holen3⟩ := hcp3
  change cp3.offsetInBits + 576 ≤ ob3.lengthInBits at holen3
  peel_load (.bitvec (.concrete 64)), ob3, cp3, hob3, out3
  rw [← word_live out3.mem cp3 ob3 hob3]
  denote_step_reduce v 56 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv56
  subst hv56
  peel_gep 24 with o, fo3, out3 as op3
  peel_store (bswapBV (word out3.mem cp3)), op3, hop3, out3
  obtain ⟨out4, hout4⟩ : ∃ t : GlobalState, {out3 with mem := out3.mem.splice op3 (bswapBV (word out3.mem cp3))} = t := ⟨_, rfl⟩
  rw [hout4]
  have hm4 : out4.mem = outputStep out3.mem p o 3 := by
    rw [← hout4]
    simp [outputStep, cp3, op3, Pointer.withOffset]
  have fc4 : Fits out4.mem p (224*8) := hout4 ▸ fits_splice fc3
  have fo4 : Fits out4.mem o (64*8) := hout4 ▸ fits_splice fo3
  peel_gep 160 with p, fc4, out4 as cp4
  obtain ⟨ob4, hob4, holen4⟩ := hcp4
  change cp4.offsetInBits + 512 ≤ ob4.lengthInBits at holen4
  peel_load (.bitvec (.concrete 64)), ob4, cp4, hob4, out4
  rw [← word_live out4.mem cp4 ob4 hob4]
  denote_step_reduce v 60 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv60
  subst hv60
  peel_gep 32 with o, fo4, out4 as op4
  peel_store (bswapBV (word out4.mem cp4)), op4, hop4, out4
  obtain ⟨out5, hout5⟩ : ∃ t : GlobalState, {out4 with mem := out4.mem.splice op4 (bswapBV (word out4.mem cp4))} = t := ⟨_, rfl⟩
  rw [hout5]
  have hm5 : out5.mem = outputStep out4.mem p o 4 := by
    rw [← hout5]
    simp [outputStep, cp4, op4, Pointer.withOffset]
  have fc5 : Fits out5.mem p (224*8) := hout5 ▸ fits_splice fc4
  have fo5 : Fits out5.mem o (64*8) := hout5 ▸ fits_splice fo4
  peel_gep 168 with p, fc5, out5 as cp5
  obtain ⟨ob5, hob5, holen5⟩ := hcp5
  change cp5.offsetInBits + 448 ≤ ob5.lengthInBits at holen5
  peel_load (.bitvec (.concrete 64)), ob5, cp5, hob5, out5
  rw [← word_live out5.mem cp5 ob5 hob5]
  denote_step_reduce v 64 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv64
  subst hv64
  peel_gep 40 with o, fo5, out5 as op5
  peel_store (bswapBV (word out5.mem cp5)), op5, hop5, out5
  obtain ⟨out6, hout6⟩ : ∃ t : GlobalState, {out5 with mem := out5.mem.splice op5 (bswapBV (word out5.mem cp5))} = t := ⟨_, rfl⟩
  rw [hout6]
  have hm6 : out6.mem = outputStep out5.mem p o 5 := by
    rw [← hout6]
    simp [outputStep, cp5, op5, Pointer.withOffset]
  have fc6 : Fits out6.mem p (224*8) := hout6 ▸ fits_splice fc5
  have fo6 : Fits out6.mem o (64*8) := hout6 ▸ fits_splice fo5
  peel_gep 176 with p, fc6, out6 as cp6
  obtain ⟨ob6, hob6, holen6⟩ := hcp6
  change cp6.offsetInBits + 384 ≤ ob6.lengthInBits at holen6
  peel_load (.bitvec (.concrete 64)), ob6, cp6, hob6, out6
  rw [← word_live out6.mem cp6 ob6 hob6]
  denote_step_reduce v 68 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv68
  subst hv68
  peel_gep 48 with o, fo6, out6 as op6
  peel_store (bswapBV (word out6.mem cp6)), op6, hop6, out6
  obtain ⟨out7, hout7⟩ : ∃ t : GlobalState, {out6 with mem := out6.mem.splice op6 (bswapBV (word out6.mem cp6))} = t := ⟨_, rfl⟩
  rw [hout7]
  have hm7 : out7.mem = outputStep out6.mem p o 6 := by
    rw [← hout7]
    simp [outputStep, cp6, op6, Pointer.withOffset]
  have fc7 : Fits out7.mem p (224*8) := hout7 ▸ fits_splice fc6
  have fo7 : Fits out7.mem o (64*8) := hout7 ▸ fits_splice fo6
  peel_gep 184 with p, fc7, out7 as cp7
  obtain ⟨ob7, hob7, holen7⟩ := hcp7
  change cp7.offsetInBits + 320 ≤ ob7.lengthInBits at holen7
  peel_load (.bitvec (.concrete 64)), ob7, cp7, hob7, out7
  rw [← word_live out7.mem cp7 ob7 hob7]
  denote_step_reduce v 72 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv72
  subst hv72
  peel_gep 56 with o, fo7, out7 as op7
  peel_store (bswapBV (word out7.mem cp7)), op7, hop7, out7
  obtain ⟨out8, hout8⟩ : ∃ t : GlobalState, {out7 with mem := out7.mem.splice op7 (bswapBV (word out7.mem cp7))} = t := ⟨_, rfl⟩
  rw [hout8]
  have hm8 : out8.mem = outputStep out7.mem p o 7 := by
    rw [← hout8]
    simp [outputStep, cp7, op7, Pointer.withOffset]
  have hmfinal : out8.mem = outputMemory after.mem p o := by
    simp only [outputMemory, ← hm1, ← hm2, ← hm3, ← hm4, ← hm5, ← hm6, ← hm7, ← hm8]
  have hafinal : out8.alloc = after.alloc := by
    simp only [← hout8, ← hout7, ← hout6, ← hout5, ← hout4, ← hout3, ← hout2, ← hout1]
  have hgfinal : out8.globals = after.globals := by
    simp only [← hout8, ← hout7, ← hout6, ← hout5, ← hout4, ← hout3, ← hout2, ← hout1]
  have hfinal : out8 = {after with mem := outputMemory after.mem p o} :=
    global_eq _ _ hafinal hmfinal hgfinal
  simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm, hfinal]

theorem long_body (p o : Pointer) (s middle after : GlobalState) (used : Nat)
    (lo hi : BitVec 64) (hn : used < 128) (hl : 112 ≤ used) (hr : Fits s.mem p (224*8))
    (hu : word s.mem (p.withOffset 200#64) = BitVec.ofNat 64 used)
    (hlo : word s.mem (p.withOffset 208#64) = lo)
    (hhi : word s.mem (p.withOffset 216#64) = hi)
    (hc : Fits after.mem p (224*8)) (ho : Fits after.mem o (64*8))
    (hmiddle : Fits middle.mem p (224*8))
    (hcoreFirst : StateT.run (runFunction (core.denote
        (.cons (.value 1#64) (.cons (.value p)
          (Ctxt.Valuation.singleton (.value (p.withOffset 128#64)))))))
      {s with mem := longMemory (markerMemory s.mem p used) p used} =
        .value (.nil, middle))
    (hcore : StateT.run (runFunction (core.denote
        (.cons (.value 1#64) (.cons (.value p)
          (Ctxt.Valuation.singleton (.value (p.withOffset 128#64)))))))
      {middle with mem := lastMemory middle.mem p 0 lo hi} =
        .value (.nil, after)) :
    StateT.run (finish.denote (.cons (.value o) (Ctxt.Valuation.singleton (.value p)))) s =
      .value ([.value o]ₕ, {after with mem := outputMemory after.mem p o}) := by
  simp only [Cfg.denote]
  denote_expose
  denote_number_from 0
  denote_step_all v 24
  denote_eval v 0 24
  have k0 : BitVec.ofInt 64 (128) = (128#64) := by decide
  have k1 : BitVec.ofInt 64 (200) = (200#64) := by decide
  have k2 : BitVec.ofInt 64 (208) = (208#64) := by decide
  have k3 : BitVec.ofInt 64 (216) = (216#64) := by decide
  have k4 : BitVec.ofInt 8 (-128) = (128#8) := by decide
  have k5 : BitVec.ofInt 64 (1) = (1#64) := by decide
  have k6 : BitVec.ofInt 64 (112) = (112#64) := by decide
  have k7 : BitVec.ofInt 64 (127) = (127#64) := by decide
  have k8 : BitVec.ofInt 8 (0) = (0#8) := by decide
  have k9 : BitVec.ofInt 64 (0) = (0#64) := by decide
  have k10 : BitVec.ofInt 64 (120) = (120#64) := by decide
  have k11 : BitVec.ofInt 64 (136) = (136#64) := by decide
  have k12 : BitVec.ofInt 64 (8) = (8#64) := by decide
  have k13 : BitVec.ofInt 64 (144) = (144#64) := by decide
  have k14 : BitVec.ofInt 64 (16) = (16#64) := by decide
  have k15 : BitVec.ofInt 64 (152) = (152#64) := by decide
  have k16 : BitVec.ofInt 64 (24) = (24#64) := by decide
  have k17 : BitVec.ofInt 64 (160) = (160#64) := by decide
  have k18 : BitVec.ofInt 64 (32) = (32#64) := by decide
  have k19 : BitVec.ofInt 64 (168) = (168#64) := by decide
  have k20 : BitVec.ofInt 64 (40) = (40#64) := by decide
  have k21 : BitVec.ofInt 64 (176) = (176#64) := by decide
  have k22 : BitVec.ofInt 64 (48) = (48#64) := by decide
  have k23 : BitVec.ofInt 64 (184) = (184#64) := by decide
  have k24 : BitVec.ofInt 64 (56) = (56#64) := by decide
  simp only [LLVM.const?, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24] at hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24
  peel_gep 128 with p, hr, s as chain
  peel_gep 200 with p, hr, s as count
  obtain ⟨bu, hbu, hlenbu⟩ := hcount
  change count.offsetInBits + 192 ≤ bu.lengthInBits at hlenbu
  peel_load (.bitvec (.concrete 64)), bu, count, hbu, s
  have hu' : bu.bytes.extractLsb' count.offsetInBits 64 = BitVec.ofNat 64 used :=
    (word_live s.mem count bu hbu).symm.trans hu
  rw [hu']
  peel_gep 208 with p, hr, s as low
  obtain ⟨bl, hbl, hlenbl⟩ := hlow
  change low.offsetInBits + 128 ≤ bl.lengthInBits at hlenbl
  peel_load (.bitvec (.concrete 64)), bl, low, hbl, s
  have hlo' : bl.bytes.extractLsb' low.offsetInBits 64 = lo :=
    (word_live s.mem low bl hbl).symm.trans hlo
  rw [hlo']
  peel_gep 216 with p, hr, s as high
  obtain ⟨bh, hbh, hlenbh⟩ := hhigh
  peel_load (.bitvec (.concrete 64)), bh, high, hbh, s
  have hhi' : bh.bytes.extractLsb' high.offsetInBits 64 = hi :=
    (word_live s.mem high bh hbh).symm.trans hhi
  rw [hhi']
  denote_step_reduce v 32 [gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?,
    LLVM.add?, LLVM.mul?, Pointer.withOffset]
  have hused : (BitVec.ofNat 64 used).toNat = used := by simp <;> omega
  have hmarker := remainingFits s.mem p hr (BitVec.ofNat 64 used) (by rw [hused]; omega)
  have hv32' : v32 = .value (p.withOffset (BitVec.ofNat 64 used)) := by
    simpa [Pointer.withOffset, Ctxt.Valuation.singleton, simp_denote, simp_sllvm] using hv32
  subst hv32'
  let s1 : GlobalState := {s with mem := markerMemory s.mem p used}
  have hs1 : s1 = {s with mem := s.mem.splice (p.withOffset (BitVec.ofNat 64 used)) (128#8)} := by unfold s1 markerMemory; rfl
  peel_store (128#8), (p.withOffset (BitVec.ofNat 64 used)), hmarker, s as s1 := hs1
  denote_step_reduce v 34 [LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?] fold
  have hnext : BitVec.ofNat 64 used + 1#64 = BitVec.ofNat 64 (used+1) := by
    simp [BitVec.ofNat_add]
  have hchoice : LLVM.icmp' LLVM.IntPred.ugt (BitVec.ofNat 64 used + 1#64) 112#64 = true := by
    simp [LLVM.icmp', BitVec.ult, BitVec.toNat_add, hused]
    omega
  simp only [hchoice] at hv34
  simp [hv34, hv33, hnext, BlockCom.denote_term, Terminator.denote_condBr, Target.denote,
    simp_denote, simp_sllvm]
  denote_enter_block
  denote_number_from 35
  have fl1 : Fits s1.mem p (224*8) := by rw [hs1]; exact fits_splice hr
  denote_step_reduce v 36 [gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?,
    LLVM.add?, LLVM.mul?, Pointer.withOffset, Ctxt.Valuation.singleton] fold
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv35 hv36
  rw [sub_long used hn] at hv36
  subst hv35 hv36
  have hlongNext : (BitVec.ofNat 64 (used+1)).toNat = used+1 := by simp <;> omega
  have hlongLen : (BitVec.ofNat 64 (127-used)).toNat = 127-used := by simp <;> omega
  have hlongClear : Fits s1.mem (p.withOffset (BitVec.ofNat 64 (used+1)))
      (8*(BitVec.ofNat 64 (127-used)).toNat) := by
    have h := remainingFits s1.mem p fl1 (BitVec.ofNat 64 (used+1)) (by rw [hlongNext]; omega)
    apply Fits.mono h
    rw [hlongNext, hlongLen]
    omega
  let sl : GlobalState := {s1 with mem := s1.mem.splice (p.withOffset (BitVec.ofNat 64 (used+1))) (BitVec.replicate (127-used) (0#8))}
  rw [BlockCom.run_bind_denote_var_of_nil (s' := sl) (by
    simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
    have hm := run_liftM (s := s1) (run_memset (b := 0#8) (len := BitVec.ofNat 64 (127-used)) hlongClear)
    simp only [Pointer.withOffset, BitVec.add_zero] at hm
    rw [hm]
    change PoisonOr.value ((HVector.nil : HVector TyDenote.toType ([] : List SLLVM.Ty)), {s1 with mem := s1.mem.splice (p.withOffset (BitVec.ofNat 64 (used+1))) (BitVec.replicate (BitVec.ofNat 64 (127-used)).toNat (0#8))}) = .value (.nil, sl)
    rw [hlongLen])]
  have hlongPre : sl = {s with mem := longMemory (markerMemory s.mem p used) p used} := by
    unfold sl s1 longMemory
    rfl
  rw [hlongPre]
  peel_call hcoreFirst with chain
  simp [BlockCom.denote_term, Terminator.denote_br, Target.denote, simp_denote, simp_sllvm]
  denote_enter_block
  denote_number_from 38
  have f1 : Fits middle.mem p (224*8) := hmiddle
  denote_step_reduce v 39 [gep, gepConst, ptradd, LLVM.add, LLVM.mul, LLVM.const?,
    LLVM.add?, LLVM.mul?, Pointer.withOffset, Ctxt.Valuation.singleton] fold
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv38 hv39
  rw [sub_last 0 (by omega)] at hv39
  subst hv38 hv39
  have hn1 : (BitVec.ofNat 64 0).toNat = 0 := by simp <;> omega
  have hlen : (BitVec.ofNat 64 (112-0)).toNat = 112-0 := by simp <;> omega
  have hclear : Fits middle.mem (p.withOffset (BitVec.ofNat 64 0))
      (8*(BitVec.ofNat 64 (112-0)).toNat) := by
    have h := remainingFits middle.mem p f1 (BitVec.ofNat 64 0) (by rw [hn1]; omega)
    apply Fits.mono h
    rw [hn1, hlen]
    omega
  let s2 : GlobalState := {middle with mem := middle.mem.splice (p.withOffset (BitVec.ofNat 64 0)) (BitVec.replicate (112-0) (0#8))}
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s2) (by
    simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
    simp -failIfUnchanged only [simp_denote, simp_sllvm]
    have hm := run_liftM (s := middle) (run_memset (b := 0#8) (len := BitVec.ofNat 64 (112-0)) hclear)
    simp only [Pointer.withOffset, BitVec.add_zero] at hm
    rw [hm]
    simp [s2, Pointer.withOffset, hlen, simp_sllvm])]
  have f2 : Fits s2.mem p (224*8) := fits_splice f1
  denote_step_reduce v 40 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv40
  subst hv40
  peel_gep 112 with p, f2, s2 as hiptr
  peel_store (bswapBV hi), hiptr, hhiptr, s2
  obtain ⟨s3, hs3⟩ : ∃ t : GlobalState, {s2 with mem := s2.mem.splice hiptr (bswapBV hi)} = t := ⟨_, rfl⟩
  rw [hs3]
  have f3 : Fits s3.mem p (224*8) := hs3 ▸ fits_splice f2
  denote_step_reduce v 42 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv42
  subst hv42
  peel_gep 120 with p, f3, s3 as loptr
  peel_store (bswapBV lo), loptr, hloptr, s3
  have hpre : {s3 with mem := s3.mem.splice loptr (bswapBV lo)} =
      {middle with mem := lastMemory middle.mem p 0 lo hi} := by
    rw [← hs3]
    unfold s2 lastMemory
    rfl
  rw [hpre]
  peel_call hcore with chain
  have fc0 : Fits after.mem chain 768 := by simpa [chain] using remainingFits after.mem p hc (128#64) (by decide)
  obtain ⟨ob0, hob0, holen0⟩ := fc0
  change chain.offsetInBits + 768 ≤ ob0.lengthInBits at holen0
  peel_load (.bitvec (.concrete 64)), ob0, chain, hob0, after
  rw [← word_live after.mem chain ob0 hob0]
  denote_step_reduce v 45 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv45
  subst hv45
  peel_store (bswapBV (word after.mem chain)), o, ho, after
  obtain ⟨out1, hout1⟩ : ∃ t : GlobalState, {after with mem := after.mem.splice o (bswapBV (word after.mem chain))} = t := ⟨_, rfl⟩
  rw [hout1]
  have hm1 : out1.mem = outputStep after.mem p o 0 := by
    rw [← hout1]
    simp [outputStep, chain, Pointer.withOffset]
  have fc1 : Fits out1.mem p (224*8) := hout1 ▸ fits_splice hc
  have fo1 : Fits out1.mem o (64*8) := hout1 ▸ fits_splice ho
  peel_gep 136 with p, fc1, out1 as cp1
  obtain ⟨ob1, hob1, holen1⟩ := hcp1
  change cp1.offsetInBits + 704 ≤ ob1.lengthInBits at holen1
  peel_load (.bitvec (.concrete 64)), ob1, cp1, hob1, out1
  rw [← word_live out1.mem cp1 ob1 hob1]
  denote_step_reduce v 48 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv48
  subst hv48
  peel_gep 8 with o, fo1, out1 as op1
  peel_store (bswapBV (word out1.mem cp1)), op1, hop1, out1
  obtain ⟨out2, hout2⟩ : ∃ t : GlobalState, {out1 with mem := out1.mem.splice op1 (bswapBV (word out1.mem cp1))} = t := ⟨_, rfl⟩
  rw [hout2]
  have hm2 : out2.mem = outputStep out1.mem p o 1 := by
    rw [← hout2]
    simp [outputStep, cp1, op1, Pointer.withOffset]
  have fc2 : Fits out2.mem p (224*8) := hout2 ▸ fits_splice fc1
  have fo2 : Fits out2.mem o (64*8) := hout2 ▸ fits_splice fo1
  peel_gep 144 with p, fc2, out2 as cp2
  obtain ⟨ob2, hob2, holen2⟩ := hcp2
  change cp2.offsetInBits + 640 ≤ ob2.lengthInBits at holen2
  peel_load (.bitvec (.concrete 64)), ob2, cp2, hob2, out2
  rw [← word_live out2.mem cp2 ob2 hob2]
  denote_step_reduce v 52 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv52
  subst hv52
  peel_gep 16 with o, fo2, out2 as op2
  peel_store (bswapBV (word out2.mem cp2)), op2, hop2, out2
  obtain ⟨out3, hout3⟩ : ∃ t : GlobalState, {out2 with mem := out2.mem.splice op2 (bswapBV (word out2.mem cp2))} = t := ⟨_, rfl⟩
  rw [hout3]
  have hm3 : out3.mem = outputStep out2.mem p o 2 := by
    rw [← hout3]
    simp [outputStep, cp2, op2, Pointer.withOffset]
  have fc3 : Fits out3.mem p (224*8) := hout3 ▸ fits_splice fc2
  have fo3 : Fits out3.mem o (64*8) := hout3 ▸ fits_splice fo2
  peel_gep 152 with p, fc3, out3 as cp3
  obtain ⟨ob3, hob3, holen3⟩ := hcp3
  change cp3.offsetInBits + 576 ≤ ob3.lengthInBits at holen3
  peel_load (.bitvec (.concrete 64)), ob3, cp3, hob3, out3
  rw [← word_live out3.mem cp3 ob3 hob3]
  denote_step_reduce v 56 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv56
  subst hv56
  peel_gep 24 with o, fo3, out3 as op3
  peel_store (bswapBV (word out3.mem cp3)), op3, hop3, out3
  obtain ⟨out4, hout4⟩ : ∃ t : GlobalState, {out3 with mem := out3.mem.splice op3 (bswapBV (word out3.mem cp3))} = t := ⟨_, rfl⟩
  rw [hout4]
  have hm4 : out4.mem = outputStep out3.mem p o 3 := by
    rw [← hout4]
    simp [outputStep, cp3, op3, Pointer.withOffset]
  have fc4 : Fits out4.mem p (224*8) := hout4 ▸ fits_splice fc3
  have fo4 : Fits out4.mem o (64*8) := hout4 ▸ fits_splice fo3
  peel_gep 160 with p, fc4, out4 as cp4
  obtain ⟨ob4, hob4, holen4⟩ := hcp4
  change cp4.offsetInBits + 512 ≤ ob4.lengthInBits at holen4
  peel_load (.bitvec (.concrete 64)), ob4, cp4, hob4, out4
  rw [← word_live out4.mem cp4 ob4 hob4]
  denote_step_reduce v 60 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv60
  subst hv60
  peel_gep 32 with o, fo4, out4 as op4
  peel_store (bswapBV (word out4.mem cp4)), op4, hop4, out4
  obtain ⟨out5, hout5⟩ : ∃ t : GlobalState, {out4 with mem := out4.mem.splice op4 (bswapBV (word out4.mem cp4))} = t := ⟨_, rfl⟩
  rw [hout5]
  have hm5 : out5.mem = outputStep out4.mem p o 4 := by
    rw [← hout5]
    simp [outputStep, cp4, op4, Pointer.withOffset]
  have fc5 : Fits out5.mem p (224*8) := hout5 ▸ fits_splice fc4
  have fo5 : Fits out5.mem o (64*8) := hout5 ▸ fits_splice fo4
  peel_gep 168 with p, fc5, out5 as cp5
  obtain ⟨ob5, hob5, holen5⟩ := hcp5
  change cp5.offsetInBits + 448 ≤ ob5.lengthInBits at holen5
  peel_load (.bitvec (.concrete 64)), ob5, cp5, hob5, out5
  rw [← word_live out5.mem cp5 ob5 hob5]
  denote_step_reduce v 64 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv64
  subst hv64
  peel_gep 40 with o, fo5, out5 as op5
  peel_store (bswapBV (word out5.mem cp5)), op5, hop5, out5
  obtain ⟨out6, hout6⟩ : ∃ t : GlobalState, {out5 with mem := out5.mem.splice op5 (bswapBV (word out5.mem cp5))} = t := ⟨_, rfl⟩
  rw [hout6]
  have hm6 : out6.mem = outputStep out5.mem p o 5 := by
    rw [← hout6]
    simp [outputStep, cp5, op5, Pointer.withOffset]
  have fc6 : Fits out6.mem p (224*8) := hout6 ▸ fits_splice fc5
  have fo6 : Fits out6.mem o (64*8) := hout6 ▸ fits_splice fo5
  peel_gep 176 with p, fc6, out6 as cp6
  obtain ⟨ob6, hob6, holen6⟩ := hcp6
  change cp6.offsetInBits + 384 ≤ ob6.lengthInBits at holen6
  peel_load (.bitvec (.concrete 64)), ob6, cp6, hob6, out6
  rw [← word_live out6.mem cp6 ob6 hob6]
  denote_step_reduce v 68 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv68
  subst hv68
  peel_gep 48 with o, fo6, out6 as op6
  peel_store (bswapBV (word out6.mem cp6)), op6, hop6, out6
  obtain ⟨out7, hout7⟩ : ∃ t : GlobalState, {out6 with mem := out6.mem.splice op6 (bswapBV (word out6.mem cp6))} = t := ⟨_, rfl⟩
  rw [hout7]
  have hm7 : out7.mem = outputStep out6.mem p o 6 := by
    rw [← hout7]
    simp [outputStep, cp6, op6, Pointer.withOffset]
  have fc7 : Fits out7.mem p (224*8) := hout7 ▸ fits_splice fc6
  have fo7 : Fits out7.mem o (64*8) := hout7 ▸ fits_splice fo6
  peel_gep 184 with p, fc7, out7 as cp7
  obtain ⟨ob7, hob7, holen7⟩ := hcp7
  change cp7.offsetInBits + 320 ≤ ob7.lengthInBits at holen7
  peel_load (.bitvec (.concrete 64)), ob7, cp7, hob7, out7
  rw [← word_live out7.mem cp7 ob7 hob7]
  denote_step_reduce v 72 [bswap_value]
  simp -failIfUnchanged only [simp_denote, simp_sllvm] at hv72
  subst hv72
  peel_gep 56 with o, fo7, out7 as op7
  peel_store (bswapBV (word out7.mem cp7)), op7, hop7, out7
  obtain ⟨out8, hout8⟩ : ∃ t : GlobalState, {out7 with mem := out7.mem.splice op7 (bswapBV (word out7.mem cp7))} = t := ⟨_, rfl⟩
  rw [hout8]
  have hm8 : out8.mem = outputStep out7.mem p o 7 := by
    rw [← hout8]
    simp [outputStep, cp7, op7, Pointer.withOffset]
  have hmfinal : out8.mem = outputMemory after.mem p o := by
    simp only [outputMemory, ← hm1, ← hm2, ← hm3, ← hm4, ← hm5, ← hm6, ← hm7, ← hm8]
  have hafinal : out8.alloc = after.alloc := by
    simp only [← hout8, ← hout7, ← hout6, ← hout5, ← hout4, ← hout3, ← hout2, ← hout1]
  have hgfinal : out8.globals = after.globals := by
    simp only [← hout8, ← hout7, ← hout6, ← hout5, ← hout4, ← hout3, ← hout2, ← hout1]
  have hfinal : out8 = {after with mem := outputMemory after.mem p o} :=
    global_eq _ _ hafinal hmfinal hgfinal
  simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm, hfinal]

end FinishExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
