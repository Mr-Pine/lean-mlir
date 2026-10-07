/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_wnaf
public import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_int_min
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_curve25519_scalar_wnaf` returns, writing the scalar's digits at `slides`

The region loops, so the proof is `Blocks.run_of_variant`: every block keeps `Reach` and steps
to a value, and `μ` drops along every edge.

`Reach` has one constructor per tail block. Each says the state is the entry state with some
`w : BitVec 4096` spliced at `slides` (`Sw`), and pins what the next stores, branches and shifts
need: the indices as small naturals, every other register a value, and the sentinel

    slot w 255 = 0 ∨ i = 255

at the outer loop head. That disjunction is the C comment's argument made checkable: the carry
scan in `^bb14`/`^bb18` only continues past a set entry, and entry 255 is clear whenever
`i < 255`, so every index it stores through stays at most 255. The outer index `m` stays at
most the inner one, which keeps `fd_int_min`'s argument non-negative (so `1 << min(j-i, 14)` is
a value) and makes the outer loop advance.

`Reach` also carries the digits' shape: every entry written so far is zero or odd and within
`±2 ^ bits` (`BndUpTo`), and the running digit `ti` satisfies `Ti`, which `^bb11`/`^bb13`
preserve against `%43 = max` and `%45 = -max` (`K`). Under `Hyp` (`bits ≤ 13`, `slides` and `n`
apart) each constructor's `hI` adds the digit sum; see "The digits".
-/

@[expose] public section

namespace Firedancer.Common

open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace Wnaf

/-! ## The buffer model

Every state the walk reaches is the entry state with some 4096 bits `w` at
`slides`; `slot w k` is entry `k` of them. -/

/-- The entry state with `w` written over the 256 entries at `slides`. -/
abbrev Sw (s : GlobalState) (slides : Pointer) (w : BitVec 4096) : GlobalState :=
  { s with mem := s.mem.splice slides w }

/-- Entry `k` of the buffer. -/
def slot (w : BitVec 4096) (k : Nat) : BitVec 16 := w.extractLsb' (16 * k) 16

/-- `slides + 2k`, the pointer `getelementptr i16` computes for entry `k`. -/
def slotPtr (slides : Pointer) (k : Nat) : Pointer :=
  { slides with offset := slides.offset + BitVec.ofNat 64 (2 * k) }

theorem slotPtr_offsetInBits {slides : Pointer} {k : Nat}
    (h : slides.offset.toNat + 512 ≤ 2 ^ 64) (hk : k < 256) :
    (slotPtr slides k).offsetInBits = slides.offsetInBits + 16 * k := by
  simp only [slotPtr, Pointer.offsetInBits, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 2 * k) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- A store into the buffer is a store into `w`. -/
theorem spliceBits_slot {n : Nat} (b : BitVec n) (off k : Nat) (hk : k < 256)
    (w : BitVec 4096) (x : BitVec 16) :
    spliceBits (spliceBits b off w) (off + 16 * k) x = spliceBits b off (spliceBits w (16 * k) x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_spliceBits]
  by_cases h1 : off + 16 * k ≤ i ∧ i < off + 16 * k + 16 ∧ i < n
  · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
    congr 1; omega
  · rw [if_neg h1]
    by_cases h2 : off ≤ i ∧ i < off + 4096 ∧ i < n
    · rw [if_pos h2, if_pos h2, if_neg (by omega)]
    · rw [if_neg h2, if_neg h2]

/-- ... and reading entry `k` back reads `w`. -/
theorem extract_spliceBits_slot {n : Nat} (b : BitVec n) (off k : Nat) (hk : k < 256)
    (hn : off + 4096 ≤ n) (w : BitVec 4096) :
    (spliceBits b off w).extractLsb' (off + 16 * k) 16 = slot w k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [slot, BitVec.getLsbD_extractLsb', getLsbD_spliceBits, hi, decide_true,
    Bool.true_and]
  rw [if_pos (by omega)]
  congr 1; omega

theorem slot_spliceBits (w : BitVec 4096) (x : BitVec 16) {j k : Nat} (hj : j < 256) (hk : k < 256) :
    slot (spliceBits w (16 * k) x) j = if j = k then x else slot w j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hjk : j = k
  · subst hjk
    simp only [slot, if_true, BitVec.getLsbD_extractLsb', getLsbD_spliceBits, hi, decide_true,
      Bool.true_and]
    rw [if_pos (by omega)]
    congr 1; omega
  · simp only [slot, hjk, if_false, BitVec.getLsbD_extractLsb', getLsbD_spliceBits, hi,
      decide_true, Bool.true_and]
    rw [if_neg (by omega)]

variable {s u : GlobalState} {slides : Pointer} {w : BitVec 4096}

/-- `u`'s block at `slides`, given the entry block. -/
theorem live?_slides (hu : u ≈ Sw s slides w) {blk : LiveBlock} (hblk : s.mem.live? slides.id = some blk) :
    u.mem.live? slides.id = some { length := blk.length, bytes := spliceBits blk.bytes slides.offsetInBits w } :=
  (hu.live slides.id).trans (splicedLive s.mem slides blk hblk w)

/-- Storing entry `k` moves the buffer model from `w` to `w` with entry `k` replaced. -/
theorem store_slot_equiv (hoff : slides.offset.toNat + 512 ≤ 2 ^ 64) (hu : u ≈ Sw s slides w)
    {k : Nat} (hk : k < 256) (x : BitVec 16) :
    ({ u with mem := u.mem.splice (slotPtr slides k) x } : GlobalState)
      ≈ Sw s slides (spliceBits w (16 * k) x) := by
  refine GlobalState.Equiv.trans (splice_equiv (p := slotPtr slides k) (x := x) hu) ⟨rfl, rfl, fun q => ?_⟩
  show ((s.mem.splice slides w).splice (slotPtr slides k) x).live? q
    = (s.mem.splice slides (spliceBits w (16 * k) x)).live? q
  by_cases hq : slides.id = q
  · subst hq
    show ((s.mem.splice slides w).splice (slotPtr slides k) x).live? (slotPtr slides k).id = _
    cases hb : s.mem.live? slides.id with
    | none =>
        rw [splicedDead (m := s.mem.splice slides w) (p := slotPtr slides k) (splicedDead hb),
          splicedDead hb]
    | some b =>
        rw [splicedLive _ (slotPtr slides k) _ (splicedLive s.mem slides b hb w) x,
          splicedLive s.mem slides b hb, slotPtr_offsetInBits hoff hk, spliceBits_slot _ _ _ hk]
  · rw [live?_splice_ne (p := slotPtr slides k) hq, live?_splice_ne (p := slides) hq,
      live?_splice_ne (p := slides) hq]

/-- Entry `k` fits in every state the walk reaches. -/
theorem fits_slot (hsl : IsSlidesPtr s.mem slides) (hu : u ≈ Sw s slides w) {k : Nat} (hk : k < 256) :
    Fits u.mem (slotPtr slides k) 16 := by
  obtain ⟨blk, hblk, hlen⟩ := hsl.1
  have hl : s.mem.live? slides.id = some blk := by simp [MemoryState.live?, hblk]
  refine ⟨{ length := blk.length, bytes := spliceBits blk.bytes slides.offsetInBits w },
    getElem?_of_live? (live?_slides hu hl), ?_⟩
  simp only [LiveBlock.lengthInBits] at hlen ⊢
  rw [slotPtr_offsetInBits hsl.2 hk]
  omega

/-- Loading entry `k` reads `slot w k`. -/
theorem run_load_slot (hsl : IsSlidesPtr s.mem slides) (hu : u ≈ Sw s slides w) {k : Nat}
    (hk : k < 256) :
    (load (.value (slotPtr slides k)) (.bitvec (.concrete 16))).run u.mem
      = .value (.value (slot w k), u.mem) := by
  obtain ⟨blk, hblk, hlen⟩ := hsl.1
  have hl : s.mem.live? slides.id = some blk := by simp [MemoryState.live?, hblk]
  simp only [LiveBlock.lengthInBits] at hlen
  rw [run_load (p := slotPtr slides k) (getElem?_of_live? (live?_slides hu hl))
    (by simp only [LiveBlock.lengthInBits, LLVM.Ty.width]; rw [slotPtr_offsetInBits hsl.2 hk]; omega)]
  simp only [LLVM.Ty.unflatten, LLVM.Ty.width]
  rw [slotPtr_offsetInBits hsl.2 hk, extract_spliceBits_slot _ _ _ hk (by omega)]

/-- Storing entry `k`. -/
theorem run_store_slot (hsl : IsSlidesPtr s.mem slides) (hu : u ≈ Sw s slides w) {k : Nat}
    (hk : k < 256) (x : BitVec 16) :
    (store (.value (slotPtr slides k)) (.bitvec (.concrete 16)) (.value x)).run u.mem
      = .value ((), u.mem.splice (slotPtr slides k) x) :=
  run_store rfl (fits_slot hsl hu hk)

/-! ## The scalar's bytes -/

/-- Byte `j` of `n`. -/
def bytePtr (n : Pointer) (j : Nat) : Pointer :=
  { n with offset := n.offset + BitVec.ofNat 64 j }

theorem gep_byte (p : Pointer) (j : Nat) :
    gep (PoisonOr.value p) 1 0 (PoisonOr.value (BitVec.ofNat 64 j)) = PoisonOr.value (bytePtr p j) := by
  simp only [gep, ptradd, LLVM.mul, LLVM.add, LLVM.const?, LLVM.mul?, LLVM.add?, bytePtr,
    PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  rw [show (BitVec.ofInt 64 ((1 : Nat) : Int)) = 1#64 from rfl,
    show (BitVec.ofInt 64 ((0 : Nat) : Int)) = 0#64 from rfl]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- Loading byte `j < 32` of `n` returns, in every state the walk reaches. -/
theorem run_load_byte {s u : GlobalState} {slides n : Pointer} {w : BitVec 4096}
    (hn : IsByteBufPtr s.mem n) (hu : u ≈ Sw s slides w)
    {j : Nat} (hj : j < 32) :
    ∃ b, (slides.id ≠ n.id → b = (readBuf hn).extractLsb' (8 * j) 8)
      ∧ (load (.value (bytePtr n j)) (.bitvec (.concrete 8))).run u.mem = .value (.value b, u.mem) := by
  obtain ⟨blk, hblk, hlen⟩ := fits_of_live?_eq (m := (Sw s slides w).mem) (hu.live n.id)
    (fits_splice hn.1)
  have hoff : (bytePtr n j).offsetInBits = n.offsetInBits + 8 * j := by
    simp only [bytePtr, Pointer.offsetInBits, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [run_load (p := bytePtr n j) hblk (by simp only [LLVM.Ty.width]; omega)]
  refine ⟨_, fun hne => ?_, rfl⟩
  have hl : u.mem.live? n.id = s.mem.live? n.id := (hu.live n.id).trans (live?_splice_ne hne)
  rw [show u.mem.live? n.id = some blk by simp [MemoryState.live?, hblk]] at hl
  simp only [LLVM.Ty.width, readBuf, readBuf?, ← hl, Option.get_some,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hoff, hi, decide_true, Bool.true_and]
  simp only [show 8 * j + i < 256 by omega, decide_true, Bool.true_and, Nat.add_assoc]

/-! ## Stepping a tail block

The stepper's impure-instruction lemmas carry the `>>= k` an entry block sits
under; a tail block is walked on its own. -/

private theorem nil_append' {Γ : Ctxt SLLVM.Ty} (V : Γ.Valuation) :
    ((.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)) ++ V) = V := by
  show (Ctxt.Valuation.ofHVector
      (.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty))) ++ V = V
  simp only [Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.nil_append]

/-- A store in a tail block, given that it succeeds. -/
theorem run_denote_var_of_nil {Γ Γout : Ctxt SLLVM.Ty} {rets succs}
    {e : Expr SLLVM Γ .impure []}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {s s' : GlobalState}
    (h : StateT.run (e.denoteOp V) s = .value (.nil, s')) :
    StateT.run ((BlockCom.var e body).denote V) s = StateT.run (body.denote V) s' := by
  rw [BlockCom.denote_var, Expr.denote_unfold,
    EffectM.run_bind_of_value
      (a := (HVector.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)) ++ V) (s' := s')
      (by rw [EffectM.run_map, h]; rfl),
    nil_append']

/-- `getelementptr i16, slides, k` is entry `k`. -/
theorem gep_slot (p : Pointer) (k : Nat) :
    gep (PoisonOr.value p) 2 0 (PoisonOr.value (BitVec.ofNat 64 k)) = PoisonOr.value (slotPtr p k) := by
  simp only [gep, ptradd, LLVM.mul, LLVM.add, LLVM.const?, LLVM.mul?, LLVM.add?, slotPtr,
    PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  rw [show (BitVec.ofInt 64 ((2 : Nat) : Int)) = 2#64 from rfl,
    show (BitVec.ofInt 64 ((0 : Nat) : Int)) = 0#64 from rfl]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- A block that ends in `llvm.br`. -/
theorem term_br {Γ : Ctxt SLLVM.Ty} {rets succs} {tgt : Target Γ succs} {V : Γ.Valuation}
    {u : GlobalState} {P : _ → GlobalState → Prop}
    (h : P (V, (.inr (tgt.denote V) : HVector toType rets ⊕ SuccArgs succs)) u) :
    ∃ p u', StateT.run ((BlockCom.term (.br tgt) : BlockCom Γ Γ rets succs).denote V) u
      = .value (p, u') ∧ P p u' :=
  ⟨_, _, rfl, h⟩

/-- A block that ends in `llvm.cond_br` on a value. -/
theorem term_condBr {Γ : Ctxt SLLVM.Ty} {rets succs} {c : Γ.Var (SLLVM.Ty.bitvec 1)}
    {tT tF : Target Γ succs} {V : Γ.Valuation} {u : GlobalState} {P : _ → GlobalState → Prop}
    {b : BitVec 1} (hc : V c = .value b)
    (h : P (V, (.inr ((if b = 1 then tT else tF).denote V) : HVector toType rets ⊕ SuccArgs succs)) u) :
    ∃ p u', StateT.run ((BlockCom.term (.condBr c tT tF) : BlockCom Γ Γ rets succs).denote V) u
      = .value (p, u') ∧ P p u' :=
  ⟨(V, .inr ((if b = 1 then tT else tF).denote V)), u,
    by simp [BlockCom.denote_term, Terminator.denote_condBr_value hc], h⟩

/-- A block that ends in `llvm.return`. -/
theorem term_ret {Γ : Ctxt SLLVM.Ty} {succs} {V : Γ.Valuation}
    {u : GlobalState} {P : _ → GlobalState → Prop}
    (h : P (V, (.inl .nil : HVector toType [] ⊕ SuccArgs succs)) u) :
    ∃ p u', StateT.run ((BlockCom.term (.ret .nil) : BlockCom Γ Γ [] succs).denote V) u
      = .value (p, u') ∧ P p u' :=
  ⟨_, _, rfl, h⟩

/-! ## Register arithmetic on small naturals

Every index the region computes stays far below any wrap, so it is carried as
`BitVec.ofNat w k` and these fold its operations. -/

theorem add64 {a b : Nat} (f : LLVM.NoWrapFlags) (h : a + b < 2 ^ 63) :
    LLVM.add (PoisonOr.value (BitVec.ofNat 64 a)) (PoisonOr.value (BitVec.ofNat 64 b)) f
      = PoisonOr.value (BitVec.ofNat 64 (a + b)) := by
  have hs : BitVec.saddOverflow (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = false := by
    simp only [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> simp <;> omega
  have hu : BitVec.uaddOverflow (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = false := by
    simp only [BitVec.uaddOverflow, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp; omega
  simp only [LLVM.add, LLVM.add?, PoisonOr.value_bind, hs, hu, Bool.false_eq_true, and_false,
    if_false]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add32 {a b : Nat} (f : LLVM.NoWrapFlags) (h : a + b < 2 ^ 31) :
    LLVM.add (PoisonOr.value (BitVec.ofNat 32 a)) (PoisonOr.value (BitVec.ofNat 32 b)) f
      = PoisonOr.value (BitVec.ofNat 32 (a + b)) := by
  have hs : BitVec.saddOverflow (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = false := by
    simp only [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> simp <;> omega
  have hu : BitVec.uaddOverflow (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = false := by
    simp only [BitVec.uaddOverflow, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp; omega
  simp only [LLVM.add, LLVM.add?, PoisonOr.value_bind, hs, hu, Bool.false_eq_true, and_false,
    if_false]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem trunc32 {a : Nat} (_h : a < 2 ^ 32) :
    LLVM.trunc 32 (PoisonOr.value (BitVec.ofNat 64 a)) = PoisonOr.value (BitVec.ofNat 32 a) := by
  simp only [LLVM.trunc, LLVM.trunc?, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sext64 {a : Nat} (h : a < 2 ^ 31) :
    LLVM.sext 64 (PoisonOr.value (BitVec.ofNat 32 a)) = PoisonOr.value (BitVec.ofNat 64 a) := by
  simp only [LLVM.sext, LLVM.sext?, PoisonOr.value_bind]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_ofNat, BitVec.msb_eq_getLsbD_last]
  by_cases hi32 : i < 32
  · simp [hi32, hi]
  · simp [hi32, hi]
    rw [Nat.testBit_lt_two_pow (show a < 2 ^ 31 from h),
      Nat.testBit_lt_two_pow (show a < 2 ^ i from
        lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem icmp_eq_ofNat {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    LLVM.icmp .eq (PoisonOr.value (BitVec.ofNat w a)) (PoisonOr.value (BitVec.ofNat w b))
      = PoisonOr.value (BitVec.ofBool (decide (a = b))) := by
  simp only [LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind]
  congr 2
  by_cases hab : a = b
  · subst hab; simp
  · simp only [hab, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact hab this

theorem icmp_slt32 {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    LLVM.icmp .slt (PoisonOr.value (BitVec.ofNat 32 a)) (PoisonOr.value (BitVec.ofNat 32 b))
      = PoisonOr.value (BitVec.ofBool (decide (a < b))) := by
  simp only [LLVM.icmp, LLVM.icmp?_slt_eq, PoisonOr.value_bind]
  congr 2
  simp only [BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, decide_eq_decide]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  split_ifs <;> omega

theorem ofBool_eq_one {p : Prop} [Decidable p] : BitVec.ofBool (decide p) = (1 : BitVec 1) ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ofBool_beq_one {w : Nat} {x y : BitVec w} : BitVec.ofBool (x == y) = (1 : BitVec 1) ↔ x = y := by
  by_cases h : x = y
  · simp [h]
  · have hb : (x == y) = false := by simpa using h
    simp [h, hb]

/-! ## Registers that are never poison -/

theorem shl_m1 {bits : BitVec 32} (h : bits.toNat < 32) :
    LLVM.shl (PoisonOr.value 4294967295#32) (PoisonOr.value bits) { nsw := true }
      = PoisonOr.value (4294967295#32 <<< bits) := by
  have hb : bits < 32#32 := by simp [BitVec.lt_def]; omega
  have hinv : (4294967295#32 <<< bits).sshiftRight' bits = 4294967295#32 := by
    have hbits : bits = BitVec.ofNat 32 bits.toNat := by simp
    rw [hbits]
    generalize bits.toNat = n at h ⊢
    interval_cases n <;> decide +kernel
  simp only [LLVM.shl, LLVM.shl?, PoisonOr.value_bind]
  split_ifs with h1 h2 h3
  · exact absurd hinv h1.2
  · exact absurd h2.1 (by decide)
  · have hge : 32 ≤ bits.toNat := by simpa [ge_iff_le, BitVec.le_def] using h3
    omega
  · rfl

theorem sub_ashr_value (y : BitVec 32) :
    ∃ a, a = 0#32 - (y <<< 16#32).sshiftRight' 16#32 ∧ LLVM.sub (PoisonOr.value 0#32)
      (LLVM.ashr (LLVM.shl (PoisonOr.value y) (PoisonOr.value 16#32)) (PoisonOr.value 16#32))
      { nsw := true } = PoisonOr.value a := by
  have h : BitVec.ssubOverflow 0#32 ((y <<< 16#32).sshiftRight' 16#32) = false := by
    have hlo := BitVec.le_toInt (y <<< 16#32)
    have hhi := BitVec.toInt_lt (x := y <<< 16#32)
    simp only [BitVec.ssubOverflow, BitVec.toInt_zero, BitVec.toInt_sshiftRight',
      Int.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    norm_num at hlo hhi ⊢
    omega
  have h32 : ¬ (16#32 ≥ ((32 : Nat) : BitVec 32)) := by decide
  simp only [LLVM.shl, LLVM.shl?, LLVM.ashr, LLVM.ashr?, PoisonOr.value_bind]
  simp only [LLVM.sub, LLVM.sub?, Bool.false_eq_true, false_and, if_false, h32, h, and_false,
    PoisonOr.value_bind]
  exact ⟨_, rfl, rfl⟩

theorem idx_n {k : Nat} (hk : k < 256) :
    LLVM.and (LLVM.lshr (PoisonOr.value (BitVec.ofNat 64 k)) (PoisonOr.value 3#64))
      (PoisonOr.value 536870911#64) = PoisonOr.value (BitVec.ofNat 64 (k / 8)) := by
  have h64 : ¬ (3#64 ≥ ((64 : Nat) : BitVec 64)) := by decide
  simp only [LLVM.and, LLVM.lshr, LLVM.lshr?, LLVM.and?, PoisonOr.value_bind, Bool.false_eq_true,
    false_and, if_false, h64]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [show (536870911 : Nat) % 2 ^ 64 = 2 ^ 29 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem ashr_shl_value (y a : BitVec 32) (ha : ¬ (a ≥ ((32 : Nat) : BitVec 32))) :
    ∃ z, z = (y <<< 16#32).sshiftRight' a ∧ LLVM.ashr (LLVM.shl (PoisonOr.value y) (PoisonOr.value 16#32)) (PoisonOr.value a)
      = PoisonOr.value z := by
  have h32 : ¬ (16#32 ≥ ((32 : Nat) : BitVec 32)) := by decide
  simp only [LLVM.shl, LLVM.shl?, LLVM.ashr, LLVM.ashr?, PoisonOr.value_bind, Bool.false_eq_true,
    false_and, if_false, h32, ha]
  exact ⟨_, rfl, rfl⟩

theorem sub32 {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    LLVM.sub (PoisonOr.value (BitVec.ofNat 32 a)) (PoisonOr.value (BitVec.ofNat 32 b))
      = PoisonOr.value (BitVec.ofNat 32 (a - b)) := by
  simp only [LLVM.sub, LLVM.sub?, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem smin14 {d : Nat} (hd : d < 2 ^ 31) :
    SLLVM.smin (PoisonOr.value (BitVec.ofNat 32 d)) (PoisonOr.value 14#32)
      = PoisonOr.value (BitVec.ofNat 32 (min d 14)) := by
  simp only [SLLVM.smin_value]
  congr 1
  split_ifs with h
  · rw [Nat.min_eq_left]
    simp only [BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, decide_eq_true_eq] at h
    split_ifs at h <;> omega
  · have h14 : 14 ≤ d := by
      simp only [BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, decide_eq_true_eq] at h
      split_ifs at h <;> omega
    rw [Nat.min_eq_right h14]

theorem delta_exact {e : Nat} (he : e ≤ 14) :
    (65536#32 <<< BitVec.ofNat 32 e).sshiftRight' 16#32 = BitVec.ofNat 32 (2 ^ e) := by
  interval_cases e <;> decide

theorem delta_le {e : Nat} (he : e ≤ 14) (he1 : 1 ≤ e) :
    (65536#32 <<< BitVec.ofNat 32 e).sshiftRight' 16#32 ≤ 16384#32
      ∧ (65536#32 <<< BitVec.ofNat 32 e).sshiftRight' 16#32 &&& 1#32 = 0#32 := by
  interval_cases e <;> first | omega | decide +kernel

theorem delta_value {e : Nat} (he : e ≤ 14) (he1 : 1 ≤ e) :
    ∃ z, (z ≤ 16384#32 ∧ z &&& 1#32 = 0#32) ∧ z = BitVec.ofNat 32 (2 ^ e) ∧ LLVM.ashr (LLVM.shl (PoisonOr.value 65536#32) (PoisonOr.value (BitVec.ofNat 32 e)))
      (PoisonOr.value 16#32) = PoisonOr.value z := by
  have h1 : ¬ (BitVec.ofNat 32 e ≥ ((32 : Nat) : BitVec 32)) := by
    rw [show ((32 : Nat) : BitVec 32) = 32#32 from rfl]
    simp only [ge_iff_le, BitVec.le_def, BitVec.toNat_ofNat, not_le]
    omega
  have h32 : ¬ (16#32 ≥ ((32 : Nat) : BitVec 32)) := by decide
  simp only [LLVM.shl, LLVM.shl?, LLVM.ashr, LLVM.ashr?, PoisonOr.value_bind, Bool.false_eq_true,
    false_and, if_false, h1, h32]
  exact ⟨_, delta_le he he1, delta_exact he, rfl⟩

/-! ## The bound

Every entry the region stores is `0`, `1`, a bit, or the running digit `ti`. `Ti` bounds `ti`
and records oddness, since every `delta` is even; `Ti.bnd` turns it into the
spec's form. -/

/-- The spec's fact about an entry: zero or odd, and `|x| ≤ 2 ^ bits`. -/
abbrev Bnd (bits : BitVec 32) (x : BitVec 16) : Prop :=
  (x = 0 ∨ x.toInt % 2 = 1) ∧ x.toInt.natAbs ≤ 2 ^ bits.toNat

/-- Entries below `k` are in bound. -/
abbrev BndUpTo (bits : BitVec 32) (w : BitVec 4096) (k : Nat) : Prop :=
  ∀ j < k, Bnd bits (slot w j)

theorem BndUpTo.store {bits : BitVec 32} {w : BitVec 4096} {k k' i : Nat} {x : BitVec 16}
    (h : BndUpTo bits w k) (hx : Bnd bits x) (hi : i < 256)
    (hk : ∀ j < k', j = i ∨ (j < k ∧ j < 256)) : BndUpTo bits (spliceBits w (16 * i) x) k' :=
  fun j hj => by
    have hj' := hk j hj
    rw [slot_spliceBits _ _ (by omega) hi]
    split_ifs with he
    · exact hx
    · exact h j (hj'.resolve_left he).1

theorem BndUpTo.store256 {bits : BitVec 32} {w : BitVec 4096} {i : Nat} {x : BitVec 16}
    (h : BndUpTo bits w 256) (hx : Bnd bits x) (hi : i < 256) :
    BndUpTo bits (spliceBits w (16 * i) x) 256 :=
  h.store hx hi fun _ hj => Or.inr ⟨hj, hj⟩

theorem bnd_zero {bits : BitVec 32} : Bnd bits 0#16 :=
  ⟨Or.inl rfl, by simp only [BitVec.toInt_zero, Int.natAbs_zero]; exact Nat.zero_le _⟩

theorem bnd_one {bits : BitVec 32} : Bnd bits 1#16 :=
  ⟨Or.inr (by decide), by simp only [show (1#16).toInt = 1 by decide]; exact Nat.one_le_two_pow⟩

theorem bnd_of_bit {bits : BitVec 32} {x : BitVec 16} (h : x = 0#16 ∨ x = 1#16) : Bnd bits x := by
  rcases h with rfl | rfl
  · exact bnd_zero
  · exact bnd_one

/-- `%19`, the C's `max`, as `^bb1` computes it. -/
abbrev Y19 (bits y19 : BitVec 32) : Prop := y19 = 4294967295#32 <<< bits ^^^ 4294967295#32

/-- `%43 = (short)max`, `%44 = 2 * %43` and `%45 = -%43`. -/
abbrev K (bits y43 y44 y45 : BitVec 32) : Prop :=
  y43 = ((4294967295#32 <<< bits ^^^ 4294967295#32) <<< 16#32).sshiftRight' 16#32
    ∧ y44 = ((4294967295#32 <<< bits ^^^ 4294967295#32) <<< 16#32).sshiftRight' 15#32
    ∧ y45 = 0#32 - y43

/-- The running digit: odd, and `1` or strictly inside `±2 ^ bits`; past `bits = 14` every
`short` is in bound. -/
def Ti (bits : BitVec 32) (y : BitVec 16) : Prop :=
  y &&& 1#16 = 1#16 ∧ (14#32 < bits ∨ y = 1#16
    ∨ ((y.signExtend 32).slt (1#32 <<< bits) ∧ (0#32 - 1#32 <<< bits).slt (y.signExtend 32)))

theorem ti_one {bits : BitVec 32} : Ti bits 1#16 := ⟨by decide, Or.inr (Or.inl rfl)⟩

theorem trunc_le {y : BitVec 32} (h : y ≤ 16384#32 ∧ y &&& 1#32 = 0#32) :
    y.truncate 16 ≤ 16384#16 ∧ y.truncate 16 &&& 1#16 = 0#16 := by
  obtain ⟨h1, h2⟩ := h
  have hy : y.toNat ≤ 16384 := h1
  constructor
  · change (y.setWidth 16).toNat ≤ 16384
    rw [BitVec.toNat_setWidth]
    omega
  · apply BitVec.eq_of_toNat_eq
    have hmod := congrArg BitVec.toNat h2
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
      show 1 % 2 ^ 32 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at hmod
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      show 1 % 2 ^ 16 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega

private theorem odd_add_even {x y : BitVec 16}
    (hx : x &&& 1#16 = 1#16) (hy : y &&& 1#16 = 0#16) :
    (x + y) &&& 1#16 = 1#16 := by
  apply BitVec.eq_of_toNat_eq
  have hx' := congrArg BitVec.toNat hx
  have hy' := congrArg BitVec.toNat hy
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod,
    BitVec.toNat_add] at hx' hy' ⊢
  norm_num at hx' hy' ⊢
  omega

private theorem odd_sub_even {x y : BitVec 16}
    (hx : x &&& 1#16 = 1#16) (hy : y &&& 1#16 = 0#16) :
    (x - y) &&& 1#16 = 1#16 := by
  apply BitVec.eq_of_toNat_eq
  have hx' := congrArg BitVec.toNat hx
  have hy' := congrArg BitVec.toNat hy
  have hylt := y.isLt
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod,
    BitVec.toNat_sub] at hx' hy' ⊢
  norm_num at hx' hy' ⊢
  omega

/-- The loop admits only these fifteen small shift counts. Kernel reduction
checks their constant register values; no input digit is enumerated. -/
private theorem bounded_shift_values (bits : BitVec 32) (hb : bits.toNat ≤ 14) :
    (1#32 <<< bits).toInt = (2 : Int) ^ bits.toNat ∧
    (0#32 - 1#32 <<< bits).toInt = -((2 : Int) ^ bits.toNat) ∧
    (((4294967295#32 <<< bits ^^^ 4294967295#32) <<< 16#32).sshiftRight' 16#32).toInt
      = (2 : Int) ^ bits.toNat - 1 ∧
    (0#32 - ((4294967295#32 <<< bits ^^^ 4294967295#32) <<< 16#32).sshiftRight' 16#32).toInt
      = 1 - (2 : Int) ^ bits.toNat := by
  have hbits : bits = BitVec.ofNat 32 bits.toNat := by simp
  rw [hbits]
  generalize bits.toNat = n at hb ⊢
  interval_cases n <;> decide +kernel

private theorem small_digit_toInt {y : BitVec 16} (hy : y ≤ 16384#16) :
    0 ≤ y.toInt ∧ y.toInt ≤ 16384 := by
  have hy' : y.toNat ≤ 16384 := hy
  rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  omega

private theorem ti_bounded_range {bits : BitVec 32} {y : BitVec 16}
    (h : Ti bits y) (hb : ¬14#32 < bits) :
    -((2 : Int) ^ bits.toNat) < y.toInt ∧
      (y.toInt < (2 : Int) ^ bits.toNat ∨ y.toInt = 1) := by
  have hb' : bits.toNat ≤ 14 := by simpa [BitVec.lt_def] using hb
  obtain ⟨hp, hn, _, _⟩ := bounded_shift_values bits hb'
  have hp0 : 0 < (2 : Int) ^ bits.toNat := by positivity
  rcases h.2 with hbad | hone | ⟨hhi, hlo⟩
  · exact False.elim (hb hbad)
  · subst y
    norm_num
    omega
  · simp only [BitVec.slt_iff_toInt_lt,
      BitVec.toInt_signExtend_of_le (show 16 ≤ 32 by decide), hp, hn] at hhi hlo
    exact ⟨hlo, Or.inl hhi⟩

private theorem bounded_power (bits : BitVec 32) (hb : ¬14#32 < bits) :
    1 ≤ (2 : Int) ^ bits.toNat ∧ (2 : Int) ^ bits.toNat ≤ 16384 := by
  have hb' : bits.toNat ≤ 14 := by simpa [BitVec.lt_def] using hb
  refine ⟨one_le_pow₀ (by norm_num), ?_⟩
  calc
    (2 : Int) ^ bits.toNat ≤ 2 ^ 14 := pow_le_pow_right₀ (by norm_num) hb'
    _ = 16384 := by norm_num


/-- `^bb11`'s `ti + delta`, kept when it is at most `max`. -/
theorem ti_tip {bits y43 y44 y45 y61 : BitVec 32} {y52 : BitVec 16} (hK : K bits y43 y44 y45)
    (h : Ti bits y52) (hd : y61 ≤ 16384#32 ∧ y61 &&& 1#32 = 0#32)
    (hc : ¬ BitVec.ofBool (LLVM.icmp' .slt y43 ((y52 + y61.truncate 16).signExtend 32)) = 1) :
    Ti bits (y52 + y61.truncate 16) := by
  have hdelta := trunc_le hd
  refine ⟨odd_add_even h.1 hdelta.2, ?_⟩
  by_cases hb : 14#32 < bits
  · exact Or.inl hb
  have hb' : bits.toNat ≤ 14 := by simpa [BitVec.lt_def] using hb
  have hrange := ti_bounded_range h hb
  obtain ⟨hp1, hpmax⟩ := bounded_power bits hb
  obtain ⟨hd0, hdmax⟩ := small_digit_toInt hdelta.1
  have hylo : -16384 < y52.toInt := by omega
  have hyhi : y52.toInt < 16384 := by rcases hrange.2 with hlt | heq <;> omega
  have hsum : (y52 + y61.truncate 16).toInt = y52.toInt + (y61.truncate 16).toInt :=
    BitVec.toInt_add_of_not_saddOverflow (by
      simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq]
      norm_num only
      omega)
  obtain ⟨rfl, _, rfl⟩ := hK
  obtain ⟨hp, hn, hmax, _⟩ := bounded_shift_values bits hb'
  simp only [LLVM.icmp', BitVec.slt, ofBool_eq_one,
    BitVec.toInt_signExtend_of_le (show 16 ≤ 32 by decide), hmax] at hc
  refine Or.inr (Or.inr ?_)
  simp only [BitVec.slt_iff_toInt_lt,
    BitVec.toInt_signExtend_of_le (show 16 ≤ 32 by decide), hp, hn]
  constructor <;> omega

/-- `^bb13`'s `ti - delta`, kept when it is at least `-max`. -/
theorem ti_tim {bits y43 y44 y45 : BitVec 32} {y52 y63 : BitVec 16} (hK : K bits y43 y44 y45)
    (h : Ti bits y52) (hd : y63 ≤ 16384#16 ∧ y63 &&& 1#16 = 0#16)
    (hc : ¬ BitVec.ofBool (LLVM.icmp' .slt ((y52 - y63).signExtend 32) y45) = 1) :
    Ti bits (y52 - y63) := by
  refine ⟨odd_sub_even h.1 hd.2, ?_⟩
  by_cases hb : 14#32 < bits
  · exact Or.inl hb
  have hb' : bits.toNat ≤ 14 := by simpa [BitVec.lt_def] using hb
  have hrange := ti_bounded_range h hb
  obtain ⟨hp1, hpmax⟩ := bounded_power bits hb
  obtain ⟨hd0, hdmax⟩ := small_digit_toInt hd.1
  have hylo : -16384 < y52.toInt := by omega
  have hyhi : y52.toInt < 16384 := by rcases hrange.2 with hlt | heq <;> omega
  have hsub : (y52 - y63).toInt = y52.toInt - y63.toInt :=
    BitVec.toInt_sub_of_not_ssubOverflow (by
      simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq]
      norm_num
      omega)
  obtain ⟨rfl, _, rfl⟩ := hK
  obtain ⟨hp, hn, _, hmin⟩ := bounded_shift_values bits hb'
  simp only [LLVM.icmp', BitVec.slt, ofBool_eq_one,
    BitVec.toInt_signExtend_of_le (show 16 ≤ 32 by decide), hmin] at hc
  by_cases hone : y52 - y63 = 1#16
  · exact Or.inr (Or.inl hone)
  have hne : (y52 - y63).toInt ≠ 1 := by
    intro heq
    apply hone
    exact BitVec.toInt_inj.mp heq
  refine Or.inr (Or.inr ?_)
  simp only [BitVec.slt_iff_toInt_lt,
    BitVec.toInt_signExtend_of_le (show 16 ≤ 32 by decide), hp, hn]
  rcases hrange.2 with hlt | heq <;> constructor <;> omega


theorem abs_le_of_ofNat (y : BitVec 16) (N : Nat) (hN : N ≤ 16384)
    (h1 : y.toInt < (BitVec.ofNat 32 N).toInt) (h2 : (0#32 - BitVec.ofNat 32 N).toInt < y.toInt) :
    |y.toInt| ≤ N := by
  have e1 : (BitVec.ofNat 32 N).toInt = N := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have e2 : (0#32 - BitVec.ofNat 32 N).toInt = -N := by
    rw [BitVec.zero_sub, BitVec.toInt_neg_of_ne_intMin (by
      intro h; have := congrArg BitVec.toNat h; simp at this; omega), e1]
  rw [e1] at h1; rw [e2] at h2
  rw [abs_le]; omega

theorem Ti.abs_le_pow {bits : BitVec 32} {y : BitVec 16} (h : Ti bits y) :
    |y.toInt| ≤ 2 ^ bits.toNat := by
  replace h := h.2
  by_cases hb : 14#32 < bits
  · have h15 : (2 : Int) ^ 15 ≤ 2 ^ bits.toNat :=
      pow_le_pow_right₀ (by norm_num) (by rw [BitVec.lt_def] at hb; simp at hb; omega)
    have := BitVec.le_toInt y; have := BitVec.toInt_lt (x := y)
    rw [abs_le]; constructor <;> simp at * <;> omega
  · rcases h with h | rfl | ⟨h1, h2⟩
    · exact absurd h hb
    · simp only [show (1#16).toInt = 1 by decide, abs_one]; exact one_le_pow₀ (by norm_num)
    · have ht : bits.toNat ≤ 14 := by rw [BitVec.lt_def] at hb; simpa using hb
      have hsh : (1#32 <<< bits) = BitVec.ofNat 32 (2 ^ bits.toNat) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      rw [hsh] at h1 h2
      simp only [BitVec.slt_iff_toInt_lt, BitVec.toInt_signExtend_of_le (show 16 ≤ 32 by omega)]
        at h1 h2
      have hN : 2 ^ bits.toNat ≤ 16384 :=
        (Nat.pow_le_pow_right (by norm_num) ht).trans (by norm_num)
      exact_mod_cast abs_le_of_ofNat y _ hN h1 h2

theorem toInt_emod_two_of_and_one {y : BitVec 16} (h : y &&& 1#16 = 1#16) : y.toInt % 2 = 1 := by
  have h1 : y.toNat % 2 = 1 := by
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_and, Nat.and_one_is_mod] using this
  rw [BitVec.toInt_eq_toNat_cond]; split_ifs <;> omega

theorem Ti.bnd {bits : BitVec 32} {y : BitVec 16} (h : Ti bits y) : Bnd bits y := by
  have := h.abs_le_pow
  rw [Int.abs_eq_natAbs] at this
  exact ⟨Or.inr (toInt_emod_two_of_and_one h.1), by exact_mod_cast this⟩

/-! ## The digits

The walk carries `digitSum w 256 + e = N` (`SumEq`), `N` the scalar's low 255 bits and `e` what
the loop still owes: `(ti - 1) * 2 ^ m` for the running digit, plus `2 ^ c` during a carry. The
transitions below are the only arithmetic; the steps apply them. -/

theorem digitSum_succ (w : BitVec 4096) (k : Nat) :
    digitSum w (k + 1) = digitSum w k + (slot w k).toInt * 2 ^ k := rfl

theorem digitSum_splice (w : BitVec 4096) (x : BitVec 16) {i : Nat} (hi : i < 256) :
    ∀ K ≤ 256, digitSum (spliceBits w (16 * i) x) K
      = digitSum w K + if i < K then (x.toInt - (slot w i).toInt) * 2 ^ i else 0
  | 0, _ => by simp [digitSum]
  | K + 1, hK => by
    rw [digitSum_succ, digitSum_succ, digitSum_splice w x hi K (by omega),
      slot_spliceBits _ _ (by omega) hi]
    by_cases hKi : K = i
    · subst hKi; simp only [if_true, lt_irrefl, if_false, Nat.lt_succ_self]; ring
    · rw [if_neg hKi]
      by_cases h : i < K
      · rw [if_pos h, if_pos (by omega)]; ring
      · rw [if_neg h, if_neg (by omega)]; ring

/-- The scalar's low 255 bits are `digitSum w 256 + e`. -/
abbrev SumEq (Nv : Nat) (w : BitVec 4096) (e : Int) : Prop :=
  digitSum w 256 + e = ((Nv % 2 ^ 255 : Nat) : Int)

theorem SumEq.store {Nv : Nat} {w : BitVec 4096} {e e' : Int} {i : Nat} {x : BitVec 16}
    (h : SumEq Nv w e) (hi : i < 256) (he : e = e' + (x.toInt - (slot w i).toInt) * 2 ^ i) :
    SumEq Nv (spliceBits w (16 * i) x) e' := by
  unfold SumEq at *
  rw [digitSum_splice w x hi 256 le_rfl, if_pos hi]
  rw [← h, he]; ring

/-- Entries from `lo` on are `0` or `1`. -/
abbrev Ones (w : BitVec 4096) (lo : Nat) : Prop :=
  ∀ k, lo ≤ k → k < 256 → slot w k = 0#16 ∨ slot w k = 1#16

theorem Ones.store {w : BitVec 4096} {lo i : Nat} {x : BitVec 16} (h : Ones w lo)
    (hx : x = 0#16 ∨ x = 1#16) (hi : i < 256) : Ones (spliceBits w (16 * i) x) lo :=
  fun k hk hk' => by
    rw [slot_spliceBits _ _ hk' hi]; split_ifs
    · exact hx
    · exact h k hk hk'

theorem Ones.store_below {w : BitVec 4096} {lo lo' i : Nat} {x : BitVec 16} (h : Ones w lo)
    (hi : i < lo') (hlo : lo ≤ lo') (hi' : i < 256) : Ones (spliceBits w (16 * i) x) lo' :=
  fun k hk hk' => by
    rw [slot_spliceBits _ _ hk' hi', if_neg (by omega)]; exact h k (by omega) hk'

theorem slot_store_ne {w : BitVec 4096} {i k : Nat} {x : BitVec 16} (hi : i < 256) (hk : k < 256)
    (hne : k ≠ i) : slot (spliceBits w (16 * i) x) k = slot w k := by
  rw [slot_spliceBits _ _ hk hi, if_neg hne]

theorem slot_store_eq {w : BitVec 4096} {i : Nat} {x : BitVec 16} (hi : i < 256) :
    slot (spliceBits w (16 * i) x) i = x := by
  rw [slot_spliceBits _ _ hi hi, if_pos rfl]

theorem Ones.one {w : BitVec 4096} {lo k : Nat} (h : Ones w lo) (hk : lo ≤ k) (hk' : k < 256)
    (hz : ¬ slot w k = 0#16) : slot w k = 1#16 :=
  (h k hk hk').resolve_left hz

/-- Bit `j` of `Nv` as an entry. -/
def bitOf (Nv j : Nat) : BitVec 16 := if Nv.testBit j then 1#16 else 0#16

/-- Entries below `k` are `Nv`'s bits, as `^bb2` leaves them. -/
abbrev Bits (Nv : Nat) (w : BitVec 4096) (k : Nat) : Prop := ∀ j < k, slot w j = bitOf Nv j

theorem Bits.store {Nv : Nat} {w : BitVec 4096} {k : Nat} (h : Bits Nv w k) (hk : k < 256) :
    Bits Nv (spliceBits w (16 * k) (bitOf Nv k)) (k + 1) := fun j hj => by
  rw [slot_spliceBits _ _ (by omega) hk]; split_ifs with he
  · rw [he]
  · exact h j (by omega)

theorem bitOf_toInt (Nv j : Nat) : (bitOf Nv j).toInt = ((Nv / 2 ^ j % 2 : Nat) : Int) := by
  unfold bitOf
  rcases Nat.mod_two_eq_zero_or_one (Nv / 2 ^ j) with h2 | h2 <;>
    simp [Nat.testBit_eq_decide_div_mod_eq, h2]

theorem Bits.store_of {Nv : Nat} {w : BitVec 4096} {k : Nat} {x : BitVec 16} (h : Bits Nv w k)
    (hk : k < 256) (hx : x = bitOf Nv k) : Bits Nv (spliceBits w (16 * k) x) (k + 1) :=
  hx ▸ h.store hk

theorem digitSum_bits {Nv : Nat} {w : BitVec 4096} :
    ∀ K ≤ 255, Bits Nv w K → digitSum w K = ((Nv % 2 ^ K : Nat) : Int)
  | 0, _, _ => by simp [digitSum]
  | K + 1, hK, h => by
    rw [digitSum_succ, digitSum_bits K (by omega) fun j hj => h j (by omega), h K (by omega),
      bitOf_toInt, Nat.mod_pow_succ]
    push_cast; ring

theorem le13_of_bits {bits : BitVec 32} (hb : bits.toNat ≤ 13) : bits ≤ 13#32 := by
  simp only [BitVec.le_def]; simpa using hb

theorem not_break {bits y43 y44 y45 : BitVec 32} {e : Nat} (hK : K bits y43 y44 y45)
    (hb : bits.toNat ≤ 13) (he : e ≤ 14)
    (hc : ¬ BitVec.ofBool (LLVM.icmp' .sgt (BitVec.ofNat 32 (2 ^ e)) y44) = 1) : e ≤ 13 := by
  have hb' := le13_of_bits hb
  refine Nat.le_of_lt_succ (lt_of_le_of_ne he fun h => hc ?_)
  subst h
  obtain ⟨-, rfl, -⟩ := hK
  simp only [LLVM.icmp']
  show BitVec.ofBool (16384#32 >ₛ _) = 1
  have hbits : bits = BitVec.ofNat 32 bits.toNat := by simp
  rw [hbits]
  generalize bits.toNat = n at hb ⊢
  interval_cases n <;> decide +kernel

theorem ofNat_pow_toInt {d : Nat} (hd : d ≤ 13) : (BitVec.ofNat 16 (2 ^ d)).toInt = 2 ^ d := by
  interval_cases d <;> decide

theorem trunc_pow {d : Nat} (hd : d ≤ 13) :
    (BitVec.ofNat 32 (2 ^ d)).truncate 16 = BitVec.ofNat 16 (2 ^ d) := by
  interval_cases d <;> decide

theorem pow_le8192 {d : Nat} (hd : d ≤ 13) : BitVec.ofNat 16 (2 ^ d) ≤ 8192#16 := by
  interval_cases d <;> decide

theorem toInt_tip {bits : BitVec 32} {y52 : BitVec 16} {d : Nat} (hti : Ti bits y52)
    (hb : bits.toNat ≤ 13) (hd : d ≤ 13) :
    (y52 + BitVec.ofNat 16 (2 ^ d)).toInt = y52.toInt + 2 ^ d := by
  have hy : |y52.toInt| ≤ 8192 := hti.abs_le_pow.trans (by
    calc
      (2 : Int) ^ bits.toNat ≤ 2 ^ 13 := pow_le_pow_right₀ (by norm_num) hb
      _ = 8192 := by norm_num)
  have hz : (2 : Int) ^ d ≤ 8192 := by
    calc
      (2 : Int) ^ d ≤ 2 ^ 13 := pow_le_pow_right₀ (by norm_num) hd
      _ = 8192 := by norm_num
  have hz0 : 0 ≤ (2 : Int) ^ d := by positivity
  rw [abs_le] at hy
  rw [BitVec.toInt_add_of_not_saddOverflow, ofNat_pow_toInt hd]
  simp only [BitVec.saddOverflow, ofNat_pow_toInt hd, Bool.or_eq_true, decide_eq_true_eq]
  norm_num
  omega

theorem toInt_tim {bits : BitVec 32} {y52 : BitVec 16} {d : Nat} (hti : Ti bits y52)
    (hb : bits.toNat ≤ 13) (hd : d ≤ 13) :
    (y52 - BitVec.ofNat 16 (2 ^ d)).toInt = y52.toInt - 2 ^ d := by
  have hy : |y52.toInt| ≤ 8192 := hti.abs_le_pow.trans (by
    calc
      (2 : Int) ^ bits.toNat ≤ 2 ^ 13 := pow_le_pow_right₀ (by norm_num) hb
      _ = 8192 := by norm_num)
  have hz : (2 : Int) ^ d ≤ 8192 := by
    calc
      (2 : Int) ^ d ≤ 2 ^ 13 := pow_le_pow_right₀ (by norm_num) hd
      _ = 8192 := by norm_num
  have hz0 : 0 ≤ (2 : Int) ^ d := by positivity
  rw [abs_le] at hy
  rw [BitVec.toInt_sub_of_not_ssubOverflow, ofNat_pow_toInt hd]
  simp only [BitVec.ssubOverflow, ofNat_pow_toInt hd, Bool.or_eq_true, decide_eq_true_eq]
  norm_num
  omega

theorem bit_eq {V : BitVec 256} {k : Nat} :
    (BitVec.zeroExtend 16 (V.extractLsb' (8 * (k / 8)) 8)
      >>> (BitVec.truncate 16 (BitVec.ofNat 64 k) &&& 7#16)) &&& 1#16 = bitOf V.toNat k := by
  have ht : BitVec.truncate 16 (BitVec.ofNat 64 k) &&& 7#16 = BitVec.ofNat 16 (k % 8) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and, Nat.and_two_pow_sub_one_eq_mod _ 3]
    omega
  have hbit : V.toNat.testBit k = (V.extractLsb' (8 * (k / 8)) 8).getLsbD (k % 8) := by
    rw [BitVec.testBit_toNat, BitVec.getLsbD_extractLsb']
    simp [show k % 8 < 8 by omega, show 8 * (k / 8) + k % 8 = k by omega]
  rw [ht, bitOf, hbit]
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  simp only [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, Nat.add_zero,
    BitVec.toNat_ofNat, BitVec.getLsbD_setWidth]
  rw [Nat.mod_eq_of_lt (show k % 8 < 2 ^ 16 by omega)]
  simp only [show k % 8 < 16 by omega, decide_true, Bool.true_and]
  cases (V.extractLsb' (8 * (k / 8)) 8).getLsbD (k % 8) <;> rfl

/-- When the digits sum to the scalar. -/
abbrev Hyp (bits : BitVec 32) (slides n : Pointer) : Prop := bits.toNat ≤ 13 ∧ slides.id ≠ n.id

section Transitions
variable {Nv : Nat} {w : BitVec 4096}

/-- The outer loop at `i`. -/
abbrev Outer (Nv : Nat) (w : BitVec 4096) (i : Nat) : Prop :=
  SumEq Nv w 0 ∧ slot w i = 1#16 ∧ Ones w i

/-- The inner loop at `m` with running digit `ti`, `e` still owed. -/
abbrev Inner (Nv : Nat) (w : BitVec 4096) (m : Nat) (ti : BitVec 16) (e : Int) : Prop :=
  SumEq Nv w ((ti.toInt - 1) * 2 ^ m + e) ∧ slot w m = 1#16 ∧ Ones w m

theorem bitOf_01 (Nv j : Nat) : bitOf Nv j = 0#16 ∨ bitOf Nv j = 1#16 := by
  unfold bitOf; split <;> simp

theorem Bits.start (h : Bits Nv w 255) :
    SumEq Nv (spliceBits w (16 * 255) 0#16) 0 ∧ Ones (spliceBits w (16 * 255) 0#16) 0 := by
  have hb : Bits Nv (spliceBits w (16 * 255) 0#16) 255 := fun j hj => by
    rw [slot_store_ne (by omega) (by omega) (by omega)]; exact h j hj
  refine ⟨?_, fun k _ hk => ?_⟩
  · show digitSum _ 256 + 0 = _
    rw [add_zero, show (256 : Nat) = 255 + 1 from rfl, digitSum_succ, digitSum_bits 255 le_rfl hb,
      slot_store_eq (by omega)]
    simp
  · by_cases hk' : k = 255
    · subst hk'; exact Or.inl (slot_store_eq (by omega))
    · rw [hb k (by omega)]; exact bitOf_01 Nv k

theorem Outer.of_scan (h : SumEq Nv w 0 ∧ Ones w 0) {k : Nat} (hk : k < 256)
    (hz : ¬ slot w k = 0#16) : Outer Nv w k :=
  ⟨h.1, h.2.one (Nat.zero_le _) hk hz, fun j _ hj => h.2 j (Nat.zero_le _) hj⟩

theorem Inner.start {i : Nat} (h : Outer Nv w i) : Inner Nv w i 1#16 0 := by
  refine ⟨?_, h.2⟩
  simpa [show (1#16).toInt = 1 from rfl] using h.1

theorem Outer.last {i : Nat} (h : Outer Nv w i) (hi : i = 255) :
    SumEq Nv w (((1#16).toInt - 1) * 2 ^ 255) ∧ slot w 255 = 1#16 := by
  subst hi
  exact ⟨by simpa [show (1#16).toInt = 1 from rfl] using h.1, h.2.1⟩

theorem Inner.last {m : Nat} {ti : BitVec 16} (h : Inner Nv w m ti 0) :
    SumEq Nv w ((ti.toInt - 1) * 2 ^ m) ∧ slot w m = 1#16 :=
  ⟨by simpa using h.1, h.2.1⟩

theorem Inner.one {m c : Nat} {ti : BitVec 16} {e : Int} (h : Inner Nv w m ti e) (hmc : m < c)
    (hc : c < 256) (hz : ¬ slot w c = 0#16) : slot w c = 1#16 :=
  h.2.2.one (by omega) hc hz

theorem delta_of_not_break {bits y43 y44 y45 y61 : BitVec 32} {d : Nat} (hK : K bits y43 y44 y45)
    (hb : bits.toNat ≤ 13) (hy : y61 = BitVec.ofNat 32 (2 ^ min d 14))
    (hc : ¬ BitVec.ofBool (LLVM.icmp' .sgt y61 y44) = 1) :
    y61 = BitVec.ofNat 32 (2 ^ d) ∧ d ≤ 13 := by
  subst hy
  have := not_break hK hb (Nat.min_le_right _ _) hc
  rw [Nat.min_eq_left (by omega)]
  exact ⟨rfl, by omega⟩

theorem Inner.add {bits : BitVec 32} {m j : Nat} {y52 : BitVec 16} {y61 : BitVec 32}
    (h : Inner Nv w m y52 0) (hti : Ti bits y52) (hb : bits.toNat ≤ 13) (hmj : m ≤ j)
    (hy : y61 = BitVec.ofNat 32 (2 ^ (j + 1 - m)) ∧ j + 1 - m ≤ 13) :
    Inner Nv w m (y52 + y61.truncate 16) (-2 ^ (j + 1)) := by
  obtain ⟨rfl, hd⟩ := hy
  refine ⟨?_, h.2⟩
  have hp : (2 : Int) ^ (j + 1) = 2 ^ (j + 1 - m) * 2 ^ m := by
    rw [← pow_add]; congr 1; omega
  rw [trunc_pow hd, toInt_tip hti hb hd]
  have := h.1; unfold SumEq at this ⊢; rw [hp]; linear_combination this

theorem Inner.sub {bits : BitVec 32} {m j : Nat} {y52 y63 : BitVec 16}
    (h : Inner Nv w m y52 0) (hti : Ti bits y52) (hb : bits.toNat ≤ 13) (hmj : m ≤ j)
    (hy : y63 = BitVec.ofNat 16 (2 ^ (j + 1 - m)) ∧ j + 1 - m ≤ 13) :
    Inner Nv w m (y52 - y63) (2 ^ (j + 1)) := by
  obtain ⟨rfl, hd⟩ := hy
  refine ⟨?_, h.2⟩
  have hp : (2 : Int) ^ (j + 1) = 2 ^ (j + 1 - m) * 2 ^ m := by
    rw [← pow_add]; congr 1; omega
  rw [toInt_tim hti hb hd]
  have := h.1; unfold SumEq at this ⊢; rw [hp]; linear_combination this

theorem trunc_delta {y61 : BitVec 32} {d : Nat} (hy : y61 = BitVec.ofNat 32 (2 ^ d) ∧ d ≤ 13) :
    y61.truncate 16 = BitVec.ofNat 16 (2 ^ d) ∧ d ≤ 13 := by
  obtain ⟨rfl, hd⟩ := hy; exact ⟨trunc_pow hd, hd⟩

/-- Clearing a `1` at `c`: `2 ^ c` more is owed. -/
theorem Inner.clear {m c : Nat} {ti : BitVec 16} {e : Int} (h : Inner Nv w m ti e)
    (h1 : slot w c = 1#16) (hmc : m < c) (hc : c < 256) :
    Inner Nv (spliceBits w (16 * c) 0#16) m ti (e + 2 ^ c) :=
  ⟨h.1.store hc (by rw [h1]; simp [show (1#16).toInt = 1 from rfl]; ring),
    by rw [slot_store_ne hc (by omega) (by omega)]; exact h.2.1, h.2.2.store (Or.inl rfl) hc⟩

theorem Inner.clear_cancel {m c : Nat} {ti : BitVec 16} (h : Inner Nv w m ti (-2 ^ c))
    (h1 : slot w c = 1#16) (hmc : m < c) (hc : c < 256) :
    Inner Nv (spliceBits w (16 * c) 0#16) m ti 0 := by
  simpa using h.clear h1 hmc hc

theorem Inner.clear_carry {m c : Nat} {ti : BitVec 16} (h : Inner Nv w m ti (2 ^ c))
    (h1 : slot w c = 1#16) (hmc : m < c) (hc : c < 256) :
    Inner Nv (spliceBits w (16 * c) 0#16) m ti (2 ^ (c + 1)) := by
  have := h.clear h1 hmc hc; rwa [← two_mul, ← pow_succ'] at this

/-- Setting a `0` at `c` pays the carry. -/
theorem Inner.set {m c : Nat} {ti : BitVec 16} (h : Inner Nv w m ti (2 ^ c))
    (h0 : slot w c = 0#16) (hmc : m < c) (hc : c < 256) :
    Inner Nv (spliceBits w (16 * c) 1#16) m ti 0 ∧ slot (spliceBits w (16 * c) 1#16) c = 1#16 :=
  ⟨⟨h.1.store hc (by rw [h0]; simp [show (1#16).toInt = 1 from rfl]),
    by rw [slot_store_ne hc (by omega) (by omega)]; exact h.2.1, h.2.2.store (Or.inr rfl) hc⟩,
    slot_store_eq hc⟩

/-- Storing `ti` at `m` finishes the digit; the outer loop resumes at `c`. -/
theorem Inner.finish {m c : Nat} {ti : BitVec 16} (h : Inner Nv w m ti 0)
    (h1 : slot w c = 1#16) (hmc : m < c) (hc : c < 256) :
    Outer Nv (spliceBits w (16 * m) ti) c :=
  ⟨h.1.store (by omega) (by rw [h.2.1]; simp [show (1#16).toInt = 1 from rfl]),
    by rw [slot_store_ne (by omega) hc (by omega)]; exact h1,
    h.2.2.store_below hmc hmc.le (by omega)⟩

theorem SumEq.finish {m : Nat} {ti : BitVec 16}
    (h : SumEq Nv w ((ti.toInt - 1) * 2 ^ m) ∧ slot w m = 1#16) (hm : m < 256) :
    SumEq Nv (spliceBits w (16 * m) ti) 0 :=
  h.1.store hm (by rw [h.2]; simp [show (1#16).toInt = 1 from rfl])

end Transitions

theorem and_one (z : BitVec 16) : z &&& 1#16 = 0#16 ∨ z &&& 1#16 = 1#16 := by
  simp only [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases z.getLsbD 0 <;> simp

theorem bit_value (b : BitVec 8) (k : Nat) :
    ∃ x, (x = 0#16 ∨ x = 1#16) ∧ (∀ V : BitVec 256, b = V.extractLsb' (8 * (k / 8)) 8 →
      x = bitOf V.toNat k) ∧ LLVM.and (LLVM.lshr (LLVM.zext 16 (PoisonOr.value b))
      (LLVM.and (LLVM.trunc 16 (PoisonOr.value (BitVec.ofNat 64 k))) (PoisonOr.value 7#16)))
      (PoisonOr.value 1#16) = PoisonOr.value x := by
  simp only [LLVM.zext, LLVM.zext?, LLVM.trunc, LLVM.trunc?, LLVM.and, LLVM.and?, LLVM.lshr,
    LLVM.lshr?, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  have h : ¬ ((BitVec.truncate 16 (BitVec.ofNat 64 k) &&& 7#16) ≥ ((16 : Nat) : BitVec 16)) := by
    simp only [ge_iff_le, BitVec.le_def, BitVec.toNat_and, BitVec.toNat_ofNat,
      show 7 % 2 ^ 16 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    norm_num
    omega
  simp only [h, if_false, PoisonOr.value_bind]
  exact ⟨_, and_one _, fun V hV => by subst hV; exact bit_eq, rfl⟩

/-! ## The entry valuation, as the tail blocks read it

`%k` is `Γout` variable `18 - k`; `%arg2`, `%arg1`, `%arg0` are 19, 20, 21. `%18` is
`-1 << bits`, a value when `bits < 32`. -/

structure EntryEnv (V : fd_curve25519_scalar_wnaf.Γout.Valuation) (slides n : Pointer)
    (bits : BitVec 32) : Prop where
  c0 : V (⟨18, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 4294967295#32
  c1 : V (⟨17, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 0#64
  c2 : V (⟨16, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 3#64
  c3 : V (⟨15, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 536870911#64
  c4 : V (⟨14, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 16)) = .value 7#16
  c5 : V (⟨13, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 16)) = .value 1#16
  c6 : V (⟨12, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 1#64
  c7 : V (⟨11, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 255#64
  c8 : V (⟨10, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 16)) = .value 0#16
  c9 : V (⟨9, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 256#32
  c10 : V (⟨8, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 16#32
  c11 : V (⟨7, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 15#32
  c12 : V (⟨6, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 0#32
  c13 : V (⟨5, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 255#32
  c14 : V (⟨4, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 2#32
  c15 : V (⟨3, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 65536#32
  c16 : V (⟨2, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 1#32
  c17 : V (⟨1, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 256#64
  c18 : V (⟨0, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value (4294967295#32 <<< bits)
  arg1 : V (⟨20, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var SLLVM.Ty.ptr) = .value n
  arg0 : V (⟨21, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var SLLVM.Ty.ptr) = .value slides

theorem entry_run (slides n : Pointer) (bits : BitVec 32) (hbits : bits.toNat < 32)
    (s : GlobalState) :
    ∃ Vout, StateT.run (fd_curve25519_scalar_wnaf.entry.denote (Ctxt.Valuation.ofHVector
        [PoisonOr.value bits, PoisonOr.value n, PoisonOr.value slides]ₕ)) s
      = .value ((Vout, .inr ⟨1, rfl, [(PoisonOr.value (BitVec.ofNat 64 0) : LLVM.IntW 64)]ₕ⟩), s)
      ∧ EntryEnv Vout slides n bits := by
  denote_step_reduce v 18 [LLVM.const?] fold
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17
  refine ⟨?V, ?run, ?env⟩
  case run =>
    simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
    rfl
  case env =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hv18 ▸ shl_m1 hbits, rfl, rfl⟩

/-! ## The invariant -/

local notation "v64 " k => (PoisonOr.value (BitVec.ofNat 64 k) : LLVM.IntW 64)
local notation "v32 " k => (PoisonOr.value (BitVec.ofNat 32 k) : LLVM.IntW 32)
local notation "vp " q => (PoisonOr.value q : SLLVM.Ptr)
local notation "r16 " x => (PoisonOr.value x : LLVM.IntW 16)
local notation "r32 " x => (PoisonOr.value x : LLVM.IntW 32)

/-- Where the walk can stand, and what holds there. -/
inductive Reach (s : GlobalState) (slides : Pointer) (bits : BitVec 32) (H : Prop) (Nv : Nat) :
    SuccArgs fd_curve25519_scalar_wnaf.sigs → GlobalState → Prop
  | bb1 {u w : _} (hu : u ≈ Sw s slides w) (hw : BndUpTo bits w 255) (hI : H → Bits Nv w 255) :
      Reach s slides bits H Nv ⟨0, rfl, .nil⟩ u
  | bb2 {u w : _} (k : Nat) (hk : k ≤ 254) (hu : u ≈ Sw s slides w) (hw : BndUpTo bits w k)
      (hI : H → Bits Nv w k) :
      Reach s slides bits H Nv ⟨1, rfl, [v64 k]ₕ⟩ u
  | bb3 {u w : _} (k : Nat) (y19 : BitVec 32) (hk : k ≤ 255) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) (hy : Y19 bits y19) (hw : BndUpTo bits w 256)
      (hI : H → SumEq Nv w 0 ∧ Ones w 0) :
      Reach s slides bits H Nv ⟨2, rfl, [v64 k, r32 y19]ₕ⟩ u
  | bb4 {u w : _} (k : Nat) (y19 : BitVec 32) (hk : k ≤ 255) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) (hy : Y19 bits y19) (hw : BndUpTo bits w 256)
      (hI : H → SumEq Nv w 0 ∧ Ones w 0) :
      Reach s slides bits H Nv ⟨3, rfl, [r32 y19, v64 k]ₕ⟩ u
  | bb5 {u w : _} (k : Nat) (y19 : BitVec 32) (hk : k ≤ 254) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) (hy : Y19 bits y19) (hw : BndUpTo bits w 256)
      (hI : H → Outer Nv w k) :
      Reach s slides bits H Nv ⟨4, rfl, [r32 y19, v64 k]ₕ⟩ u
  | bb6 {u w : _} (i : Nat) (y19 : BitVec 32) (hi : i ≤ 254) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) (hy : Y19 bits y19) (hw : BndUpTo bits w 256)
      (hI : H → Outer Nv w i) :
      Reach s slides bits H Nv ⟨5, rfl, [r32 y19, v32 i]ₕ⟩ u
  | bb7 {u w : _} (i : Nat) (y43 y44 y45 : BitVec 32) (hi : i ≤ 255) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0 ∨ i = 255) (hK : K bits y43 y44 y45) (hw : BndUpTo bits w 256)
      (hI : H → Outer Nv w i) :
      Reach s slides bits H Nv ⟨6, rfl, [v32 i, r32 y43, r32 y44, r32 y45]ₕ⟩ u
  | bb8 {u w : _} (i : Nat) (y43 y44 y45 : BitVec 32) (hi : i ≤ 254) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hw : BndUpTo bits w 256)
      (hI : H → Outer Nv w i) :
      Reach s slides bits H Nv ⟨7, rfl, [r32 y43, r32 y44, r32 y45, v32 i]ₕ⟩ u
  | bb9 {u w : _} (j m : Nat) (y52 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmj : m ≤ j)
      (hj : j ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y52 0) :
      Reach s slides bits H Nv ⟨8, rfl, [v32 (j + 2), v64 j, r16 y52, r32 y43, r32 y44, r32 y45,
        v32 m, v64 m]ₕ⟩ u
  | bb10 {u w : _} (j m : Nat) (y52 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmj : m ≤ j)
      (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y52 0 ∧ slot w (j + 1) = 1#16) :
      Reach s slides bits H Nv ⟨9, rfl, [r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (j + 2),
        v64 j, r16 y52, v64 (j + 1), vp (slotPtr slides (j + 1))]ₕ⟩ u
  | bb11 {u w : _} (j m : Nat) (y52 : BitVec 16) (y43 y44 y45 y61 : BitVec 32) (hmj : m ≤ j)
      (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hd : y61 ≤ 16384#32 ∧ y61 &&& 1#32 = 0#32)
      (hw : BndUpTo bits w 256)
      (hI : H → (Inner Nv w m y52 0 ∧ slot w (j + 1) = 1#16)
        ∧ y61 = BitVec.ofNat 32 (2 ^ (j + 1 - m)) ∧ j + 1 - m ≤ 13) :
      Reach s slides bits H Nv ⟨10, rfl, [r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (j + 2),
        v64 j, r16 y52, v64 (j + 1), vp (slotPtr slides (j + 1)), r32 y61]ₕ⟩ u
  | bb12 {u w : _} (j m : Nat) (y64 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmj : m ≤ j)
      (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y64) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y64 (-2 ^ (j + 1)) ∧ slot w (j + 1) = 1#16) :
      Reach s slides bits H Nv ⟨11, rfl, [r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (j + 2),
        v64 (j + 1), vp (slotPtr slides (j + 1)), r16 y64]ₕ⟩ u
  | bb13 {u w : _} (j m : Nat) (y52 y63 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmj : m ≤ j)
      (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hd : y63 ≤ 16384#16 ∧ y63 &&& 1#16 = 0#16)
      (hw : BndUpTo bits w 256)
      (hI : H → (Inner Nv w m y52 0 ∧ slot w (j + 1) = 1#16)
        ∧ y63 = BitVec.ofNat 16 (2 ^ (j + 1 - m)) ∧ j + 1 - m ≤ 13) :
      Reach s slides bits H Nv ⟨12, rfl, [r32 y43, r32 y44, r32 y45, v64 m, v32 (j + 2), v64 j,
        r16 y52, v64 (j + 1), vp (slotPtr slides (j + 1)), r16 y63]ₕ⟩ u
  | bb14 {u w : _} (j m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmj : m ≤ j)
      (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y68 (2 ^ (j + 1)) ∧ slot w (j + 1) = 1#16) :
      Reach s slides bits H Nv ⟨13, rfl, [r32 y43, r32 y44, r32 y45, v64 m, v32 (j + 2), v64 j,
        vp (slotPtr slides (j + 1)), r16 y68]ₕ⟩ u
  | bb15 {u w : _} (c m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmc : m < c)
      (hc : c ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y68 (2 ^ c) ∧ slot w c = 1#16) :
      Reach s slides bits H Nv ⟨14, rfl, [r32 y43, r32 y44, r32 y45, v64 m, v32 c, r16 y68,
        vp (slotPtr slides c)]ₕ⟩ u
  | bb16 {u w : _} (c m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmc : m < c)
      (hc : c ≤ 255) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y68 (2 ^ c) ∧ slot w c = 0#16) :
      Reach s slides bits H Nv ⟨15, rfl, [r32 y43, r32 y44, r32 y45, v64 m, r16 y68, v64 c,
        vp (slotPtr slides c)]ₕ⟩ u
  | bb17 {u w : _} (c m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmc : m < c)
      (hc : c ≤ 255) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y68 (2 ^ c) ∧ slot w c = 0#16) :
      Reach s slides bits H Nv ⟨16, rfl, [v32 c, vp (slotPtr slides c), r32 y43, r32 y44, r32 y45,
        v64 m, r16 y68]ₕ⟩ u
  | bb18 {u w : _} (c m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmc : m < c)
      (hc : c ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y68 (2 ^ c) ∧ slot w c = 1#16) :
      Reach s slides bits H Nv ⟨17, rfl, [v64 c, vp (slotPtr slides c), r32 y43, r32 y44, r32 y45,
        v64 m, r16 y68]ₕ⟩ u
  | bb19 {u w : _} (c m : Nat) (y87 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmc : m < c)
      (hc : c ≤ 255) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y87) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y87 0) :
      Reach s slides bits H Nv ⟨18, rfl, [r16 y87, r32 y43, r32 y44, r32 y45, v32 m, v64 m,
        v32 (c + 1), v64 c]ₕ⟩ u
  | bb20 {u w : _} (m : Nat) (y91 : BitVec 16) (hm : m ≤ 255) (hu : u ≈ Sw s slides w)
      (hti : Ti bits y91) (hw : BndUpTo bits w 256)
      (hI : H → SumEq Nv w ((y91.toInt - 1) * 2 ^ m) ∧ slot w m = 1#16) :
      Reach s slides bits H Nv ⟨19, rfl, [v64 m, r16 y91]ₕ⟩ u
  | bb21 {u w : _} (c m : Nat) (y52 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmc : m < c)
      (hc : c ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0)
      (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y52 0 ∧ slot w c = 1#16) :
      Reach s slides bits H Nv ⟨20, rfl, [r32 y43, r32 y44, r32 y45, v64 m, r16 y52, v64 c]ₕ⟩ u
  | bb22 {u w : _} (c m : Nat) (y95 : BitVec 16) (y43 y44 y45 : BitVec 32) (hmc : m < c)
      (hc : c ≤ 255) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0 ∨ c = 255)
      (hK : K bits y43 y44 y45) (hti : Ti bits y95) (hw : BndUpTo bits w 256)
      (hI : H → Inner Nv w m y95 0 ∧ slot w c = 1#16) :
      Reach s slides bits H Nv ⟨21, rfl, [v32 c, r16 y95, r32 y43, r32 y44, r32 y45, v64 m]ₕ⟩ u
  | bb23 {u w : _} (hu : u ≈ Sw s slides w) (hw : BndUpTo bits w 256) (hI : H → SumEq Nv w 0) :
      Reach s slides bits H Nv ⟨22, rfl, .nil⟩ u

/-- What the walk ends in. -/
def Done (s : GlobalState) (slides : Pointer) (bits : BitVec 32) (H : Prop) (Nv : Nat)
    (u : GlobalState) : Prop :=
  ∃ w, u ≈ Sw s slides w ∧ BndUpTo bits w 256 ∧ (H → SumEq Nv w 0)

/-! ## The variant -/

/-- A register as a natural; `0` unless it is a bitvector value. -/
def headNat : (t : SLLVM.Ty) → toType t → Nat
  | SLLVM.Ty.bitvec _, .value x => x.toNat
  | _, _ => 0

/-- Argument `i` as a natural. -/
def argNat : {l : List SLLVM.Ty} → HVector toType l → Nat → Nat
  | [], _, _ => 0
  | t :: _, .cons x _, 0 => headNat t x
  | _ :: _, .cons _ xs, i + 1 => argNat xs i

@[simp] theorem argNat_succ {t : SLLVM.Ty} {l : List SLLVM.Ty} (x : toType t)
    (xs : HVector toType l) (i : Nat) : argNat (HVector.cons x xs) (i + 1) = argNat xs i := rfl

@[simp] theorem argNat_zero {w : Nat} {l : List SLLVM.Ty} (x : BitVec w) (xs : HVector toType l) :
    argNat (l := SLLVM.Ty.bitvec w :: l) (HVector.cons (PoisonOr.value x : LLVM.IntW w) xs) 0
      = x.toNat := rfl

/-- The variant by block index, reading the loop indices from the arguments `a`: `3000` per
outer index left, then `8` per inner index left, `1` per carry index left. -/
def rank : Nat → (Nat → Nat) → Nat
  | 0, _ => 772040
  | 1, a => 772041 + (255 - a 0)
  | 2, a => 771005 + 4 * (256 - a 0)
  | 3, a => 771004 + 4 * (256 - a 1)
  | 4, _ => 771001
  | 5, _ => 771000
  | 6, a => (256 - a 0) * 3000 + 2999
  | 7, a => (256 - a 3) * 3000 + 2998
  | 8, a => (256 - a 7) * 3000 + 305 + 8 * (256 - a 1)
  | 9, a => (256 - a 4) * 3000 + 304 + 8 * (256 - a 6)
  | 10, a => (256 - a 4) * 3000 + 303 + 8 * (256 - a 6)
  | 11, a => (256 - a 4) * 3000 + 302 + 8 * (257 - a 6)
  | 12, a => (256 - a 3) * 3000 + 264
  | 13, a => (256 - a 3) * 3000 + 263
  | 14, a => (256 - a 3) * 3000 + 6 + (256 - a 4)
  | 15, a => (256 - a 3) * 3000 + 4
  | 16, a => (256 - a 5) * 3000 + 3
  | 17, a => (256 - a 5) * 3000 + 5 + (256 - a 0)
  | 18, a => (256 - a 5) * 3000 + 306 + 8 * (256 - a 7)
  | 19, _ => 1
  | 20, a => (256 - a 3) * 3000 + 3
  | 21, a => (256 - a 5) * 3000 + 2
  | _, _ => 0

abbrev μ (t : SuccArgs fd_curve25519_scalar_wnaf.sigs) (_ : GlobalState) : Nat :=
  rank t.idx (argNat t.args)

/-- Closes `μ t' u' < m₀` for concrete successors. -/
macro "rank_lt" : tactic => `(tactic| (simp [μ, rank] <;> omega))

/-- A block's outcome, as `Blocks.run_of_variant` consumes it; `m₀` is the source's `μ`. -/
abbrev Post (s : GlobalState) (slides : Pointer) (bits : BitVec 32) (H : Prop) (Nv : Nat) (m₀ : Nat) {Γ : Ctxt SLLVM.Ty}
    (p : Γ.Valuation × (HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty) ⊕
      SuccArgs fd_curve25519_scalar_wnaf.sigs))
    (u : GlobalState) : Prop :=
  (∀ rs, p.2 = .inl rs → Done s slides bits H Nv u) ∧ (∀ t, p.2 = .inr t → Reach s slides bits H Nv t u ∧ μ t u < m₀)

/-! ## The blocks -/

section Steps
variable {s : GlobalState} {slides n : Pointer} {bits : BitVec 32} {H : Prop} {Nv : Nat}
  {V : fd_curve25519_scalar_wnaf.Γout.Valuation}

theorem step_bb23 {u : GlobalState} {w : BitVec 4096} (hu : u ≈ Sw s slides w)
    (hw : BndUpTo bits w 256) (hI : H → SumEq Nv w 0) (m₀ : Nat) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 22 rfl).2.denote
      (Ctxt.Valuation.ofHVector (.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv m₀ p u' := by
  denote_reduce_get
  exact term_ret ⟨fun _ _ => ⟨w, hu, hw, hI⟩, fun _ h => absurd h (by simp)⟩

theorem step_bb1 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (hu : u ≈ Sw s slides w) (hw : BndUpTo bits w 255)
    (hI : H → Bits Nv w 255) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 0 rfl).2.denote
      (Ctxt.Valuation.ofHVector (.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨0, rfl, .nil⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 19
  denote_step_reduce v 20 [LLVM.const?] fold
  try simp only [simp_spine] at hv19 hv20
  simp only [hV.arg0] at hv20
  have h19 : v19 = .value (4294967295#32 <<< bits ^^^ 4294967295#32) := by
    rw [hv19, hV.c18, hV.c0]; rfl
  have h20 : v20 = PoisonOr.value (slotPtr slides 255) := by rw [hv20]; exact gep_slot slides 255
  clear hv19 hv20
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides 255) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c8, h20]
      rw [run_liftM (run_store_slot hsl hu (by omega) 0#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show 255 < 256 by omega) 0#16
  refine term_br ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hV.c1, h19]
  refine ⟨Reach.bb3 0 _ (by omega) hu' (by rw [slot_spliceBits _ _ (by omega) (by omega), if_pos rfl]; rfl)
    rfl (hw.store bnd_zero (by omega) fun j hj => by omega) fun hh => Bits.start (hI hh), ?_⟩
  rank_lt

theorem step_bb2 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides)
    (hn : IsByteBufPtr s.mem n) {u : GlobalState}
    {w : BitVec 4096} (k : Nat) (hk : k ≤ 254) (hu : u ≈ Sw s slides w) (hw : BndUpTo bits w k)
    (hI : H → Bits Nv w k) (hH : H → Hyp bits slides n) (hNv : Nv = (readBuf hn).toNat) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 1 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v64 k]ₕ : HVector toType [SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨1, rfl, [v64 k]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 22
  denote_step_reduce v 25 [LLVM.const?] fold
  simp only [simp_spine, hV.c2, hV.c3, hV.arg1] at hv23 hv24 hv25
  rw [idx_n (by omega)] at hv25
  have h25 : v25 = PoisonOr.value (bytePtr n (k / 8)) := by rw [hv25, gep_byte]
  clear hv23 hv24 hv25
  refine (run_load_byte hn hu (show k / 8 < 32 by omega)).elim fun b hb => ?_
  have hbv := hb.1
  rw [BlockCom.run_denote_var_of_value (x := (PoisonOr.value b : LLVM.IntW 8)) (s' := u) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h25]
      rw [run_liftM hb.2]; rfl)]
  denote_step_reduce v 31 [LLVM.const?] fold
  simp only [simp_spine, hV.arg0, hV.c4, hV.c5] at hv27 hv28 hv29 hv30 hv31
  rw [hv22] at hv30
  have h31 : v31 = PoisonOr.value (slotPtr slides k) := by rw [hv31, gep_slot]
  clear hv31
  refine (bit_value b k).elim fun x30 h30' => ?_
  have h30 := h30'.2.2
  rw [h30] at hv30
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides k) x30 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hv30, h31]
      rw [run_liftM (run_store_slot hsl hu (by omega) x30)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show k < 256 by omega) x30
  have hw' : BndUpTo bits (spliceBits w (16 * k) x30) (k + 1) :=
    hw.store (bnd_of_bit h30'.1) (by omega) fun j hj => by omega
  have hI' : H → Bits Nv (spliceBits w (16 * k) x30) (k + 1) := fun hh =>
    Bits.store_of (hI hh) (by omega) (hNv ▸ h30'.2.1 _ (hbv (hH hh).2))
  denote_step_reduce v 33 [LLVM.const?] fold
  simp only [simp_spine, hV.c6, hV.c7] at hv32 hv33
  rw [add64 _ (by omega), icmp_eq_ofNat (by omega) (by omega)] at hv33
  refine term_condBr (by simp only [simp_spine, hv33]; rfl) ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hk1 : k + 1 = 255
  · rw [if_pos (ofBool_eq_one.mpr hk1)]
    exact ⟨Reach.bb1 hu' (hk1 ▸ hw') (hk1 ▸ hI'), by rank_lt⟩
  · rw [if_neg (mt ofBool_eq_one.mp hk1)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv32, add64 _ (show k + 1 < 2 ^ 63 by omega)]
    refine ⟨Reach.bb2 (k + 1) (by omega) hu' hw' hI', ?_⟩
    rank_lt

theorem step_bb3 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (k : Nat) (y19 : BitVec 32) (hk : k ≤ 255)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hy : Y19 bits y19) (hw : BndUpTo bits w 256)
    (hI : H → SumEq Nv w 0 ∧ Ones w 0) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 2 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v64 k, r32 y19]ₕ : HVector toType [SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨2, rfl, [v64 k, r32 y19]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 35
  denote_step_reduce v 35 [LLVM.const?] fold
  simp only [simp_spine, hV.arg0] at hv35
  have h35 : v35 = PoisonOr.value (slotPtr slides k) := by rw [hv35, gep_slot]
  clear hv35
  rw [BlockCom.run_denote_var_of_value (x := (PoisonOr.value (slot w k) : LLVM.IntW 16)) (s' := u) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h35]
      rw [run_liftM (run_load_slot hsl hu (by omega))]; rfl)]
  denote_step_reduce v 37 [LLVM.const?] fold
  simp only [simp_spine, hV.c8] at hv37
  refine term_condBr (b := BitVec.ofBool (slot w k == 0#16))
    (by simp only [simp_spine, hv37]; rfl) ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hz : slot w k = 0#16
  · rw [if_pos (ofBool_beq_one.mpr hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine]
    exact ⟨Reach.bb4 k y19 hk hu ht hy hw hI, by rank_lt⟩
  · rw [if_neg (mt ofBool_beq_one.mp hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine]
    have hk' : k ≠ 255 := fun h => hz (h ▸ ht)
    exact ⟨Reach.bb5 k y19 (by omega) hu ht hy hw fun hh => Outer.of_scan (hI hh) (by omega) hz,
      by rank_lt⟩

theorem step_bb4 (hV : EntryEnv V slides n bits) {u : GlobalState}
    {w : BitVec 4096} (k : Nat) (y19 : BitVec 32) (hk : k ≤ 255)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hy : Y19 bits y19) (hw : BndUpTo bits w 256)
    (hI : H → SumEq Nv w 0 ∧ Ones w 0) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 3 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y19, v64 k]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨3, rfl, [r32 y19, v64 k]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 38
  denote_step_reduce v 39 [LLVM.const?] fold
  simp only [simp_spine, hV.c6, hV.c17] at hv38 hv39
  rw [add64 _ (by omega), icmp_eq_ofNat (by omega) (by omega)] at hv39
  refine term_condBr (by simp only [simp_spine, hv39]; rfl)
    ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hk1 : k + 1 = 256
  · rw [if_pos (ofBool_eq_one.mpr hk1)]
    exact ⟨Reach.bb23 hu hw fun hh => (hI hh).1, by rank_lt⟩
  · rw [if_neg (mt ofBool_eq_one.mp hk1)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv38, add64 _ (show k + 1 < 2 ^ 63 by omega)]
    exact ⟨Reach.bb3 (k + 1) y19 (by omega) hu ht hy hw hI, by rank_lt⟩

theorem step_bb5 (hV : EntryEnv V slides n bits) {u : GlobalState}
    {w : BitVec 4096} (k : Nat) (y19 : BitVec 32) (hk : k ≤ 254)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hy : Y19 bits y19) (hw : BndUpTo bits w 256)
    (hI : H → Outer Nv w k) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 4 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y19, v64 k]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨4, rfl, [r32 y19, v64 k]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 40
  denote_step_reduce v 41 [LLVM.const?] fold
  simp only [simp_spine, hV.c9] at hv40 hv41
  rw [trunc32 (show k < 2 ^ 32 by omega)] at hv40 hv41
  rw [icmp_slt32 (by omega) (by omega)] at hv41
  refine term_condBr (by simp only [simp_spine, hv41]; rfl)
    ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  rw [if_pos (ofBool_eq_one.mpr (by omega))]
  simp only [Target.denote_mk, HVector.map, simp_spine, hv40]
  exact ⟨Reach.bb6 k y19 hk hu ht hy hw hI, by rank_lt⟩

theorem step_bb6 (hV : EntryEnv V slides n bits) {u : GlobalState}
    {w : BitVec 4096} (i : Nat) (y19 : BitVec 32) (hi : i ≤ 254)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hy : Y19 bits y19) (hw : BndUpTo bits w 256)
    (hI : H → Outer Nv w i) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 5 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y19, v32 i]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨5, rfl, [r32 y19, v32 i]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 42
  denote_step_reduce v 45 [LLVM.const?] fold
  simp only [simp_spine, hV.c10, hV.c11, hV.c12] at hv42 hv43 hv44 hv45
  refine (sub_ashr_value y19).elim fun y45 h45 => ?_
  refine (ashr_shl_value y19 16#32 (by decide)).elim fun y43 h43 => ?_
  refine (ashr_shl_value y19 15#32 (by decide)).elim fun y44 h44 => ?_
  rw [h45.2] at hv45
  rw [h43.2] at hv43
  rw [h44.2] at hv44
  refine term_br ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hv43, hv44, hv45]
  exact ⟨Reach.bb7 i y43 y44 y45 (by omega) hu (Or.inl ht)
    ⟨by rw [h43.1, hy], by rw [h44.1, hy], by rw [h45.1, h43.1]⟩ hw hI, by rank_lt⟩

theorem step_bb7 (hV : EntryEnv V slides n bits) {u : GlobalState}
    {w : BitVec 4096} (i : Nat) (y43 y44 y45 : BitVec 32) (hi : i ≤ 255)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0 ∨ i = 255) (hK : K bits y43 y44 y45) (hw : BndUpTo bits w 256)
    (hI : H → Outer Nv w i) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 6 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v32 i, r32 y43, r32 y44, r32 y45]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨6, rfl, [v32 i, r32 y43, r32 y44, r32 y45]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 47
  denote_step_reduce v 47 [LLVM.const?] fold
  simp only [simp_spine, hV.c13] at hv47
  rw [icmp_slt32 (by omega) (by omega)] at hv47
  refine term_condBr (by simp only [simp_spine, hv47]; rfl)
    ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hi1 : i < 255
  · rw [if_pos (ofBool_eq_one.mpr hi1)]
    simp only [Target.denote_mk, HVector.map, simp_spine]
    exact ⟨Reach.bb8 i y43 y44 y45 (by omega) hu (ht.resolve_right (by omega)) hK hw hI,
      by rank_lt⟩
  · rw [if_neg (mt ofBool_eq_one.mp hi1)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hV.c7, hV.c5]
    exact ⟨Reach.bb20 255 1#16 (by omega) hu ti_one hw fun hh => Outer.last (hI hh) (by omega),
      by rank_lt⟩

theorem step_bb8 (hV : EntryEnv V slides n bits) {u : GlobalState}
    {w : BitVec 4096} (i : Nat) (y43 y44 y45 : BitVec 32) (hi : i ≤ 254)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hw : BndUpTo bits w 256)
    (hI : H → Outer Nv w i) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 7 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y43, r32 y44, r32 y45, v32 i]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨7, rfl, [r32 y43, r32 y44, r32 y45, v32 i]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 48
  denote_step_reduce v 49 [LLVM.const?] fold
  try simp only [simp_spine] at hv48 hv49
  simp only [hV.c14] at hv49
  refine term_br ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hv48, hv49, hV.c5,
    sext64 (show i < 2 ^ 31 by omega), add32 _ (show i + 2 < 2 ^ 31 by omega)]
  exact ⟨Reach.bb9 i i 1#16 y43 y44 y45 le_rfl hi hu ht hK ti_one hw fun hh => Inner.start (hI hh),
    by rank_lt⟩

theorem step_bb9 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (y52 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmj : m ≤ j) (hj : j ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y52 0) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 8 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v32 (j + 2), v64 j, r16 y52, r32 y43, r32 y44, r32 y45, v32 m, v64 m]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨8, rfl, [v32 (j + 2), v64 j, r16 y52, r32 y43, r32 y44, r32 y45, v32 m, v64 m]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 53
  denote_step_reduce v 54 [LLVM.const?] fold
  simp only [simp_spine, hV.c6, hV.arg0] at hv53 hv54
  rw [add64 _ (show j + 1 < 2 ^ 63 by omega)] at hv53 hv54
  have h54 : v54 = PoisonOr.value (slotPtr slides (j + 1)) := by rw [hv54, gep_slot]
  clear hv54
  rw [BlockCom.run_denote_var_of_value (x := (PoisonOr.value (slot w (j + 1)) : LLVM.IntW 16)) (s' := u) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h54]
      rw [run_liftM (run_load_slot hsl hu (by omega))]; rfl)]
  denote_step_reduce v 56 [LLVM.const?] fold
  simp only [simp_spine, hV.c8] at hv56
  refine term_condBr (b := BitVec.ofBool (slot w (j + 1) == 0#16))
    (by simp only [simp_spine, hv56]; rfl) ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hz : slot w (j + 1) = 0#16
  · rw [if_pos (ofBool_beq_one.mpr hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv53, h54]
    exact ⟨Reach.bb19 (j + 1) m y52 y43 y44 y45 (by omega) (by omega) hu ht hK hti hw hI, by rank_lt⟩
  · rw [if_neg (mt ofBool_beq_one.mp hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv53, h54]
    have hj' : j + 1 ≠ 255 := fun h => hz (h ▸ ht)
    exact ⟨Reach.bb10 j m y52 y43 y44 y45 hmj (by omega) hu ht hK hti hw
      fun hh => ⟨hI hh, Inner.one (hI hh) (by omega) (by omega) hz⟩, by rank_lt⟩

theorem step_bb10 (hs : s.WF) (hV : EntryEnv V slides n bits)
    {u : GlobalState} {w : BitVec 4096} (j m : Nat) (y52 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmj : m ≤ j) (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y52 0 ∧ slot w (j + 1) = 1#16) (hH : H → Hyp bits slides n) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 9 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (j + 2), v64 j, r16 y52, v64 (j + 1),
          vp (slotPtr slides (j + 1))]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32,
          SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32,
          SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨9, rfl, [r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (j + 2), v64 j, r16 y52, v64 (j + 1),
          vp (slotPtr slides (j + 1))]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 57
  denote_step_reduce v 58 [LLVM.const?] fold
  rw [trunc32 (show j + 1 < 2 ^ 32 by omega), sub32 (by omega) (by omega)] at hv58
  have hwf : u.WF := (GlobalState.WF.splice hs).of_equiv hu.symm
  refine (fd_int_min_conforms v58 u hwf).elim fun u1 h => h.elim fun hcall he => ?_
  rw [BlockCom.run_denote_call_cfg_of_value (c := fd_int_min) (argTys := [SLLVM.Ty.bitvec 32])
    (argVals := [v58]ₕ) (x := SLLVM.smin v58 (.value 14#32)) (s' := u1) (by simp only [simp_spine])
    hcall]
  have hu1 := he.symm.trans hu
  rw [hv58, smin14 (by omega)]
  denote_step_reduce v 62 [LLVM.const?] fold
  simp only [simp_spine, hV.c10, hV.c15] at hv60 hv61 hv62
  refine (delta_value (e := min (j + 1 - m) 14) (by omega) (by omega)).elim fun y61 h61 => ?_
  rw [h61.2.2] at hv61 hv62
  refine term_condBr (by simp only [simp_spine, hv62]; rfl)
    ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  split
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact ⟨Reach.bb21 (j + 1) m y52 y43 y44 y45 (by omega) hj hu1 ht hK hti hw hI, by rank_lt⟩
  · rename_i hc
    simp only [Target.denote_mk, HVector.map, simp_spine, hv61]
    exact ⟨Reach.bb11 j m y52 y43 y44 y45 y61 hmj hj hu1 ht hK hti h61.1 hw
      fun hh => ⟨hI hh, delta_of_not_break hK (hH hh).1 h61.2.1 hc⟩, by rank_lt⟩

theorem step_bb11 {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (y52 : BitVec 16) (y43 y44 y45 y61 : BitVec 32)
    (hmj : m ≤ j) (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hd : y61 ≤ 16384#32 ∧ y61 &&& 1#32 = 0#32) (hw : BndUpTo bits w 256)
    (hI : H → (Inner Nv w m y52 0 ∧ slot w (j + 1) = 1#16)
      ∧ y61 = BitVec.ofNat 32 (2 ^ (j + 1 - m)) ∧ j + 1 - m ≤ 13) (hH : H → Hyp bits slides n) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 10 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (j + 2), v64 j, r16 y52, v64 (j + 1), vp (slotPtr slides (j + 1)), r32 y61]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨10, rfl, [r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (j + 2), v64 j, r16 y52, v64 (j + 1), vp (slotPtr slides (j + 1)), r32 y61]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 63
  denote_step_reduce v 66 [LLVM.const?] fold
  refine term_condBr (by simp only [simp_spine, hv66]; rfl)
    ⟨fun _ h => absurd h (by simp), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  split
  · simp only [Target.denote_mk, HVector.map, simp_spine, hv63]
    exact ⟨Reach.bb13 j m y52 _ y43 y44 y45 hmj hj hu ht hK hti (trunc_le hd) hw
      fun hh => ⟨(hI hh).1, trunc_delta (hI hh).2⟩, by rank_lt⟩
  · rename_i hc
    simp only [Target.denote_mk, HVector.map, simp_spine, hv64]
    exact ⟨Reach.bb12 j m _ y43 y44 y45 hmj hj hu ht hK (ti_tip hK hti hd hc) hw
      fun hh => ⟨Inner.add (hI hh).1.1 hti (hH hh).1 hmj (hI hh).2, (hI hh).1.2⟩, by rank_lt⟩

theorem step_bb12 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (y64 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmj : m ≤ j) (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y64) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y64 (-2 ^ (j + 1)) ∧ slot w (j + 1) = 1#16) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 11 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (j + 2), v64 (j + 1), vp (slotPtr slides (j + 1)), r16 y64]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨11, rfl, [r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (j + 2), v64 (j + 1), vp (slotPtr slides (j + 1)), r16 y64]ₕ⟩ u) p u' := by
  denote_reduce_get
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (j + 1)) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c8]
      rw [run_liftM (run_store_slot hsl hu (by omega) 0#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show j + 1 < 256 by omega) 0#16
  refine term_br ⟨fun _ h => absurd h (by simp), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine]
  exact ⟨Reach.bb19 (j + 1) m y64 y43 y44 y45 (by omega) (by omega) hu'
    (by rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht) hK hti
    (hw.store256 bnd_zero (by omega))
    fun hh => Inner.clear_cancel (hI hh).1 (hI hh).2 (by omega) (by omega), by rank_lt⟩

theorem step_bb13 {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (y52 y63 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmj : m ≤ j) (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hd : y63 ≤ 16384#16 ∧ y63 &&& 1#16 = 0#16) (hw : BndUpTo bits w 256)
    (hI : H → (Inner Nv w m y52 0 ∧ slot w (j + 1) = 1#16)
      ∧ y63 = BitVec.ofNat 16 (2 ^ (j + 1 - m)) ∧ j + 1 - m ≤ 13) (hH : H → Hyp bits slides n) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 12 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y43, r32 y44, r32 y45, v64 m, v32 (j + 2), v64 j, r16 y52, v64 (j + 1), vp (slotPtr slides (j + 1)), r16 y63]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨12, rfl, [r32 y43, r32 y44, r32 y45, v64 m, v32 (j + 2), v64 j, r16 y52, v64 (j + 1), vp (slotPtr slides (j + 1)), r16 y63]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 67
  denote_step_reduce v 70 [LLVM.const?] fold
  refine term_condBr (by simp only [simp_spine, hv70]; rfl)
    ⟨fun _ h => absurd h (by simp), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  split
  · simp only [Target.denote_mk, HVector.map, simp_spine, hv67, trunc32 (show j + 1 < 2 ^ 32 by omega)]
    exact ⟨Reach.bb22 (j + 1) m y52 y43 y44 y45 (by omega) (by omega) hu (Or.inl ht) hK hti hw
      fun hh => (hI hh).1, by rank_lt⟩
  · rename_i hc
    simp only [Target.denote_mk, HVector.map, simp_spine, hv68]
    exact ⟨Reach.bb14 j m _ y43 y44 y45 hmj hj hu ht hK (ti_tim hK hti hd hc) hw
      fun hh => ⟨Inner.sub (hI hh).1.1 hti (hH hh).1 hmj (hI hh).2, (hI hh).1.2⟩, by rank_lt⟩

theorem step_bb14 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmj : m ≤ j) (hj : j + 1 ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y68 (2 ^ (j + 1)) ∧ slot w (j + 1) = 1#16) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 13 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y43, r32 y44, r32 y45, v64 m, v32 (j + 2), v64 j, vp (slotPtr slides (j + 1)), r16 y68]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨13, rfl, [r32 y43, r32 y44, r32 y45, v64 m, v32 (j + 2), v64 j, vp (slotPtr slides (j + 1)), r16 y68]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 71
  denote_step_reduce v 71 [LLVM.const?] fold
  try simp only [simp_spine] at hv71
  rw [trunc32 (show j < 2 ^ 32 by omega)] at hv71
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (j + 1)) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c8]
      rw [run_liftM (run_store_slot hsl hu (by omega) 0#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show j + 1 < 256 by omega) 0#16
  have ht' : slot (spliceBits w (16 * (j + 1)) 0#16) 255 = 0 :=
    (by rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht)
  have hw' := hw.store256 bnd_zero (show j + 1 < 256 by omega)
  have hI' : H → Inner Nv (spliceBits w (16 * (j + 1)) 0#16) m y68 (2 ^ (j + 2)) := fun hh =>
    Inner.clear_carry (hI hh).1 (hI hh).2 (by omega) (by omega)
  denote_step_reduce v 74 [LLVM.const?] fold
  simp only [simp_spine, hV.c14, hV.arg0, hv71] at hv72 hv73 hv74
  rw [add32 _ (show j + 2 < 2 ^ 31 by omega)] at hv72 hv73 hv74
  rw [sext64 (show j + 2 < 2 ^ 31 by omega)] at hv73 hv74
  have h74 : v74 = PoisonOr.value (slotPtr slides (j + 2)) := by rw [hv74, gep_slot]
  clear hv74
  rw [BlockCom.run_denote_var_of_value (x := (PoisonOr.value (slot (spliceBits w (16 * (j + 1)) 0#16) (j + 2)) : LLVM.IntW 16)) (s' := { u with mem := u.mem.splice (slotPtr slides (j + 1)) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h74]
      rw [run_liftM (run_load_slot hsl hu' (by omega))]; rfl)]
  denote_step_reduce v 76 [LLVM.const?] fold
  simp only [simp_spine, hV.c8] at hv76
  refine term_condBr (b := BitVec.ofBool (slot (spliceBits w (16 * (j + 1)) 0#16) (j + 2) == 0#16))
    (by simp only [simp_spine, hv76]; rfl) ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hz : slot (spliceBits w (16 * (j + 1)) 0#16) (j + 2) = 0#16
  · rw [if_pos (ofBool_beq_one.mpr hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv72, h74]
    exact ⟨Reach.bb17 (j + 2) m y68 y43 y44 y45 (by omega) (by omega) hu' ht' hK hti hw'
      fun hh => ⟨hI' hh, hz⟩, by rank_lt⟩
  · rw [if_neg (mt ofBool_beq_one.mp hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, h74]
    have hj' : j + 2 ≠ 255 := fun h => hz (h ▸ ht')
    exact ⟨Reach.bb15 (j + 2) m y68 y43 y44 y45 (by omega) (by omega) hu' ht' hK hti hw'
      fun hh => ⟨hI' hh, Inner.one (hI' hh) (by omega) (by omega) hz⟩, by rank_lt⟩

theorem step_bb15 {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmc : m < c) (hc : c ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y68 (2 ^ c) ∧ slot w c = 1#16) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 14 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y43, r32 y44, r32 y45, v64 m, v32 c, r16 y68, vp (slotPtr slides c)]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 16, SLLVM.Ty.ptr]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨14, rfl, [r32 y43, r32 y44, r32 y45, v64 m, v32 c, r16 y68, vp (slotPtr slides c)]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 77
  denote_step_reduce v 77 [LLVM.const?] fold
  try simp only [simp_spine] at hv77
  refine term_br ⟨fun _ h => absurd h (by simp), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hv77, sext64 (show c < 2 ^ 31 by omega)]
  exact ⟨Reach.bb18 c m y68 y43 y44 y45 hmc hc hu ht hK hti hw hI, by rank_lt⟩

theorem step_bb16 {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmc : m < c) (hc : c ≤ 255) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y68 (2 ^ c) ∧ slot w c = 0#16) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 15 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y43, r32 y44, r32 y45, v64 m, r16 y68, v64 c, vp (slotPtr slides c)]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨15, rfl, [r32 y43, r32 y44, r32 y45, v64 m, r16 y68, v64 c, vp (slotPtr slides c)]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 78
  denote_step_reduce v 78 [LLVM.const?] fold
  try simp only [simp_spine] at hv78
  refine term_br ⟨fun _ h => absurd h (by simp), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hv78, trunc32 (show c < 2 ^ 32 by omega)]
  exact ⟨Reach.bb17 c m y68 y43 y44 y45 hmc hc hu ht hK hti hw hI, by rank_lt⟩

theorem step_bb17 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmc : m < c) (hc : c ≤ 255) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y68 (2 ^ c) ∧ slot w c = 0#16) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 16 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v32 c, vp (slotPtr slides c), r32 y43, r32 y44, r32 y45, v64 m, r16 y68]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨16, rfl, [v32 c, vp (slotPtr slides c), r32 y43, r32 y44, r32 y45, v64 m, r16 y68]ₕ⟩ u) p u' := by
  denote_reduce_get
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides c) 1#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c5]
      rw [run_liftM (run_store_slot hsl hu (by omega) 1#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show c < 256 by omega) 1#16
  refine term_br ⟨fun _ h => absurd h (by simp), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine]
  refine ⟨Reach.bb22 c m y68 y43 y44 y45 hmc hc hu' ?_ hK hti (hw.store256 bnd_one (by omega))
    (fun hh => Inner.set (hI hh).1 (hI hh).2 hmc (by omega)), by rank_lt⟩
  by_cases hc1 : c = 255
  · exact Or.inr hc1
  · exact Or.inl (by rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht)

theorem step_bb18 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (y68 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmc : m < c) (hc : c ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y68) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y68 (2 ^ c) ∧ slot w c = 1#16) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 17 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v64 c, vp (slotPtr slides c), r32 y43, r32 y44, r32 y45, v64 m, r16 y68]ₕ : HVector toType [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨17, rfl, [v64 c, vp (slotPtr slides c), r32 y43, r32 y44, r32 y45, v64 m, r16 y68]ₕ⟩ u) p u' := by
  denote_reduce_get
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides c) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c8]
      rw [run_liftM (run_store_slot hsl hu (by omega) 0#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show c < 256 by omega) 0#16
  have ht' : slot (spliceBits w (16 * c) 0#16) 255 = 0 :=
    (by rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht)
  have hw' := hw.store256 bnd_zero (show c < 256 by omega)
  have hI' : H → Inner Nv (spliceBits w (16 * c) 0#16) m y68 (2 ^ (c + 1)) := fun hh =>
    Inner.clear_carry (hI hh).1 (hI hh).2 hmc (by omega)
  denote_number_from 83
  denote_step_reduce v 84 [LLVM.const?] fold
  simp only [simp_spine, hV.c6, hV.arg0] at hv83 hv84
  rw [add64 _ (show c + 1 < 2 ^ 63 by omega)] at hv83 hv84
  have h84 : v84 = PoisonOr.value (slotPtr slides (c + 1)) := by rw [hv84, gep_slot]
  clear hv84
  rw [BlockCom.run_denote_var_of_value (x := (PoisonOr.value (slot (spliceBits w (16 * c) 0#16) (c + 1)) : LLVM.IntW 16)) (s' := { u with mem := u.mem.splice (slotPtr slides c) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h84]
      rw [run_liftM (run_load_slot hsl hu' (by omega))]; rfl)]
  denote_step_reduce v 86 [LLVM.const?] fold
  simp only [simp_spine, hV.c8] at hv86
  refine term_condBr (b := BitVec.ofBool (slot (spliceBits w (16 * c) 0#16) (c + 1) == 0#16))
    (by simp only [simp_spine, hv86]; rfl) ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hz : slot (spliceBits w (16 * c) 0#16) (c + 1) = 0#16
  · rw [if_pos (ofBool_beq_one.mpr hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv83, h84]
    exact ⟨Reach.bb16 (c + 1) m y68 y43 y44 y45 (by omega) (by omega) hu' ht' hK hti hw'
      fun hh => ⟨hI' hh, hz⟩, by rank_lt⟩
  · rw [if_neg (mt ofBool_beq_one.mp hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv83, h84]
    have hc' : c + 1 ≠ 255 := fun h => hz (h ▸ ht')
    exact ⟨Reach.bb18 (c + 1) m y68 y43 y44 y45 (by omega) (by omega) hu' ht' hK hti hw'
      fun hh => ⟨hI' hh, Inner.one (hI' hh) (by omega) (by omega) hz⟩, by rank_lt⟩

theorem step_bb19 (hV : EntryEnv V slides n bits) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (y87 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmc : m < c) (hc : c ≤ 255) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y87) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y87 0) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 18 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r16 y87, r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (c + 1), v64 c]ₕ : HVector toType [SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨18, rfl, [r16 y87, r32 y43, r32 y44, r32 y45, v32 m, v64 m, v32 (c + 1), v64 c]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 88
  denote_step_reduce v 89 [LLVM.const?] fold
  simp only [simp_spine, hV.c7, hV.c16] at hv88 hv89
  rw [icmp_eq_ofNat (by omega) (by omega)] at hv88
  refine term_condBr (by simp only [simp_spine, hv88]; rfl)
    ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hc1 : c = 255
  · rw [if_pos (ofBool_eq_one.mpr hc1)]
    simp only [Target.denote_mk, HVector.map, simp_spine]
    exact ⟨Reach.bb20 m y87 (by omega) hu hti hw fun hh => Inner.last (hI hh), by rank_lt⟩
  · rw [if_neg (mt ofBool_eq_one.mp hc1)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv89, add32 _ (show c + 1 + 1 < 2 ^ 31 by omega)]
    exact ⟨Reach.bb9 c m y87 y43 y44 y45 (by omega) (by omega) hu ht hK hti hw hI, by rank_lt⟩

theorem step_bb20 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (m : Nat) (y91 : BitVec 16) (hm : m ≤ 255) (hu : u ≈ Sw s slides w) (hti : Ti bits y91) (hw : BndUpTo bits w 256)
    (hI : H → SumEq Nv w ((y91.toInt - 1) * 2 ^ m) ∧ slot w m = 1#16) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 19 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v64 m, r16 y91]ₕ : HVector toType [SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨19, rfl, [v64 m, r16 y91]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 92
  denote_step_reduce v 92 [LLVM.const?] fold
  simp only [simp_spine, hV.arg0] at hv92
  have h92 : v92 = PoisonOr.value (slotPtr slides m) := by rw [hv92, gep_slot]
  clear hv92
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides m) y91 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h92]
      rw [run_liftM (run_store_slot hsl hu (by omega) y91)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show m < 256 by omega) y91
  refine term_br ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  exact ⟨Reach.bb23 hu' (hw.store256 hti.bnd (by omega)) fun hh => SumEq.finish (hI hh) (by omega),
    by rank_lt⟩

theorem step_bb21 {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (y52 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmc : m < c) (hc : c ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) (hK : K bits y43 y44 y45) (hti : Ti bits y52) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y52 0 ∧ slot w c = 1#16) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 20 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([r32 y43, r32 y44, r32 y45, v64 m, r16 y52, v64 c]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨20, rfl, [r32 y43, r32 y44, r32 y45, v64 m, r16 y52, v64 c]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 93
  denote_step_reduce v 93 [LLVM.const?] fold
  try simp only [simp_spine] at hv93
  refine term_br ⟨fun _ h => absurd h (by simp), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hv93, trunc32 (show c < 2 ^ 32 by omega)]
  exact ⟨Reach.bb22 c m y52 y43 y44 y45 hmc (by omega) hu (Or.inl ht) hK hti hw hI, by rank_lt⟩

theorem step_bb22 (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (y95 : BitVec 16) (y43 y44 y45 : BitVec 32)
    (hmc : m < c) (hc : c ≤ 255) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0 ∨ c = 255) (hK : K bits y43 y44 y45) (hti : Ti bits y95) (hw : BndUpTo bits w 256)
    (hI : H → Inner Nv w m y95 0 ∧ slot w c = 1#16) :
    ∃ p u', StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 21 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v32 c, r16 y95, r32 y43, r32 y44, r32 y45, v64 m]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = .value (p, u') ∧ Post s slides bits H Nv (μ ⟨21, rfl, [v32 c, r16 y95, r32 y43, r32 y44, r32 y45, v64 m]ₕ⟩ u) p u' := by
  denote_reduce_get
  denote_number_from 96
  denote_step_reduce v 96 [LLVM.const?] fold
  simp only [simp_spine, hV.arg0] at hv96
  have h96 : v96 = PoisonOr.value (slotPtr slides m) := by rw [hv96, gep_slot]
  clear hv96
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides m) y95 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h96]
      rw [run_liftM (run_store_slot hsl hu (by omega) y95)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show m < 256 by omega) y95
  have ht' : slot (spliceBits w (16 * m) y95) 255 = 0 ∨ c = 255 := by
    rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht
  denote_step_reduce v 97 [LLVM.const?] fold
  simp only [simp_spine, hV.c9] at hv97
  rw [icmp_slt32 (by omega) (by omega)] at hv97
  refine term_condBr (by simp only [simp_spine, hv97]; rfl)
    ⟨fun _ h => (nomatch h), fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  rw [if_pos (ofBool_eq_one.mpr (by omega))]
  simp only [Target.denote_mk, HVector.map, simp_spine]
  exact ⟨Reach.bb7 c y43 y44 y45 hc hu' ht' hK (hw.store256 hti.bnd (by omega))
    fun hh => Inner.finish (hI hh).1 (hI hh).2 hmc (by omega), by rank_lt⟩

end Steps

theorem steps {s : GlobalState} {slides n : Pointer} {bits : BitVec 32} {H : Prop} {Nv : Nat}
    {V : fd_curve25519_scalar_wnaf.Γout.Valuation}
    (hs : s.WF) (hV : EntryEnv V slides n bits) (hsl : IsSlidesPtr s.mem slides)
    (hn : IsByteBufPtr s.mem n) (hH : H → Hyp bits slides n) (hNv : Nv = (readBuf hn).toNat) :
    ∀ t u, Reach s slides bits H Nv t u → ∃ p u',
      StateT.run ((fd_curve25519_scalar_wnaf.blocks.get t.idx t.hidx).2.denote
          (Ctxt.Valuation.ofHVector t.args.reverse ++ V)) u = .value (p, u')
      ∧ (∀ rs, p.2 = .inl rs → Done s slides bits H Nv u')
      ∧ (∀ t', p.2 = .inr t' → Reach s slides bits H Nv t' u' ∧ μ t' u' < μ t u) := by
  intro t u h
  cases h with
  | bb1 => exact step_bb1 hV hsl ‹_› ‹_› ‹_›
  | bb2 => exact step_bb2 hV hsl hn _ ‹_› ‹_› ‹_› ‹_› hH hNv
  | bb3 => exact step_bb3 hV hsl _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb4 => exact step_bb4 hV _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb5 => exact step_bb5 hV _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb6 => exact step_bb6 hV _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb7 => exact step_bb7 hV _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb8 => exact step_bb8 hV _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb9 => exact step_bb9 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb10 => exact step_bb10 hs hV _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› hH
  | bb11 => exact step_bb11 _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› hH
  | bb12 => exact step_bb12 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb13 => exact step_bb13 _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› hH
  | bb14 => exact step_bb14 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb15 => exact step_bb15 _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb16 => exact step_bb16 _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb17 => exact step_bb17 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb18 => exact step_bb18 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb19 => exact step_bb19 hV _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb20 => exact step_bb20 hV hsl _ _ ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb21 => exact step_bb21 _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb22 => exact step_bb22 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | bb23 => exact step_bb23 ‹_› ‹_› ‹_› _

end Wnaf

open Wnaf in
/-- **`fd_curve25519_scalar_wnaf` returns, writing the scalar's digits at `slides`.** -/
theorem fd_curve25519_scalar_wnaf_conforms (slides n : Pointer) (bits : BitVec 32) (s : GlobalState)
    (hs : s.WF) (hsl : IsSlidesPtr s.mem slides) (hn : IsByteBufPtr s.mem n)
    (hbits : bits.toNat < 32) :
    fd_curve25519_scalar_wnaf_spec slides n bits s hn := by
  simp only [fd_curve25519_scalar_wnaf_spec, Cfg.denote]
  refine run_runFunction' _ ?_
  refine (entry_run slides n bits hbits s).elim fun Vout h => h.elim fun hentry hV => ?_
  obtain ⟨blk, hblk, -⟩ := hsl.1
  have hl : s.mem.live? slides.id = some blk := by simp [MemoryState.live?, hblk]
  have hu₀ : s ≈ Sw s slides (blk.bytes.extractLsb' slides.offsetInBits 4096) :=
    ⟨rfl, rfl, fun q => (live?_splice_extract 4096 hl q).symm⟩
  obtain ⟨rs, u, hrun, w, hw, hB, hS⟩ := Blocks.run_of_variant
    (bs := fd_curve25519_scalar_wnaf.blocks) (Vamb := Vout)
    (Reach s slides bits (Hyp bits slides n) (readBuf hn).toNat) μ
    (fun _ u => Done s slides bits (Hyp bits slides n) (readBuf hn).toNat u)
    (steps hs hV hsl hn id rfl)
    (Reach.bb2 0 (by omega) hu₀ (fun _ h => absurd h (Nat.not_lt_zero _))
      fun _ _ h => absurd h (Nat.not_lt_zero _))
  refine ⟨u, ?_, w, ?_, hB, fun h13 hne => (add_zero _).symm.trans (hS ⟨h13, hne⟩)⟩
  · rw [EffectM.run_bind, hentry, PoisonOr.value_bind]
    cases rs
    exact hrun
  · refine (popFrame_equiv_splice hs (lt_nextFreeBlock_of_fits hs hsl.1)
      (fun b _ hb => ?_) (hw.live slides.id)).symm
    rw [hw.live b, live?_splice_ne (fun h => hb h.symm)]


end Firedancer.Common
