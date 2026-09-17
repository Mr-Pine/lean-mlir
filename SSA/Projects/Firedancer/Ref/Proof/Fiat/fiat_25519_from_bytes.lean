module

public import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_from_bytes
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_from_bytes
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
public import SSA.Projects.Firedancer.Ref.Proof.Limb

@[expose] public section


namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The C's `out1[k]`: the `k`-th 51-bit window of the little-endian buffer. The
C reaches it through the `x33`-`x71` add chain; the compiled region ors each
window's byte fields together directly. -/
def from_bytes_repr (buf : BitVec 256) : Fin 5 → ℕ :=
  fun i => (buf.extractLsb' (51 * i.toNat) 51).toNat

lemma from_bytes_bounds (buf : BitVec 256) : ∀ i, from_bytes_repr buf i ≤ 0x8000000000000 := by
  intro i
  have := (buf.extractLsb' (51 * i.toNat) 51).isLt
  simp only [from_bytes_repr]
  omega

/-- The windows are the buffer's low 255 bits, split at the limb boundaries;
`decodeBytes` puts them back together. -/
lemma from_bytes_eq_value (buf : BitVec 256) :
    decodeFieldElem (from_bytes_repr buf) = decodeBytes buf := by
  have key : ∀ k : ℕ, (buf.extractLsb' k 51).toNat = buf.toNat / 2 ^ k % 2 ^ 51 := by
    intro k
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have h255 : (buf.extractLsb' 0 255).toNat = buf.toNat % 2 ^ 255 := by
    rw [BitVec.extractLsb'_toNat]; simp
  have hnat : (buf.extractLsb' 0 51).toNat + (buf.extractLsb' 51 51).toNat * 2 ^ 51
      + (buf.extractLsb' 102 51).toNat * 2 ^ 102 + (buf.extractLsb' 153 51).toNat * 2 ^ 153
      + (buf.extractLsb' 204 51).toNat * 2 ^ 204 = (buf.extractLsb' 0 255).toNat := by
    rw [key, key, key, key, key, h255]
    omega
  have hcast := congrArg (fun n : ℕ => (n : ZMod _root_.p)) hnat
  -- v4.34: `push_cast` evaluates the powers in `hcast` but not in the target
  push_cast [-Nat.reducePow] at hcast
  simpa [decodeFieldElem, decodeBytes, from_bytes_repr, Fin.isValue, -Nat.reducePow] using hcast

/-- What the buffer read is, once the block behind `p` is known. -/
lemma bufBits {m : MemoryState} {p : Pointer} {blk : LiveBlock}
    (hblk : m[p.id]? = some (Block.live blk)) (h : IsByteBufPtr m p) :
    readBuf h = blk.bytes.extractLsb' p.offsetInBits 256 := by
  have hlive : m.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  simp [readBuf, readBuf?, hlive]

/-- ... and what it holds at byte `k`. The offset is a parameter, since what a
load leaves behind is only equal to `p.offsetInBits + 8 * k`, not syntactically
it. -/
lemma bufByte {m : MemoryState} {p : Pointer} {blk : LiveBlock}
    (hblk : m[p.id]? = some (Block.live blk)) (h : IsByteBufPtr m p) {k : ℕ} (hk : k < 32)
    {off : ℕ} (hoff : off = p.offsetInBits + 8 * k) :
    blk.bytes.extractLsb' off 8 = (readBuf h).extractLsb' (8 * k) 8 := by
  rw [bufBits hblk h, extractLsb'_extractLsb' _ (by omega), hoff]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem fiat_25519_from_bytes_conforms (o p: Pointer) (s: GlobalState)
  (hs : s.WF)
  (ho : IsFieldElemPtr s.mem o)
  (hp : IsByteBufPtr s.mem p) :
  fiat_25519_from_bytes_spec o p s ho hp := by
    simp only [fiat_25519_from_bytes_spec, Cfg.denote]

    obtain ⟨pblk, hpblk, hplen⟩ := id hp.left
    set buf := readBuf hp with hbuf
    let output := from_bytes_repr buf
    let outputBV := BitVec.ofNat 64 ∘ output

    have hcb : ∀ i, output i ≤ 0x8000000000000 := from_bytes_bounds buf
    have hlimb : ∀ i : Fin 5, (outputBV i).toNat = output i := by
      intro i
      have hi : output i < 2 ^ 64 := by have := hcb i; omega
      show (BitVec.ofNat 64 (output i)).toNat = output i
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

    refine ⟨outputBV, ?value, ?bounds, ?exec⟩

    case value =>
      have hread : readFieldElem? o (s.mem.splice o (packLimbs outputBV))
          = some (decodeFieldElem fun i => (outputBV i).toNat) := by
        rw [readFieldElem?_splice _ ho.left]
        simp only [extractLsb'_packLimbs]
      rw [readFieldElem_eq_of hread,
        show (fun i : Fin 5 => (outputBV i).toNat) = output from funext hlimb]
      exact from_bytes_eq_value buf
    case bounds =>
      intro i
      simp only [readLimb, limbReadbackPack s.mem o outputBV ho.left i, Option.get_some, hlimb]
      exact hcb i

    obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState,
        m = ((((s.mem.splice o (outputBV 0)).splice (o.withOffset 8) (outputBV 1)).splice
              (o.withOffset 16) (outputBV 2)).splice (o.withOffset 24) (outputBV 3)).splice
              (o.withOffset 32) (outputBV 4) := ⟨_, rfl⟩
    refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
    case equiv =>
      have hnone : ∀ (b : BlockId), s.alloc.nextFreeBlock ≤ b.id → outMem.live? b = none := by
        rw [houtMem]
        exact fun b hb => live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none
          (live?_splice_eq_none (live?_splice_eq_none (hs b hb)))))
      refine GlobalState.Equiv.trans ?_ (GlobalState.Equiv.symm
        (killFrom_equiv_of_none (s := s) (m := outMem) hnone))
      rw [houtMem]
      exact GlobalState.Equiv.symm
        (splice5_equiv (outputBV 0) (outputBV 1) (outputBV 2) (outputBV 3) (outputBV 4) ho)

    denote_step_all v 34
    eval_consts v 0 34

    have hpoff : ∀ (k : ℕ) (off : BitVec 64), k ≤ 31 → off.toNat = k →
        (p.withOffset off).offsetInBits = p.offsetInBits + 8 * k :=
      fun k _ hk hoff => byteOffsetInBits hp.right hk hoff
    have hpbyte : ∀ (k off : ℕ), k < 32 → off = p.offsetInBits + 8 * k →
        pblk.bytes.extractLsb' off 8 = buf.extractLsb' (8 * k) 8 :=
      fun k off hk hoff => bufByte hpblk hp hk hoff

    peel_buf_bytes p, hp, pblk, hpblk, buf, hpoff, hpbyte
    -- v4.34: `bv_decide` fails on *any* goal while `hpbyte` is in scope; it is dead
    -- after the peel, so drop it (and `hpoff` with it).
    clear hpoff hpbyte

    -- `arg1[0]`-`arg1[3]`, the C's `x32` and `x31`-`x29`, arrive as one 32-bit
    -- load off the base pointer
    peel_load (.bitvec (.concrete 32)), pblk, p, hpblk, s
    set arg₀ := pblk.bytes.extractLsb' p.offsetInBits 32 with harg₀
    have hpword : pblk.bytes.extractLsb' p.offsetInBits 32 = buf.extractLsb' 0 32 := by
      rw [hbuf, bufBits hpblk hp, extractLsb'_extractLsb' _ (by omega), Nat.add_zero]
    rw [show arg₀ = buf.extractLsb' 0 32 from harg₀.trans hpword]
    clear harg₀ arg₀

    denote_step_all v 185
    -- in four chunks: one `denote_eval` over all 150 instructions times out
    denote_eval v 37 87
    denote_eval v 88 127
    denote_eval v 128 162
    denote_eval v 163 185

    have key : v153 = PoisonOr.value (outputBV 0) ∧ v161 = PoisonOr.value (outputBV 1)
        ∧ v170 = PoisonOr.value (outputBV 2) ∧ v178 = PoisonOr.value (outputBV 3)
        ∧ v185 = PoisonOr.value (outputBV 4) := by
      -- `x1`-`x28`: each byte masked (only `arg1[31]`), widened and shifted into place
      eval_llvm_range 37 38
      eval_llvm 39 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x1
      eval_llvm_range 40 42
      eval_llvm 43 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x2
      eval_llvm_range 44 46
      eval_llvm 47 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x3
      eval_llvm_range 48 50
      eval_llvm 51 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x4
      eval_llvm_range 52 54
      eval_llvm 55 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x5
      eval_llvm_range 56 58
      eval_llvm 59 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x6
      eval_llvm_range 60 62
      eval_llvm 63 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x7
      eval_llvm_range 64 66
      eval_llvm 67 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x8
      eval_llvm_range 68 70
      eval_llvm 71 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x9
      eval_llvm_range 72 74
      eval_llvm 75 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x10
      eval_llvm_range 76 78
      eval_llvm 79 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x11
      eval_llvm_range 80 82
      eval_llvm 83 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x12
      eval_llvm_range 84 86
      eval_llvm 87 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x13
      eval_llvm_range 88 90
      eval_llvm 91 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x14
      eval_llvm_range 92 94
      eval_llvm 95 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x15
      eval_llvm_range 96 98
      eval_llvm 99 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x16
      eval_llvm_range 100 102
      eval_llvm 103 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x17
      eval_llvm_range 104 106
      eval_llvm 107 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x18
      eval_llvm_range 108 110
      eval_llvm 111 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x19
      eval_llvm_range 112 114
      eval_llvm 115 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x20
      eval_llvm_range 116 118
      eval_llvm 119 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x21
      eval_llvm_range 120 122
      eval_llvm 123 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x22
      eval_llvm_range 124 126
      eval_llvm 127 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x23
      eval_llvm_range 128 130
      eval_llvm 131 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x24
      eval_llvm_range 132 134
      eval_llvm 135 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x25
      eval_llvm_range 136 138
      eval_llvm 139 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x26
      eval_llvm_range 140 142
      eval_llvm 143 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x27
      eval_llvm_range 144 146
      eval_llvm 147 [zext8_shl_ushr_ofNat, zext8_shl_sshr_ofNat] as x28

      -- the C's `x29`-`x32` are `arg1[3]`-`arg1[0]` shifted; the compiler reads
      -- all four in one 32-bit load, so they share a name here
      eval_llvm_range 148 148
      eval_llvm 149 as x29_32

      -- the four limbs and the carry each hands the next. The or-chains between
      -- them are the compiler's, not the C's: `x33`-`x38` and their counterparts
      -- accumulate a limb by addition, where this ors disjoint byte fields.
      eval_llvm_range 150 152
      eval_llvm 153 as x39
      eval_llvm 154 as x40
      eval_llvm_range 155 160
      eval_llvm 161 as x47
      eval_llvm 162 as x48
      -- The three limb adds carry `nsw, nuw`, so each needs its operands bounded.
      -- One operand is the incoming carry; the other is the or of that limb's
      -- byte fields, which the C has no name for -- it accumulates a limb by
      -- adding one field at a time (`x49`-`x55` for this one), carrying the
      -- incoming `x48` along, where the compiler ors the fields and adds the
      -- carry once at the end.
      eval_llvm_range 163 167
      eval_llvm 168 as limb2_fields
      have bf2 : limb2_fields ≤ 288230376151711743#64 := by
        rw [← hlimb2_fields, ← hx13, ← hx14, ← hx15, ← hx16, ← hx17, ← hx18, ← hx19]
        bv_decide
      have bc2 : x48 ≤ 3#64 := by rw [← hx48]; bv_decide
      have hb2 : limb2_fields.toNat + x48.toNat < 2 ^ 63 := by
        simp only [BitVec.le_def, BitVec.toNat_ofNat] at bf2 bc2; omega
      have hb2' : limb2_fields.toNat + x48.toNat < 2 ^ 64 := by omega
      eval_llvm 169 [saddOverflow_eq_false hb2, uaddOverflow_eq_false hb2'] as x55
      eval_llvm 170 as x56
      eval_llvm 171 as x57

      eval_llvm_range 172 175
      eval_llvm 176 as limb3_fields
      have bf3 : limb3_fields ≤ 36028797018963967#64 := by
        rw [← hlimb3_fields, ← hx7, ← hx8, ← hx9, ← hx10, ← hx11, ← hx12]
        bv_decide
      have bc3 : x57 ≤ 128#64 := by rw [← hx57, ← hx55]; bv_decide
      have hb3 : limb3_fields.toNat + x57.toNat < 2 ^ 63 := by
        simp only [BitVec.le_def, BitVec.toNat_ofNat] at bf3 bc3; omega
      have hb3' : limb3_fields.toNat + x57.toNat < 2 ^ 64 := by omega
      eval_llvm 177 [saddOverflow_eq_false hb3, uaddOverflow_eq_false hb3'] as x63
      eval_llvm 178 as x64
      eval_llvm 179 as x65

      eval_llvm_range 180 183
      eval_llvm 184 as limb4_fields
      have bf4 : limb4_fields ≤ 2251799813685247#64 := by
        rw [← hlimb4_fields, ← hx1, ← hx2, ← hx3, ← hx4, ← hx5, ← hx6]
        bv_decide
      have bc4 : x65 ≤ 16#64 := by rw [← hx65, ← hx63]; bv_decide
      have hb4 : limb4_fields.toNat + x65.toNat < 2 ^ 63 := by
        simp only [BitVec.le_def, BitVec.toNat_ofNat] at bf4 bc4; omega
      have hb4' : limb4_fields.toNat + x65.toNat < 2 ^ 64 := by omega
      eval_llvm 185 [saddOverflow_eq_false hb4, uaddOverflow_eq_false hb4'] as x71

      -- each limb is `from_bytes_repr`'s window of the buffer, widened
      have hbv : ∀ i : Fin 5, outputBV i = (buf.extractLsb' (51 * i.toNat) 51).setWidth 64 := by
        intro i
        have hlt := (buf.extractLsb' (51 * i.toNat) 51).isLt
        apply BitVec.eq_of_toNat_eq
        simp only [outputBV, Function.comp_apply, output, from_bytes_repr, BitVec.toNat_ofNat,
          BitVec.toNat_setWidth]
      -- `as` makes each value an atom, which is what keeps the or-chains from
      -- growing as they are evaluated; `bv_decide` cannot see through an atom, so
      -- the definitions go back into the five limb equations before it runs. The
      -- byte terms are already in the buffer's vocabulary: `peel_buf_bytes`
      -- rewrites them before the stepper generalizes each value into its `hv`.
      simp only [← hx1, ← hx2, ← hx3, ← hx4, ← hx5, ← hx6, ← hx7, ← hx8, ← hx9, ← hx10, ← hx11,
        ← hx12, ← hx13, ← hx14, ← hx15, ← hx16, ← hx17, ← hx18, ← hx19, ← hx20, ← hx21, ← hx22,
        ← hx23, ← hx24, ← hx25, ← hx26, ← hx27, ← hx28, ← hx29_32, ← hx40, ← hx48, ← hx57, ← hx65,
        ← hlimb2_fields, ← hlimb3_fields, ← hlimb4_fields, ← hx55, ← hx63]
        at hx39 hx47 hx56 hx64 hx71
      -- and the byte terms move into the buffer's vocabulary. The pointer lets are
      -- unfolded in the same pass: the equations are stated over `p.withOffset k`,
      -- while the loads left the let-bound `p<k>` behind.
      simp only [p₃₁, p₃₀, p₂₉, p₂₈, p₂₇, p₂₆, p₂₅, p₂₄, p₂₃, p₂₂, p₂₁, p₂₀, p₁₉, p₁₈, p₁₇, p₁₆, p₁₅, p₁₄, p₁₃, p₁₂, p₁₁, p₁₀, p₉, p₈, p₇, p₆, p₅, p₄,
        hpword, hbyte₃₁, hbyte₃₀, hbyte₂₉, hbyte₂₈, hbyte₂₇, hbyte₂₆, hbyte₂₅, hbyte₂₄, hbyte₂₃, hbyte₂₂, hbyte₂₁, hbyte₂₀, hbyte₁₉, hbyte₁₈, hbyte₁₇, hbyte₁₆, hbyte₁₅, hbyte₁₄, hbyte₁₃, hbyte₁₂, hbyte₁₁, hbyte₁₀, hbyte₉, hbyte₈, hbyte₇, hbyte₆, hbyte₅, hbyte₄]
        at hx39 hx47 hx56 hx64 hx71

      -- at literal offsets, so `51 * Fin.toNat i` never reaches the solver
      have hbv0 : outputBV 0 = (buf.extractLsb' 0 51).setWidth 64 := hbv 0
      have hbv1 : outputBV 1 = (buf.extractLsb' 51 51).setWidth 64 := hbv 1
      have hbv2 : outputBV 2 = (buf.extractLsb' 102 51).setWidth 64 := hbv 2
      have hbv3 : outputBV 3 = (buf.extractLsb' 153 51).setWidth 64 := hbv 3
      have hbv4 : outputBV 4 = (buf.extractLsb' 204 51).setWidth 64 := hbv 4

      refine ⟨hv153.trans (congrArg _ ?_), hv161.trans (congrArg _ ?_),
        hv170.trans (congrArg _ ?_), hv178.trans (congrArg _ ?_), hv185.trans (congrArg _ ?_)⟩
      · rw [← hx39, hbv0]
        bv_decide
      · rw [← hx47, hbv1]
        bv_decide
      · rw [← hx56, hbv2]
        bv_decide
      · rw [← hx64, hbv3]
        bv_decide
      · rw [← hx71, hbv4]
        bv_decide

    obtain ⟨k0, k1, k2, k3, k4⟩ := key
    rw [k0, k1, k2, k3, k4]

    store_limbs outputBV, o, ho.left, s

    simp only [BlockCom.denote_term, Terminator.denote_ret, houtMem,
      hs₁, hs₂, hs₃, hs₄, o₁, o₂, o₃, o₄, simp_denote, simp_sllvm]

end Firedancer.Ref
