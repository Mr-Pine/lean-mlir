/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_r43x6_ge_decode2
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
import SSA.Projects.Firedancer.Avx512.Proof.Step.wv_ld
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_unpack
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_pow22523_2
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_r43x6_ge_decode2_blocks
import SSA.Projects.Firedancer.Avx512.Proof.Sub

/-!
# `fd_r43x6_ge_decode2` conforms to its spec

Header only: the statement, the return value, and the `runFunction` peel. The
return value has to be supplied before the state (`run_runFunction'` takes the
state last), so it is named first, as the `ref` walks do.

What is left is the region's five blocks: the two `memcpy`s and unpacks, the
shared `u`/`v` chain, `fd_r43x6_pow22523_2`, the two square-root branches, and
the sign fixup through `fd_r43x6_diagnose`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/- Scaffolding for the `fd_r43x6_ge_decode2` derivation. Only
`fd_r43x6_ge_decode2_conforms`, below, escapes. -/
namespace GeDecode2

/-! ### The frame

Four locals, and unlike `fd_r43x6_pow22523_2`'s twenty they are not all one
width: `_sa`/`_sb` are the 32-byte staging buffers `memcpy` fills, `t0a`/`t0b`
the `wwl_t` out-parameters of the inlined `FD_R43X6_POW22523_2_INL`. -/

/-- The four locals' widths, in allocation order. -/
def cw : Nat → Nat
  | 0 => 256
  | 1 => 256
  | _ => 512

/-- The locals as pointers: consecutive blocks from the entry counter. -/
def slotPtr (s : GlobalState) (k : Nat) : Pointer := s.chainPtr cw k

namespace Slot

/-- `%45` -- `ulong _sa[4]`, the buffer `memcpy( _sa, _vsa, 32 )` fills. -/
def sa : Nat := 0
/-- `%46` -- `ulong _sb[4]`. -/
def sb : Nat := 1
/-- `%47` -- `t0a`, the first out-parameter of `FD_R43X6_POW22523_2_INL`. -/
def t0a : Nat := 2
/-- `%48` -- `t0b`. -/
def t0b : Nat := 3

end Slot

/-- Fold a pointer the `alloca` prologue leaves expanded back to `slotPtr s k`. -/
@[simp] theorem slotPtr_sa (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 0).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.sa := rfl
@[simp] theorem slotPtr_sb (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 1).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.sb := rfl
@[simp] theorem slotPtr_t0a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 2).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.t0a := rfl
@[simp] theorem slotPtr_t0b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 3).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.t0b := rfl

/-- The frame the four `alloca`s allocate: consecutive blocks from the entry
counter `n₀`, with all eight of the caller's pointers strictly below it. -/
structure Slots (t : Nat → Pointer) (n₀ : Nat) : Prop where
  id : ∀ k, (t k).id.id = n₀ + k
  off : ∀ k, (t k).offset = 0

/-- Distinct locals are distinct blocks. -/
theorem Slots.ne {t : Nat → Pointer} {n₀ i j : Nat} (hs : Slots t n₀) (hij : i ≠ j) :
    (t i).id ≠ (t j).id := fun h => by
  have hi := hs.id i; have hj := hs.id j
  have h' : (t i).id.id = (t j).id.id := by rw [h]
  omega

/-- What holds of a state part-way through the region. -/
structure Frame (t : Nat → Pointer) (n₀ : Nat) (s₀ u : GlobalState) : Prop where
  wf : u.WF
  fits : ∀ k, k < 4 → Fits u.mem (t k) (cw k)
  fb : FrameBelow n₀ s₀ u

/-- The prologue's facts, with the state it reaches handed out opaquely --
`hsAlloc` is the only place `allocaChain` is written, which is what keeps every
later `isDefEq` off the four-step chain. -/
theorem exists_slots_frame (s : GlobalState) (hs : s.WF) :
    ∃ sAlloc : GlobalState, sAlloc = s.allocaChain cw 4
      ∧ Slots (slotPtr s) s.alloc.nextFreeBlock
      ∧ Frame (slotPtr s) s.alloc.nextFreeBlock s sAlloc :=
  ⟨_, rfl,
   { id := fun k => GlobalState.chainPtr_id k
     off := fun k => GlobalState.chainPtr_offset k },
   { wf := GlobalState.WF.allocaChain hs 4
     fits := fun _ hk => GlobalState.fits_chainPtr hk
     fb := FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 4 }⟩

/-- `%20` -- the curve constant `d`, in r43x6 limbs. -/
def dVec : Vector (BitVec 64) 8 :=
  #v[6365466163363, 253762649449, 7518893317, 260847760460, 7696165686388, 704489577558, 0, 0]

theorem dVec_u47 : R43x6.U47 (dVec.take R43x6.limbCount) := by
  constructor <;> intro i <;> fin_cases i <;>
    simp [LimbRepresentations.toInts, dVec]
theorem dVec_six : dVec[6] = 0 := rfl
theorem dVec_seven : dVec[7] = 0 := rfl

/-- ... and it is `d`. -/
theorem vecValue_dVec : vecValue dVec = Ed25519.d := by
  have h0 : (6365466163363 : BitVec 64).toNat = 6365466163363 := rfl
  have h1 : (253762649449 : BitVec 64).toNat = 253762649449 := rfl
  have h2 : (7518893317 : BitVec 64).toNat = 7518893317 := rfl
  have h3 : (260847760460 : BitVec 64).toNat = 260847760460 := rfl
  have h4 : (7696165686388 : BitVec 64).toNat = 7696165686388 := rfl
  have h5 : (704489577558 : BitVec 64).toNat = 704489577558 := rfl
  norm_num [vecValue_eq_decodeNat, decodeNat_eq, limbNat, dVec, Ed25519.d, h0, h1, h2, h3, h4, h5]

end GeDecode2

open GeDecode2 in
open scoped Classical in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem fd_r43x6_ge_decode2_conforms (a03 a14 a25 vsa b03 b14 b25 vsb : Pointer)
    (s : GlobalState) (hs : s.WF)
    (ha03 : IsVecPtr s.mem a03) (ha14 : IsVecPtr s.mem a14) (ha25 : IsVecPtr s.mem a25)
    (hb03 : IsVecPtr s.mem b03) (hb14 : IsVecPtr s.mem b14) (hb25 : IsVecPtr s.mem b25)
    (hvsa : IsWvPtr s.mem vsa) (hvsb : IsWvPtr s.mem vsb)
    -- the six out-vectors are six distinct blocks: what the reload after the
    -- QUAD transpose needs, and the C's contract
    (hne : GeDecode2.SixDistinct a03 a14 a25 b03 b14 b25) :
    fd_r43x6_ge_decode2_spec a03 a14 a25 vsa b03 b14 b25 vsb s
      ha03 ha14 ha25 hb03 hb14 hb25 hvsa hvsb := by
  obtain ⟨sAlloc, hsAlloc, slots, frame⟩ := GeDecode2.exists_slots_frame s hs
  simp only [fd_r43x6_ge_decode2_spec, Cfg.denote]
  apply Firedancer.existsISecond
    (if Decodable (readWv hvsa) then
      (if Decodable (readWv hvsb) then (.value 0#32 : LLVM.IntW 32) else .value (-2#32))
     else .value (-1#32))
  refine Firedancer.run_runFunction' _ ?_
  -- %0-%44: the constants, and the `undef`/`insertelement` chain that builds
  -- the all-poison vector the shuffles take as their dead operand
  denote_step_reduce v 44 [LLVM.const?, LLVM.Ty.poison]
  -- the scalars this stretch reads: `%29 = 32` (the `memcpy` length), `%30 = 63`
  -- and `%31 = 2^63-1` the sign split
  subst hv29 hv30 hv31
  -- %45-%48: `_sa`, `_sb`, `t0a`, `t0b`
  peel_alloca_chain s, cw, 4
  simp only [slotPtr_sa, slotPtr_sb, slotPtr_t0a, slotPtr_t0b]
  rw [← hsAlloc]

  -- Newly allocated slots are valid ptrs
  have hsa : IsWvPtr sAlloc.mem (slotPtr s Slot.sa) :=
    ⟨frame.fits Slot.sa (by decide), by simp [slots.off Slot.sa]⟩
  have hsb : IsWvPtr sAlloc.mem (slotPtr s Slot.sb) :=
    ⟨frame.fits Slot.sb (by decide), by simp [slots.off Slot.sb]⟩

  -- the staging buffers' lifetimes, then `memcpy( _sa, _vsa, 32 )` and its `b`
  -- twin: 32 bytes off the caller's encoding into the frame
  iterate 2 peel_lifetime
  have hsaF : Fits sAlloc.mem (slotPtr s Slot.sa) (8 * 32) := frame.fits 0 (by decide)
  have hsbF : Fits sAlloc.mem (slotPtr s Slot.sb) (8 * 32) := frame.fits 1 (by decide)
  have hvsa' : Fits sAlloc.mem vsa (8 * 32) :=
    fits_of_live?_eq (frame.fb vsa.id (lt_nextFreeBlock_of_fits hs hvsa.1)) hvsa.1
  have hvsb' : Fits sAlloc.mem vsb (8 * 32) :=
    fits_of_live?_eq (frame.fb vsb.id (lt_nextFreeBlock_of_fits hs hvsb.1)) hvsb.1
  refine name_of ({ sAlloc with mem := sAlloc.mem.splice (slotPtr s Slot.sa) (BitVec.extractLsb' vsa.offsetInBits (8 * 32) hvsa'.choose.bytes) }) fun m₁ hm₁ => ?_
  peel_memcpy 32, (slotPtr s Slot.sa), vsa, hvsa', hsaF, sAlloc as m₁ := hm₁
  -- and `memcpy( _sb, _vsb, 32 )`, at the state the first one left
  have hvsb'' := (hm₁ ▸ fits_splice hvsb' : Fits m₁.mem vsb (8 * 32))
  have hsbF := (hm₁ ▸ fits_splice hsbF : Fits m₁.mem (slotPtr s Slot.sb) (8 * 32))
  refine name_of ({ m₁ with mem := m₁.mem.splice (slotPtr s Slot.sb) (BitVec.extractLsb' vsb.offsetInBits (8 * 32) hvsb''.choose.bytes) }) fun m₂ hm₂ => ?_
  peel_memcpy 32, (slotPtr s Slot.sb), vsb, hvsb'', hsbF, m₁ as m₂ := hm₂

  have hsaF := (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice hsaF) : Fits m₂.mem (slotPtr s Slot.sa) (8 * 32))
  peel_gep 24 with (slotPtr s Slot.sa), hsaF, m₂ as pa_high
  obtain ⟨a_high_blk, ha_high_blk, ha_high_len⟩ := id hpa_high
  have hfitA : pa_high.offsetInBits + 64 ≤ a_high_blk.lengthInBits := by
    simpa [pa_high] using ha_high_len
  peel_load (.bitvec (.concrete 64)), a_high_blk, pa_high, ha_high_blk, m₂

  have hsbF := (hm₂ ▸ fits_splice hsbF : Fits m₂.mem (slotPtr s Slot.sb) (8 * 32))
  peel_gep 24 with (slotPtr s Slot.sb), hsbF, m₂ as pb_high
  obtain ⟨b_high_blk, hb_high_blk, hb_high_len⟩ := id hpb_high
  have hfitB : pb_high.offsetInBits + 64 ≤ b_high_blk.lengthInBits := by
    simpa [pb_high] using hb_high_len
  peel_load (.bitvec (.concrete 64)), b_high_blk, pb_high, hb_high_blk, m₂

  denote_step_reduce v 58 [LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.trunc, LLVM.trunc?] fold

  -- what `_sa`'s block holds in `m₂`: the `sb` copy missed it, the `sa` copy
  -- spliced the caller's 32 bytes in at offset `0`
  have hblkA : a_high_blk
      = { hsa.1.choose with
            bytes := spliceBits hsa.1.choose.bytes (slotPtr s Slot.sa).offsetInBits
                (BitVec.extractLsb' vsa.offsetInBits (8 * 32) hvsa'.choose.bytes) } := by
    have h := ha_high_blk
    simp only [Pointer.withOffset, hm₂, hm₁,
      getElem?_splice_ne (slots.ne (show Slot.sb ≠ Slot.sa by decide)),
      getElem?_splice_self hsa.1.choose_spec.1] at h
    simpa using h.symm
  -- the source side of the `memcpy`: `vsa`'s block is the one `sAlloc` copied
  -- from, `frame.fb` being what says the prologue left it alone
  have hliveVsa : s.mem.live? vsa.id = some hvsa'.choose :=
    (frame.fb vsa.id (lt_nextFreeBlock_of_fits hs hvsa.1)).symm.trans
      (live?_of_getElem? hvsa'.choose_spec.1)
  -- every lane, not just the sign one: the whole quad is read back after the
  -- store, and `wv_ld` wants all four
  have hlanesA : ∀ (j : Nat) (hj : j < 4),
      a_high_blk.bytes.extractLsb' ((slotPtr s Slot.sa).offsetInBits + 64 * j) 64
        = (readWv hvsa)[j] := by
    intro j hj
    have hlenSlot := hsa.1.choose_spec.2
    simp only [LiveBlock.lengthInBits] at hlenSlot
    -- the equation is at `BitVec 64`, so swapping the block in is not a
    -- dependent rewrite
    rw [hblkA]
    show BitVec.extractLsb' ((slotPtr s Slot.sa).offsetInBits + 64 * j) 64
        (spliceBits hsa.1.choose.bytes (slotPtr s Slot.sa).offsetInBits
          (BitVec.extractLsb' vsa.offsetInBits (8 * 32) hvsa'.choose.bytes)) = _
    rw [extractLsb'_spliceBits_of_subrange _ _ _ _ (by omega) (by omega) (by omega),
      Nat.add_sub_cancel_left,
      BitVec.extractLsb'_extractLsb'_add_of_le (show 64 * j + 64 ≤ 8 * 32 from by omega)]
    simp [readWv, readWv?, hliveVsa]
  have hoffPa : pa_high.offsetInBits = (slotPtr s Slot.sa).offsetInBits + 64 * 3 := by
    simp [pa_high, Pointer.withOffset, Pointer.offsetInBits, slots.off Slot.sa]
  have hlaneA : a_high_blk.bytes.extractLsb' pa_high.offsetInBits 64 = (readWv hvsa)[3] := by
    rw [hoffPa]; exact hlanesA 3 (by omega)

  -- `_sb`'s block in `m₂`, the same argument one state along: its copy is the
  -- last thing that touched it, so there is no `_splice_ne` step
  have hsb : IsWvPtr m₁.mem (slotPtr s Slot.sb) :=
    ⟨(hm₁ ▸ fits_splice (frame.fits 1 (by decide)) :
        Fits m₁.mem (slotPtr s Slot.sb) (8 * 32)), by simp [slots.off Slot.sb]⟩
  have hblkB : b_high_blk
      = { hsb.1.choose with
            bytes := spliceBits hsb.1.choose.bytes (slotPtr s Slot.sb).offsetInBits
                (BitVec.extractLsb' vsb.offsetInBits (8 * 32) hvsb''.choose.bytes) } := by
    have h := hb_high_blk
    simp only [Pointer.withOffset, hm₂, getElem?_splice_self hsb.1.choose_spec.1] at h
    simpa using h.symm
  -- the source side is one splice further off than `vsa`'s: `vsb`'s block has
  -- to be carried back across the `sa` copy as well as the prologue
  have hnvsb : vsb.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hvsb.1
  have hneVsb : (slotPtr s Slot.sa).id ≠ vsb.id := fun he => by
    have hid := slots.id Slot.sa
    rw [he] at hid
    omega
  have hm₁live : m₁.mem.live? vsb.id = sAlloc.mem.live? vsb.id := by
    rw [hm₁]; exact live?_splice_ne hneVsb
  have hliveVsb : s.mem.live? vsb.id = some hvsb''.choose :=
    (frame.fb vsb.id hnvsb).symm.trans
      (hm₁live.symm.trans (live?_of_getElem? hvsb''.choose_spec.1))
  have hlanesB : ∀ (j : Nat) (hj : j < 4),
      b_high_blk.bytes.extractLsb' ((slotPtr s Slot.sb).offsetInBits + 64 * j) 64
        = (readWv hvsb)[j] := by
    intro j hj
    have hlenSlot := hsb.1.choose_spec.2
    simp only [LiveBlock.lengthInBits] at hlenSlot
    rw [hblkB]
    show BitVec.extractLsb' ((slotPtr s Slot.sb).offsetInBits + 64 * j) 64
        (spliceBits hsb.1.choose.bytes (slotPtr s Slot.sb).offsetInBits
          (BitVec.extractLsb' vsb.offsetInBits (8 * 32) hvsb''.choose.bytes)) = _
    rw [extractLsb'_spliceBits_of_subrange _ _ _ _ (by omega) (by omega) (by omega),
      Nat.add_sub_cancel_left,
      BitVec.extractLsb'_extractLsb'_add_of_le (show 64 * j + 64 ≤ 8 * 32 from by omega)]
    simp [readWv, readWv?, hliveVsb]
  have hoffPb : pb_high.offsetInBits = (slotPtr s Slot.sb).offsetInBits + 64 * 3 := by
    simp [pb_high, Pointer.withOffset, Pointer.offsetInBits, slots.off Slot.sb]
  have hlaneB : b_high_blk.bytes.extractLsb' pb_high.offsetInBits 64 = (readWv hvsb)[3] := by
    rw [hoffPb]; exact hlanesB 3 (by omega)

  rw [hlaneA] at hv57 hv54
  rw [hlaneB] at hv58 hv56
  denote_clear v 53 53
  denote_clear v 55 55
  subst hv57
  subst hv58
  refine name_of ({ m₂ with mem := m₂.mem.splice pa_high ((readWv hvsa)[3] &&& 0x7fffffffffffffff#64) }) fun m₃ hm₃ => ?_
  peel_store ((readWv hvsa)[3] &&& 0x7fffffffffffffff#64), pa_high,
    (⟨a_high_blk, ha_high_blk, hfitA⟩ : Fits m₂.mem pa_high 64), m₂ as m₃ := hm₃
  have hpb_high : Fits m₃.mem pb_high 64 :=
    hm₃ ▸ fits_splice hpb_high
  refine name_of ({ m₃ with mem := m₃.mem.splice pb_high ((readWv hvsb)[3] &&& 0x7fffffffffffffff#64) }) fun m₄ hm₄ => ?_
  peel_store ((readWv hvsb)[3] &&& 0x7fffffffffffffff#64), pb_high, hpb_high, m₃ as m₄ := hm₄

  -- %59: `wv_ld( _sa )`, the staging buffer with its sign bit now cleared. The
  -- quad comes back as an opaque `wa`; `hwa` is what it holds.
  have hwf₄ : m₄.WF := hm₄ ▸ (hm₃ ▸ (hm₂ ▸ (hm₁ ▸ frame.wf.splice).splice).splice).splice
  have hslot₃ : Fits m₃.mem (slotPtr s Slot.sa) (8 * 32) := hm₃ ▸ fits_splice hsaF
  have hslot₄ : Fits m₄.mem (slotPtr s Slot.sa) (8 * 32) := hm₄ ▸ fits_splice hslot₃
  have hslotWvA : IsWvPtr m₄.mem (slotPtr s Slot.sa) := ⟨hslot₄, hsa.2⟩
  refine wv_ld_step hwf₄ hslotWvA fun u₅ yaPacked hrun₅ hyaPacked hequ₅ => ?_
  peel_call hrun₅
  -- what the load read: `_sa`'s block with lane 3's top bit cleared, the `sb`
  -- store having missed the block entirely
  have hblk₄ : m₄.mem.live? (slotPtr s Slot.sa).id
      = some { a_high_blk with
          bytes := spliceBits a_high_blk.bytes pa_high.offsetInBits
              ((readWv hvsa)[3] &&& 0x7fffffffffffffff#64) } := by
    have h₃ : m₃.mem.live? (slotPtr s Slot.sa).id
        = some { a_high_blk with
            bytes := spliceBits a_high_blk.bytes pa_high.offsetInBits
                ((readWv hvsa)[3] &&& 0x7fffffffffffffff#64) } := by
      simp only [hm₃]
      exact splicedLive m₂.mem pa_high a_high_blk (live?_of_getElem? ha_high_blk) _
    simp only [hm₄]
    rw [live?_splice_ne (by
      simpa [pb_high, Pointer.withOffset] using slots.ne (show Slot.sb ≠ Slot.sa by decide))]
    exact h₃
  have hreadA : readWv hslotWvA = Vector.ofFn fun i : Fin 4 =>
      (spliceBits a_high_blk.bytes pa_high.offsetInBits
          ((readWv hvsa)[3] &&& 0x7fffffffffffffff#64)).extractLsb'
        ((slotPtr s Slot.sa).offsetInBits + 64 * i.val) 64 := by
    simp [readWv, readWv?, hblk₄]
  -- lanes 0-2 are below the store, lane 3 is what it wrote
  have hlo : ∀ (j : Nat) (hj : j < 3), (readWv hslotWvA)[j]'(by omega) = (readWv hvsa)[j] := by
    intro j hj
    simp only [hreadA, Vector.getElem_ofFn]
    rw [hoffPa, extractLsb'_spliceBits_of_disjoint _ _ _ _ (Or.inl (by omega))]
    exact hlanesA j (by omega)
  have hhi : (readWv hslotWvA)[3] = (readWv hvsa)[3] &&& 0x7fffffffffffffff#64 := by
    have hlen : pa_high.offsetInBits + 64 ≤ 8 * a_high_blk.length := by
      simpa [LiveBlock.lengthInBits] using hfitA
    simp only [hreadA, Vector.getElem_ofFn]
    rw [← hoffPa, extractLsb'_spliceBits _ _ _ hlen]
  have hmask : ∀ x : BitVec 64, (x &&& 0x7fffffffffffffff#64).toNat = x.toNat % 2 ^ 63 := by
    intro x
    have h : x &&& 0x7fffffffffffffff#64 = (x.setWidth 63).setWidth 64 := by bv_decide
    rw [h]
    have := x.isLt
    simp only [BitVec.toNat_setWidth]
    omega
  replace hyaPacked : wvNat yaPacked = wvY (readWv hvsa) := by
    have hnat : wvNat yaPacked = wvNat (readWv hvsa) % 2 ^ 255 := by
      rw [hyaPacked]
      simp only [wvNat, hlo 0 (by omega), hlo 1 (by omega), hlo 2 (by omega), hhi, hmask]
      have b0 := (readWv hvsa)[0].isLt
      have b1 := (readWv hvsa)[1].isLt
      have b2 := (readWv hvsa)[2].isLt
      have b3 := (readWv hvsa)[3].isLt
      omega
    rw [wvY, hnat]

  refine name_of (u₅.popFrame u₅.mem) fun u₆ hu₆ => ?_
  refine unpack_step yaPacked u₅ u₆ hu₆ fun yaVec hrun₆ hunpA hdecA h6A h7A hnrA hredA => ?_
  peel_call hrun₆
  replace hdecA : (R43x6.decode' yaVec : ZMod p) = wvY (readWv hvsa) := by
    simp [← hyaPacked, hdecA]
  clear hyaPacked

  -- %61: `wv_ld( _sb )`, the `a` load's argument at the state the unpack left
  have hwf₅ : u₅.WF := hwf₄.of_equiv hequ₅
  have hequ₆ : u₅ ≈ u₆ := hu₆ ▸ hwf₅.popFrame_equiv
  have hwf₆ : u₆.WF := hwf₅.of_equiv hequ₆
  have hslot₃B : Fits m₃.mem (slotPtr s Slot.sb) (8 * 32) := hm₃ ▸ fits_splice hsbF
  have hslot₄B : Fits m₄.mem (slotPtr s Slot.sb) (8 * 32) := hm₄ ▸ fits_splice hslot₃B
  have hliveB₆ : u₆.mem.live? (slotPtr s Slot.sb).id = m₄.mem.live? (slotPtr s Slot.sb).id :=
    (hequ₆.live _).symm.trans (hequ₅.live _).symm
  have hslotWvB : IsWvPtr u₆.mem (slotPtr s Slot.sb) :=
    ⟨fits_of_live?_eq hliveB₆ hslot₄B, hsb.2⟩
  refine wv_ld_step hwf₆ hslotWvB fun u₇ ybPacked hrun₇ hybPacked hequ₇ => ?_
  peel_call hrun₇
  -- what that load read: `_sb`'s block with lane 3's top bit cleared. The `sa`
  -- store missed the block, and neither call moved memory.
  have hblkB₆ : u₆.mem.live? (slotPtr s Slot.sb).id
      = some { b_high_blk with
          bytes := spliceBits b_high_blk.bytes pb_high.offsetInBits
              ((readWv hvsb)[3] &&& 0x7fffffffffffffff#64) } := by
    have h₃ : m₃.mem.live? (slotPtr s Slot.sb).id = some b_high_blk := by
      simp only [hm₃]
      rw [live?_splice_ne (by
        simpa [pa_high, Pointer.withOffset] using slots.ne (show Slot.sa ≠ Slot.sb by decide))]
      exact live?_of_getElem? hb_high_blk
    refine hliveB₆.trans ?_
    simp only [hm₄]
    exact splicedLive m₃.mem pb_high b_high_blk h₃ _
  have hreadB : readWv hslotWvB = Vector.ofFn fun i : Fin 4 =>
      (spliceBits b_high_blk.bytes pb_high.offsetInBits
          ((readWv hvsb)[3] &&& 0x7fffffffffffffff#64)).extractLsb'
        ((slotPtr s Slot.sb).offsetInBits + 64 * i.val) 64 := by
    simp [readWv, readWv?, hblkB₆]
  have hloB : ∀ (j : Nat) (hj : j < 3), (readWv hslotWvB)[j]'(by omega) = (readWv hvsb)[j] := by
    intro j hj
    simp only [hreadB, Vector.getElem_ofFn]
    rw [hoffPb, extractLsb'_spliceBits_of_disjoint _ _ _ _ (Or.inl (by omega))]
    exact hlanesB j (by omega)
  have hhiB : (readWv hslotWvB)[3] = (readWv hvsb)[3] &&& 0x7fffffffffffffff#64 := by
    have hlen : pb_high.offsetInBits + 64 ≤ 8 * b_high_blk.length := by
      simpa [LiveBlock.lengthInBits] using hfitB
    simp only [hreadB, Vector.getElem_ofFn]
    rw [← hoffPb, extractLsb'_spliceBits _ _ _ hlen]
  replace hybPacked : wvNat ybPacked = wvY (readWv hvsb) := by
    have hnat : wvNat ybPacked = wvNat (readWv hvsb) % 2 ^ 255 := by
      rw [hybPacked]
      simp only [wvNat, hloB 0 (by omega), hloB 1 (by omega), hloB 2 (by omega), hhiB, hmask]
      have b0 := (readWv hvsb)[0].isLt
      have b1 := (readWv hvsb)[1].isLt
      have b2 := (readWv hvsb)[2].isLt
      have b3 := (readWv hvsb)[3].isLt
      omega
    rw [wvY, hnat]

  -- %62: `fd_r43x6_unpack( ybVec )`
  refine name_of (u₇.popFrame u₇.mem) fun u₈ hu₈ => ?_
  refine unpack_step ybPacked u₇ u₈ hu₈ fun ybVec hrun₈ hunpB hdecB h6B h7B hnrB hredB => ?_
  peel_call hrun₈
  replace hdecB : (R43x6.decode' ybVec : ZMod p) = wvY (readWv hvsb) := by
    simp [← hybPacked, hdecB]
  clear hybPacked



  -- The fold's three constants, in the shape `denote_foldVec` states them.
  replace hv32 : v32 = toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207,
      8796093022207, 8796093022207, 1099511627775, 0, 0] := by denote_dense hv32
  replace hv33 : v33 = toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0] := by denote_dense hv33
  replace hv27 : v27 = toBitVecValue 64 #v[19, 1, 1, 1, 1, 1, 0, 0] := by denote_dense hv27

  -- %63-%67: `FD_R43X6_SQR_INL( ua, yaVec )` sqr 1
  have hyaU47 : R43x6.U47 (yaVec.take R43x6.limbCount) := u47_take_of_unpacked hunpA
  refine name_of (u₈.popFrame u₈.mem) fun u₉ hu₉ => ?_
  peel_call (sqr_step_of_take hyaU47 h6A h7A u₈ u₉ hu₉)
  fold_unsigned (sqrVec yaVec), (limbNat_sqr_lt hyaU47)
  refine name_of (foldVec (sqrVec yaVec)) fun ysqa hysqa => ?_
  have hsqrA : SqrInl yaVec ysqa := by
    rw [hysqa]
    exact sqr_inl hyaU47
  rw [← hysqa] at hv67


  -- %68-%72: the `b` twin
  have hybU47 : R43x6.U47 (ybVec.take R43x6.limbCount) := u47_take_of_unpacked hunpB
  refine name_of (u₉.popFrame u₉.mem) fun u₁₀ hu₁₀ => ?_
  peel_call (sqr_step_of_take hybU47 h6B h7B u₉ u₁₀ hu₁₀)
  fold_unsigned (sqrVec ybVec), (limbNat_sqr_lt hybU47)
  refine name_of (foldVec (sqrVec ybVec)) fun ysqb hysqb => ?_
  have hsqrB : SqrInl ybVec ysqb := by
    rw [hysqb]
    exact sqr_inl hybU47
  rw [← hysqb] at hv72

  -- %73-%81: `fd_r43x6_sub( ysqa, one )` -- the constant carries both the
  -- `- 1` and the signed fold's bias
  replace hv26 : v26 = toBitVecValue 64 subOneConst := by
    simp only [subOneConst]; denote_dense hv26
  replace hv25 : v25 = toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8] := by denote_dense hv25
  replace hv24 : v24 = toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0] := by denote_dense hv24
  replace hv23 : v23 = toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18] := by denote_dense hv23
  replace hv22 : v22 = toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0] := by
    denote_dense hv22
  replace hv21 : v21 = toBitVecValue 64
      #v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0] := by denote_dense hv21
  denote_step_reduce v 81 only [hv67, hv26, hv32, hv33, hv25, hv24, hv23, hv22, hv21]
  refine name_of (subOneVec ysqa) fun ua huadef => ?_
  replace hv81 : v81 = ua.map PoisonOr.value := by
    rw [huadef]; exact denote_subOneVec hv73 hv74 hv75 hv76 hv77 hv78 hv79 hv80 hv81
  -- `%80`, the fold's pre-bias output: what the `sub_fast` at `%185` reads
  have hv80acp := denote_subOneVec' hv73 hv74 hv75 hv76 hv77 hv78 hv79 hv80
  denote_clear v 73 80
  -- what `ua` holds, and the bound the next kernel takes
  have hysqaB : ∀ k, 0 ≤ R43x6.extractLimbs ysqa k ∧ R43x6.extractLimbs ysqa k < 2 ^ 44 := by
    intro k
    have h1 := hsqrA.u44.1 k
    have h2 := hsqrA.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega
  have hyaB : ∀ k, 0 ≤ R43x6.extractLimbs yaVec k ∧ R43x6.extractLimbs yaVec k < 2 ^ 44 := by
    intro k
    have h5 := hunpA.2
    by_cases hk : (k : ℕ) < 5
    · have := hunpA.1 k hk
      omega
    · have hk5 : k = (5 : Fin R43x6.limbCount) := by
        have := k.isLt
        apply Fin.ext
        simp only [R43x6.limbCount] at *
        omega
      subst hk5
      omega
  have huaValue : ((R43x6.decode' ua : ℤ) : ZMod p) = wvY (readWv hvsa) ^ 2 - 1 := by
    rw [huadef, decode'_subOneVec hysqaB, decode'_cast_eq_vecValue ysqa hysqaB, hsqrA.value,
      ← decode'_cast_eq_vecValue yaVec hyaB, hdecA]
  have huaB : ∀ k, 0 ≤ R43x6.extractLimbs ua k ∧ R43x6.extractLimbs ua k < 2 ^ 44 := by
    rw [huadef]; exact extractLimbs_subOneVec hysqaB
  have hua6 : ua[6] = 0 := by rw [huadef]; exact subOneVec_six ysqa
  have hua7 : ua[7] = 0 := by rw [huadef]; exact subOneVec_seven ysqa

  -- %82-%90: the `b` twin. Its two carry adds come in the other operand
  -- order, which is what `denote_vec_add_comm` puts back.
  denote_step_reduce v 90 only [hv72, hv26, hv32, hv33, hv25, hv24, hv23, hv22, hv21]
  replace hv88 := hv88.trans (denote_vec_add_comm v83 v85)
  refine name_of (subOneVec ysqb) fun ub hubdef => ?_
  replace hv90 : v90 = ub.map PoisonOr.value := by
    rw [hubdef]; exact denote_subOneVec hv82 hv83 hv84 hv85 hv86 hv87 hv88 hv89 hv90
  have hv89acp := denote_subOneVec' hv82 hv83 hv84 hv85 hv86 hv87 hv88 hv89
  denote_clear v 82 89
  have hysqbB : ∀ k, 0 ≤ R43x6.extractLimbs ysqb k ∧ R43x6.extractLimbs ysqb k < 2 ^ 44 := by
    intro k
    have h1 := hsqrB.u44.1 k
    have h2 := hsqrB.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega
  have hybB : ∀ k, 0 ≤ R43x6.extractLimbs ybVec k ∧ R43x6.extractLimbs ybVec k < 2 ^ 44 := by
    intro k
    have h5 := hunpB.2
    by_cases hk : (k : ℕ) < 5
    · have := hunpB.1 k hk
      omega
    · have hk5 : k = (5 : Fin R43x6.limbCount) := by
        have := k.isLt
        apply Fin.ext
        simp only [R43x6.limbCount] at *
        omega
      subst hk5
      omega
  have hubValue : ((R43x6.decode' ub : ℤ) : ZMod p) = wvY (readWv hvsb) ^ 2 - 1 := by
    rw [hubdef, decode'_subOneVec hysqbB, decode'_cast_eq_vecValue ysqb hysqbB, hsqrB.value,
      ← decode'_cast_eq_vecValue ybVec hybB, hdecB]
  have hubB : ∀ k, 0 ≤ R43x6.extractLimbs ub k ∧ R43x6.extractLimbs ub k < 2 ^ 44 := by
    rw [hubdef]; exact extractLimbs_subOneVec hysqbB
  have hub6 : ub[6] = 0 := by rw [hubdef]; exact subOneVec_six ysqb
  have hub7 : ub[7] = 0 := by rw [hubdef]; exact subOneVec_seven ysqb


  -- the two `y`s the encodings name, as the spec spells them
  refine name_of (wvY (readWv hvsa)) fun ya hya => ?_
  refine name_of (wvY (readWv hvsb)) fun yb hyb => ?_
  rw [← hya] at huaValue
  rw [← hyb] at hubValue

  -- %91-%96: `FD_R43X6_MUL_INL( va, d, ysqa )` and the `fd_r43x6_add_fast( ·, one )`
  -- after it, and the same for `b` at %97-%102
  replace hv20 : v20 = dVec.map PoisonOr.value := by
    have h : v20 = toBitVecValue 64 #v[6365466163363, 253762649449, 7518893317, 260847760460,
        7696165686388, 704489577558, 0, 0] := by denote_dense hv20
    rw [h]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [toBitVecValue, dVec]
  replace hv19 : v19 = toBitVecValue 64 addOneConst := by
    simp only [addOneConst]; denote_dense hv19
  refine name_of (u₁₀.popFrame u₁₀.mem) fun u₁₁ hu₁₁ => ?_
  have hmulRunA := mul_step_of_take dVec_u47 dVec_six dVec_seven hsqrA.u47 hsqrA.z6 hsqrA.z7
    u₁₀ u₁₁ hu₁₁
  rw [← hv20, ← hv67] at hmulRunA
  peel_call hmulRunA
  fold_unsigned (mulVec dVec ysqa), (limbNat_mul_lt dVec_u47 hsqrA.u47)
  have hmulA : MulInl dVec ysqa (foldVec (mulVec dVec ysqa)) := mul_inl dVec_u47 hsqrA.u47
  have hmulAB : ∀ k, 0 ≤ R43x6.extractLimbs (foldVec (mulVec dVec ysqa)) k
      ∧ R43x6.extractLimbs (foldVec (mulVec dVec ysqa)) k < 2 ^ 44 := by
    intro k
    have h1 := hmulA.u44.1 k
    have h2 := hmulA.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega
  denote_step_reduce v 96 only [hv95, hv19]
  refine name_of (addOneVec (foldVec (mulVec dVec ysqa))) fun va hvadef => ?_
  replace hv96 : v96 = va.map PoisonOr.value := by
    rw [hvadef]; exact denote_addOneVec hv96
  have hvaValue : ((R43x6.decode' va : ℤ) : ZMod p)
      = Ed25519.d * ya ^ 2 + 1 := by
    rw [hvadef, decode'_addOneVec hmulAB]
    push_cast
    rw [decode'_cast_eq_vecValue _ hmulAB, hmulA.value, vecValue_dVec, hsqrA.value,
      ← decode'_cast_eq_vecValue yaVec hyaB, hdecA, hya]
  have hvaB : ∀ k, 0 ≤ R43x6.extractLimbs va k ∧ R43x6.extractLimbs va k < 2 ^ 45 := by
    rw [hvadef]; exact extractLimbs_addOneVec_bounds hmulAB

  refine name_of (u₁₁.popFrame u₁₁.mem) fun u₁₂ hu₁₂ => ?_
  have hmulRunB := mul_step_of_take dVec_u47 dVec_six dVec_seven hsqrB.u47 hsqrB.z6 hsqrB.z7
    u₁₁ u₁₂ hu₁₂
  rw [← hv20, ← hv72] at hmulRunB
  peel_call hmulRunB
  fold_unsigned (mulVec dVec ysqb), (limbNat_mul_lt dVec_u47 hsqrB.u47)
  have hmulB : MulInl dVec ysqb (foldVec (mulVec dVec ysqb)) := mul_inl dVec_u47 hsqrB.u47
  have hmulBB : ∀ k, 0 ≤ R43x6.extractLimbs (foldVec (mulVec dVec ysqb)) k
      ∧ R43x6.extractLimbs (foldVec (mulVec dVec ysqb)) k < 2 ^ 44 := by
    intro k
    have h1 := hmulB.u44.1 k
    have h2 := hmulB.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega
  denote_step_reduce v 102 only [hv101, hv19]
  refine name_of (addOneVec (foldVec (mulVec dVec ysqb))) fun vb hvbdef => ?_
  replace hv102 : v102 = vb.map PoisonOr.value := by
    rw [hvbdef]; exact denote_addOneVec hv102
  have hvbValue : ((R43x6.decode' vb : ℤ) : ZMod p)
      = Ed25519.d * yb ^ 2 + 1 := by
    rw [hvbdef, decode'_addOneVec hmulBB]
    push_cast
    rw [decode'_cast_eq_vecValue _ hmulBB, hmulB.value, vecValue_dVec, hsqrB.value,
      ← decode'_cast_eq_vecValue ybVec hybB, hdecB, hyb]
  have hvbB : ∀ k, 0 ≤ R43x6.extractLimbs vb k ∧ R43x6.extractLimbs vb k < 2 ^ 45 := by
    rw [hvbdef]; exact extractLimbs_addOneVec_bounds hmulBB


  -- the walk carries `ua`, `va`, `ub`, `vb` and what they hold from here; the
  -- limb-level reasoning that got them is spent
  clear hmulRunA hmulRunB hmulA hmulB hmulAB hmulBB
  clear hlanesA hlanesB hblkA hblkB hoffPa hoffPb hlaneA hlaneB
  clear hliveVsa hliveVsb hnvsb hneVsb hm₁live hmask
  clear hreadA hreadB hlo hhi hloB hhiB hblk₄ hblkB₆
  clear hslot₃ hslot₄ hslot₃B hslot₄B hliveB₆ hfitA hfitB
  clear hyaB hybB hysqaB hysqbB

  denote_clear v 91 95
  denote_clear v 97 101

  -- %103-%107: `FD_R43X6_SQR_INL( ·, va )`, the head of the `u`/`v` chain the
  -- square root runs on
  have hvaU47 : R43x6.U47 (va.take R43x6.limbCount) := by
    constructor <;> intro i <;> rw [R43x6.toInts_take] <;> have := hvaB i <;> omega
  have hva6 : va[6] = 0 := by rw [hvadef]; exact addOneVec_six (foldVec_getElem_six _)
  have hva7 : va[7] = 0 := by rw [hvadef]; exact addOneVec_seven (foldVec_getElem_seven _)
  refine name_of (u₁₂.popFrame u₁₂.mem) fun u₁₃ hu₁₃ => ?_
  have hsqrRunA := sqr_step_of_take hvaU47 hva6 hva7 u₁₂ u₁₃ hu₁₃
  rw [← hv96] at hsqrRunA
  peel_call hsqrRunA
  fold_unsigned (sqrVec va), (limbNat_sqr_lt hvaU47)
  refine name_of (foldVec (sqrVec va)) fun v2a hv2a => ?_
  have hsqr2a : SqrInl va v2a := by rw [hv2a]; exact sqr_inl hvaU47
  rw [← hv2a] at hv107

  -- the rest of the `u`/`v` chain, in the C's names: `v2`, `v4`, `v3 = v·v2`,
  -- `uv3 = u·v3`, `uv7 = uv3·v4`, which is what `fd_r43x6_pow22523_2` takes
  have hvbU47 : R43x6.U47 (vb.take R43x6.limbCount) := by
    constructor <;> intro i <;> rw [R43x6.toInts_take] <;> have := hvbB i <;> omega
  have hvb6 : vb[6] = 0 := by rw [hvbdef]; exact addOneVec_six (foldVec_getElem_six _)
  have hvb7 : vb[7] = 0 := by rw [hvbdef]; exact addOneVec_seven (foldVec_getElem_seven _)
  have huaU47 : R43x6.U47 (ua.take R43x6.limbCount) := by
    constructor <;> intro i <;> rw [R43x6.toInts_take] <;> have := huaB i <;> omega
  have hubU47 : R43x6.U47 (ub.take R43x6.limbCount) := by
    constructor <;> intro i <;> rw [R43x6.toInts_take] <;> have := hubB i <;> omega

  -- %108-%112: `FD_R43X6_SQR_INL( v2b, vb )`
  refine name_of (u₁₃.popFrame u₁₃.mem) fun u₁₄ hu₁₄ => ?_
  have hrunv2b := sqr_step_of_take hvbU47 hvb6 hvb7 u₁₃ u₁₄ hu₁₄
  rw [← hv102] at hrunv2b
  peel_call hrunv2b
  fold_unsigned (sqrVec vb), (limbNat_sqr_lt hvbU47)
  refine name_of (foldVec (sqrVec vb)) fun v2b hv2b => ?_
  have hsqrv2b : SqrInl vb v2b := by rw [hv2b]; exact sqr_inl hvbU47
  rw [← hv2b] at hv112

  -- %113-%117: `FD_R43X6_SQR_INL( v4a, v2a )`
  refine name_of (u₁₄.popFrame u₁₄.mem) fun u₁₅ hu₁₅ => ?_
  have hrunv4a := sqr_step_of_take hsqr2a.u47 hsqr2a.z6 hsqr2a.z7 u₁₄ u₁₅ hu₁₅
  rw [← hv107] at hrunv4a
  peel_call hrunv4a
  fold_unsigned (sqrVec v2a), (limbNat_sqr_lt hsqr2a.u47)
  refine name_of (foldVec (sqrVec v2a)) fun v4a hv4a => ?_
  have hsqrv4a : SqrInl v2a v4a := by rw [hv4a]; exact sqr_inl hsqr2a.u47
  rw [← hv4a] at hv117

  -- %118-%122: `FD_R43X6_SQR_INL( v4b, v2b )`
  refine name_of (u₁₅.popFrame u₁₅.mem) fun u₁₆ hu₁₆ => ?_
  have hrunv4b := sqr_step_of_take hsqrv2b.u47 hsqrv2b.z6 hsqrv2b.z7 u₁₅ u₁₆ hu₁₆
  rw [← hv112] at hrunv4b
  peel_call hrunv4b
  fold_unsigned (sqrVec v2b), (limbNat_sqr_lt hsqrv2b.u47)
  refine name_of (foldVec (sqrVec v2b)) fun v4b hv4b => ?_
  have hsqrv4b : SqrInl v2b v4b := by rw [hv4b]; exact sqr_inl hsqrv2b.u47
  rw [← hv4b] at hv122

  -- %123-%127: `FD_R43X6_MUL_INL( v3a, va, v2a )`
  refine name_of (u₁₆.popFrame u₁₆.mem) fun u₁₇ hu₁₇ => ?_
  have hrunv3a := mul_step_of_take hvaU47 hva6 hva7 hsqr2a.u47 hsqr2a.z6 hsqr2a.z7
    u₁₆ u₁₇ hu₁₇
  rw [← hv96, ← hv107] at hrunv3a
  peel_call hrunv3a
  fold_unsigned (mulVec va v2a), (limbNat_mul_lt hvaU47 hsqr2a.u47)
  refine name_of (foldVec (mulVec va v2a)) fun v3a hv3a => ?_
  have hmulv3a : MulInl va v2a v3a := by rw [hv3a]; exact mul_inl hvaU47 hsqr2a.u47
  rw [← hv3a] at hv127

  -- %128-%132: `FD_R43X6_MUL_INL( v3b, vb, v2b )`
  refine name_of (u₁₇.popFrame u₁₇.mem) fun u₁₈ hu₁₈ => ?_
  have hrunv3b := mul_step_of_take hvbU47 hvb6 hvb7 hsqrv2b.u47 hsqrv2b.z6 hsqrv2b.z7
    u₁₇ u₁₈ hu₁₈
  rw [← hv102, ← hv112] at hrunv3b
  peel_call hrunv3b
  fold_unsigned (mulVec vb v2b), (limbNat_mul_lt hvbU47 hsqrv2b.u47)
  refine name_of (foldVec (mulVec vb v2b)) fun v3b hv3b => ?_
  have hmulv3b : MulInl vb v2b v3b := by rw [hv3b]; exact mul_inl hvbU47 hsqrv2b.u47
  rw [← hv3b] at hv132

  -- %133-%137: `FD_R43X6_MUL_INL( uv3a, ua, v3a )`
  refine name_of (u₁₈.popFrame u₁₈.mem) fun u₁₉ hu₁₉ => ?_
  have hrunuv3a := mul_step_of_take huaU47 hua6 hua7 hmulv3a.u47 hmulv3a.z6 hmulv3a.z7
    u₁₈ u₁₉ hu₁₉
  rw [← hv81, ← hv127] at hrunuv3a
  peel_call hrunuv3a
  fold_unsigned (mulVec ua v3a), (limbNat_mul_lt huaU47 hmulv3a.u47)
  refine name_of (foldVec (mulVec ua v3a)) fun uv3a huv3a => ?_
  have hmuluv3a : MulInl ua v3a uv3a := by rw [huv3a]; exact mul_inl huaU47 hmulv3a.u47
  rw [← huv3a] at hv137

  -- %138-%142: `FD_R43X6_MUL_INL( uv3b, ub, v3b )`
  refine name_of (u₁₉.popFrame u₁₉.mem) fun u₂₀ hu₂₀ => ?_
  have hrunuv3b := mul_step_of_take hubU47 hub6 hub7 hmulv3b.u47 hmulv3b.z6 hmulv3b.z7
    u₁₉ u₂₀ hu₂₀
  rw [← hv90, ← hv132] at hrunuv3b
  peel_call hrunuv3b
  fold_unsigned (mulVec ub v3b), (limbNat_mul_lt hubU47 hmulv3b.u47)
  refine name_of (foldVec (mulVec ub v3b)) fun uv3b huv3b => ?_
  have hmuluv3b : MulInl ub v3b uv3b := by rw [huv3b]; exact mul_inl hubU47 hmulv3b.u47
  rw [← huv3b] at hv142

  -- %143-%147: `FD_R43X6_MUL_INL( uv7a, uv3a, v4a )`
  refine name_of (u₂₀.popFrame u₂₀.mem) fun u₂₁ hu₂₁ => ?_
  have hrunuv7a := mul_step_of_take hmuluv3a.u47 hmuluv3a.z6 hmuluv3a.z7 hsqrv4a.u47 hsqrv4a.z6 hsqrv4a.z7
    u₂₀ u₂₁ hu₂₁
  rw [← hv137, ← hv117] at hrunuv7a
  peel_call hrunuv7a
  fold_unsigned (mulVec uv3a v4a), (limbNat_mul_lt hmuluv3a.u47 hsqrv4a.u47)
  refine name_of (foldVec (mulVec uv3a v4a)) fun uv7a huv7a => ?_
  have hmuluv7a : MulInl uv3a v4a uv7a := by rw [huv7a]; exact mul_inl hmuluv3a.u47 hsqrv4a.u47
  rw [← huv7a] at hv147

  -- %148-%152: `FD_R43X6_MUL_INL( uv7b, uv3b, v4b )`
  refine name_of (u₂₁.popFrame u₂₁.mem) fun u₂₂ hu₂₂ => ?_
  have hrunuv7b := mul_step_of_take hmuluv3b.u47 hmuluv3b.z6 hmuluv3b.z7 hsqrv4b.u47 hsqrv4b.z6 hsqrv4b.z7
    u₂₁ u₂₂ hu₂₂
  rw [← hv142, ← hv122] at hrunuv7b
  peel_call hrunuv7b
  fold_unsigned (mulVec uv3b v4b), (limbNat_mul_lt hmuluv3b.u47 hsqrv4b.u47)
  refine name_of (foldVec (mulVec uv3b v4b)) fun uv7b huv7b => ?_
  have hmuluv7b : MulInl uv3b v4b uv7b := by rw [huv7b]; exact mul_inl hmuluv3b.u47 hsqrv4b.u47
  rw [← huv7b] at hv152

  -- the states the calls left, as one chain back to `m₄`
  have hwf₇ : u₇.WF := hwf₆.of_equiv hequ₇
  have heq₇ : m₄ ≈ u₇ := (hequ₅.trans hequ₆).trans hequ₇
  have hequ₈ : u₇ ≈ u₈ := hu₈ ▸ hwf₇.popFrame_equiv
  have hwf₈ : u₈.WF := hwf₇.of_equiv hequ₈
  have heq₈ : m₄ ≈ u₈ := heq₇.trans hequ₈
  have hequ₉ : u₈ ≈ u₉ := hu₉ ▸ hwf₈.popFrame_equiv
  have hwf₉ : u₉.WF := hwf₈.of_equiv hequ₉
  have heq₉ : m₄ ≈ u₉ := heq₈.trans hequ₉
  have hequ₁₀ : u₉ ≈ u₁₀ := hu₁₀ ▸ hwf₉.popFrame_equiv
  have hwf₁₀ : u₁₀.WF := hwf₉.of_equiv hequ₁₀
  have heq₁₀ : m₄ ≈ u₁₀ := heq₉.trans hequ₁₀
  have hequ₁₁ : u₁₀ ≈ u₁₁ := hu₁₁ ▸ hwf₁₀.popFrame_equiv
  have hwf₁₁ : u₁₁.WF := hwf₁₀.of_equiv hequ₁₁
  have heq₁₁ : m₄ ≈ u₁₁ := heq₁₀.trans hequ₁₁
  have hequ₁₂ : u₁₁ ≈ u₁₂ := hu₁₂ ▸ hwf₁₁.popFrame_equiv
  have hwf₁₂ : u₁₂.WF := hwf₁₁.of_equiv hequ₁₂
  have heq₁₂ : m₄ ≈ u₁₂ := heq₁₁.trans hequ₁₂
  have hequ₁₃ : u₁₂ ≈ u₁₃ := hu₁₃ ▸ hwf₁₂.popFrame_equiv
  have hwf₁₃ : u₁₃.WF := hwf₁₂.of_equiv hequ₁₃
  have heq₁₃ : m₄ ≈ u₁₃ := heq₁₂.trans hequ₁₃
  have hequ₁₄ : u₁₃ ≈ u₁₄ := hu₁₄ ▸ hwf₁₃.popFrame_equiv
  have hwf₁₄ : u₁₄.WF := hwf₁₃.of_equiv hequ₁₄
  have heq₁₄ : m₄ ≈ u₁₄ := heq₁₃.trans hequ₁₄
  have hequ₁₅ : u₁₄ ≈ u₁₅ := hu₁₅ ▸ hwf₁₄.popFrame_equiv
  have hwf₁₅ : u₁₅.WF := hwf₁₄.of_equiv hequ₁₅
  have heq₁₅ : m₄ ≈ u₁₅ := heq₁₄.trans hequ₁₅
  have hequ₁₆ : u₁₅ ≈ u₁₆ := hu₁₆ ▸ hwf₁₅.popFrame_equiv
  have hwf₁₆ : u₁₆.WF := hwf₁₅.of_equiv hequ₁₆
  have heq₁₆ : m₄ ≈ u₁₆ := heq₁₅.trans hequ₁₆
  have hequ₁₇ : u₁₆ ≈ u₁₇ := hu₁₇ ▸ hwf₁₆.popFrame_equiv
  have hwf₁₇ : u₁₇.WF := hwf₁₆.of_equiv hequ₁₇
  have heq₁₇ : m₄ ≈ u₁₇ := heq₁₆.trans hequ₁₇
  have hequ₁₈ : u₁₇ ≈ u₁₈ := hu₁₈ ▸ hwf₁₇.popFrame_equiv
  have hwf₁₈ : u₁₈.WF := hwf₁₇.of_equiv hequ₁₈
  have heq₁₈ : m₄ ≈ u₁₈ := heq₁₇.trans hequ₁₈
  have hequ₁₉ : u₁₈ ≈ u₁₉ := hu₁₉ ▸ hwf₁₈.popFrame_equiv
  have hwf₁₉ : u₁₉.WF := hwf₁₈.of_equiv hequ₁₉
  have heq₁₉ : m₄ ≈ u₁₉ := heq₁₈.trans hequ₁₉
  have hequ₂₀ : u₁₉ ≈ u₂₀ := hu₂₀ ▸ hwf₁₉.popFrame_equiv
  have hwf₂₀ : u₂₀.WF := hwf₁₉.of_equiv hequ₂₀
  have heq₂₀ : m₄ ≈ u₂₀ := heq₁₉.trans hequ₂₀
  have hequ₂₁ : u₂₀ ≈ u₂₁ := hu₂₁ ▸ hwf₂₀.popFrame_equiv
  have hwf₂₁ : u₂₁.WF := hwf₂₀.of_equiv hequ₂₁
  have heq₂₁ : m₄ ≈ u₂₁ := heq₂₀.trans hequ₂₁
  have hequ₂₂ : u₂₁ ≈ u₂₂ := hu₂₂ ▸ hwf₂₁.popFrame_equiv
  have hwf₂₂ : u₂₂.WF := hwf₂₁.of_equiv hequ₂₂
  have heq₂₂ : m₄ ≈ u₂₂ := heq₂₁.trans hequ₂₂

  -- the chain is spent once `heq₂₂`/`hwf₂₂` hold: every `have` and `refine`
  -- from here on is elaborated against this context, so the intermediates are
  -- hundreds of milliseconds each
  clear hequ₆ hequ₇ hequ₈ hequ₉ hequ₁₀ hequ₁₁ hequ₁₂ hequ₁₃ hequ₁₄ hequ₁₅ hequ₁₆ hequ₁₇ hequ₁₈ hequ₁₉ hequ₂₀ hequ₂₁
  clear hwf₅ hwf₆ hwf₇ hwf₈ hwf₉ hwf₁₀ hwf₁₁ hwf₁₂ hwf₁₃ hwf₁₄ hwf₁₅ hwf₁₆ hwf₁₇ hwf₁₈ hwf₁₉ hwf₂₀ hwf₂₁
  clear heq₇ heq₈ heq₉ heq₁₀ heq₁₁ heq₁₂ heq₁₃ heq₁₄ heq₁₅ heq₁₆ heq₁₇ heq₁₈ heq₁₉ heq₂₀ heq₂₁
  clear hu₆ hu₈ hu₉ hu₁₀ hu₁₁ hu₁₂ hu₁₃ hu₁₄ hu₁₅ hu₁₆ hu₁₇ hu₁₈ hu₁₉ hu₂₀ hu₂₁ hequ₂₂ hequ₅

  -- %153-%154: `FD_R43X6_POW22523_2_INL( t0a, uv7a, t0b, uv7b )`, whose two
  -- `wwl_t` out-parameters are the `t0a`/`t0b` slots, and the loads that read
  -- them back
  iterate 2 peel_lifetime
  have hslotT0a : IsVecPtr u₂₂.mem (slotPtr s Slot.t0a) :=
    ⟨fits_of_live?_eq (heq₂₂.live _).symm
      (hm₄ ▸ fits_splice (hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice
        (frame.fits 2 (by decide)) : Fits m₁.mem (slotPtr s Slot.t0a) (cw 2))
        : Fits m₂.mem (slotPtr s Slot.t0a) (cw 2))
        : Fits m₃.mem (slotPtr s Slot.t0a) (cw 2))
      : Fits m₄.mem (slotPtr s Slot.t0a) (cw 2)), by simp [slots.off Slot.t0a]⟩
  have hslotT0b : IsVecPtr u₂₂.mem (slotPtr s Slot.t0b) :=
    ⟨fits_of_live?_eq (heq₂₂.live _).symm
      (hm₄ ▸ fits_splice (hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice
        (frame.fits 3 (by decide)) : Fits m₁.mem (slotPtr s Slot.t0b) (cw 3))
        : Fits m₂.mem (slotPtr s Slot.t0b) (cw 3))
        : Fits m₃.mem (slotPtr s Slot.t0b) (cw 3))
      : Fits m₄.mem (slotPtr s Slot.t0b) (cw 3)), by simp [slots.off Slot.t0b]⟩
  refine pow22523_2_step' (slotPtr s Slot.t0a) (slotPtr s Slot.t0b) uv7a uv7b hwf₂₂
    hslotT0a hslotT0b (slots.ne (show Slot.t0a ≠ Slot.t0b by decide))
    hmuluv7a.u47 hmuluv7a.z6 hmuluv7a.z7 hmuluv7b.u47 hmuluv7b.z6 hmuluv7b.z7
    fun u₂₃ t0a t0b hrunPow hvalT0a hvalT0b wroteT0 => ?_
  rw [← hv147, ← hv152] at hrunPow
  peel_call hrunPow
  peel_load_vec t0a, (slotPtr s Slot.t0a), wroteT0.ptrA, wroteT0.valA, u₂₃
  peel_load_vec t0b, (slotPtr s Slot.t0b), wroteT0.ptrB, wroteT0.valB, u₂₃
  iterate 2 peel_lifetime

  -- %155-%159: `FD_R43X6_MUL_INL( xa, uv3a, t0a )`
  refine name_of (u₂₃.popFrame u₂₃.mem) fun u₂₄ hu₂₄ => ?_
  have hrunxa := mul_step_of_take hmuluv3a.u47 hmuluv3a.z6 hmuluv3a.z7 (u47_of_u44 wroteT0.u44A) wroteT0.z6A wroteT0.z7A
    u₂₃ u₂₄ hu₂₄
  rw [← hv137] at hrunxa
  peel_call hrunxa
  fold_unsigned (mulVec uv3a t0a), (limbNat_mul_lt hmuluv3a.u47 (u47_of_u44 wroteT0.u44A))
  refine name_of (foldVec (mulVec uv3a t0a)) fun xa hxa => ?_
  have hmulxa : MulInl uv3a t0a xa := by rw [hxa]; exact mul_inl hmuluv3a.u47 (u47_of_u44 wroteT0.u44A)
  rw [← hxa] at hv159

  -- %160-%164: `FD_R43X6_MUL_INL( xb, uv3b, t0b )`
  refine name_of (u₂₄.popFrame u₂₄.mem) fun u₂₅ hu₂₅ => ?_
  have hrunxb := mul_step_of_take hmuluv3b.u47 hmuluv3b.z6 hmuluv3b.z7 (u47_of_u44 wroteT0.u44B) wroteT0.z6B wroteT0.z7B
    u₂₄ u₂₅ hu₂₅
  rw [← hv142] at hrunxb
  peel_call hrunxb
  fold_unsigned (mulVec uv3b t0b), (limbNat_mul_lt hmuluv3b.u47 (u47_of_u44 wroteT0.u44B))
  refine name_of (foldVec (mulVec uv3b t0b)) fun xb hxb => ?_
  have hmulxb : MulInl uv3b t0b xb := by rw [hxb]; exact mul_inl hmuluv3b.u47 (u47_of_u44 wroteT0.u44B)
  rw [← hxb] at hv164

  -- %165-%169: `FD_R43X6_SQR_INL( x2a, xa )`
  refine name_of (u₂₅.popFrame u₂₅.mem) fun u₂₆ hu₂₆ => ?_
  have hrunx2a := sqr_step_of_take hmulxa.u47 hmulxa.z6 hmulxa.z7 u₂₅ u₂₆ hu₂₆
  rw [← hv159] at hrunx2a
  peel_call hrunx2a
  fold_unsigned (sqrVec xa), (limbNat_sqr_lt hmulxa.u47)
  refine name_of (foldVec (sqrVec xa)) fun x2a hx2a => ?_
  have hsqrx2a : SqrInl xa x2a := by rw [hx2a]; exact sqr_inl hmulxa.u47
  rw [← hx2a] at hv169

  -- %170-%174: `FD_R43X6_SQR_INL( x2b, xb )`
  refine name_of (u₂₆.popFrame u₂₆.mem) fun u₂₇ hu₂₇ => ?_
  have hrunx2b := sqr_step_of_take hmulxb.u47 hmulxb.z6 hmulxb.z7 u₂₆ u₂₇ hu₂₇
  rw [← hv164] at hrunx2b
  peel_call hrunx2b
  fold_unsigned (sqrVec xb), (limbNat_sqr_lt hmulxb.u47)
  refine name_of (foldVec (sqrVec xb)) fun x2b hx2b => ?_
  have hsqrx2b : SqrInl xb x2b := by rw [hx2b]; exact sqr_inl hmulxb.u47
  rw [← hx2b] at hv174

  -- %175-%179: `FD_R43X6_MUL_INL( vx2a, va, x2a )`
  refine name_of (u₂₇.popFrame u₂₇.mem) fun u₂₈ hu₂₈ => ?_
  have hrunvx2a := mul_step_of_take hvaU47 hva6 hva7 hsqrx2a.u47 hsqrx2a.z6 hsqrx2a.z7
    u₂₇ u₂₈ hu₂₈
  rw [← hv96, ← hv169] at hrunvx2a
  peel_call hrunvx2a
  fold_unsigned (mulVec va x2a), (limbNat_mul_lt hvaU47 hsqrx2a.u47)
  refine name_of (foldVec (mulVec va x2a)) fun vx2a hvx2a => ?_
  have hmulvx2a : MulInl va x2a vx2a := by rw [hvx2a]; exact mul_inl hvaU47 hsqrx2a.u47
  rw [← hvx2a] at hv179

  -- %180-%184: `FD_R43X6_MUL_INL( vx2b, vb, x2b )`
  refine name_of (u₂₈.popFrame u₂₈.mem) fun u₂₉ hu₂₉ => ?_
  have hrunvx2b := mul_step_of_take hvbU47 hvb6 hvb7 hsqrx2b.u47 hsqrx2b.z6 hsqrx2b.z7
    u₂₈ u₂₉ hu₂₉
  rw [← hv102, ← hv174] at hrunvx2b
  peel_call hrunvx2b
  fold_unsigned (mulVec vb x2b), (limbNat_mul_lt hvbU47 hsqrx2b.u47)
  refine name_of (foldVec (mulVec vb x2b)) fun vx2b hvx2b => ?_
  have hmulvx2b : MulInl vb x2b vx2b := by rw [hvx2b]; exact mul_inl hvbU47 hsqrx2b.u47
  rw [← hvx2b] at hv184


  -- %185-%192: `t1 = fd_r43x6_sub_fast( vx2, u )` and
  -- `t2 = fd_r43x6_add_fast( vx2, u )`, then the three `fd_r43x6_is_nonzero`
  -- calls `bb0` holds. The `sub` reads the fold's pre-bias vector, so the
  -- constant it adds back is `p` less the bias.
  replace hv18 : v18 = toBitVecValue 64 subFastConst := by
    simp only [subFastConst]; denote_dense hv18
  denote_step_all v 189
  denote_eval v 185 189
  simp only [hv179, hv80acp] at hv185
  replace hv185 := hv185.trans (denote_vec_sub vx2a (subOneAcp ysqa))
  simp only [hv185, hv18] at hv186
  replace hv186 := hv186.trans (denote_vec_add_const _ subFastConst)
  rw [subFastVec_eq] at hv186
  simp only [hv184, hv89acp] at hv187
  replace hv187 := hv187.trans (denote_vec_sub vx2b (subOneAcp ysqb))
  simp only [hv187, hv18] at hv188
  replace hv188 := hv188.trans (denote_vec_add_const _ subFastConst)
  rw [subFastVec_eq] at hv188
  simp only [hv179, hv81] at hv189
  replace hv189 := hv189.trans (denote_vec_add vx2a ua)
  denote_clear v 185 185
  denote_clear v 187 187

  -- the limbs of the three, for `is_nonzero`'s `s62`
  have hysqaB : ∀ k, 0 ≤ R43x6.extractLimbs ysqa k ∧ R43x6.extractLimbs ysqa k < 2 ^ 44 := by
    intro k
    have h1 := hsqrA.u44.1 k
    have h2 := hsqrA.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega
  have hysqbB : ∀ k, 0 ≤ R43x6.extractLimbs ysqb k ∧ R43x6.extractLimbs ysqb k < 2 ^ 44 := by
    intro k
    have h1 := hsqrB.u44.1 k
    have h2 := hsqrB.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega
  have hacpaB := subOneAcp_bounds hysqaB
  have hacpbB := subOneAcp_bounds hysqbB
  have hvx2aB : ∀ k, 0 ≤ R43x6.extractLimbs vx2a k ∧ R43x6.extractLimbs vx2a k < 2 ^ 44 := by
    intro k
    have h1 := hmulvx2a.u44.1 k
    have h2 := hmulvx2a.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega
  have hvx2bB : ∀ k, 0 ≤ R43x6.extractLimbs vx2b k ∧ R43x6.extractLimbs vx2b k < 2 ^ 44 := by
    intro k
    have h1 := hmulvx2b.u44.1 k
    have h2 := hmulvx2b.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega

  -- every `peel_call` is done with its run equation, and they are the largest
  -- terms left in the context
  clear hrun₅ hrun₆ hrun₇ hrun₈ hsqrRunA hrunv2b hrunv4a hrunv4b hrunv3a hrunv3b hrunuv3a hrunuv3b hrunuv7a hrunuv7b hrunPow hrunxa hrunxb hrunx2a hrunx2b hrunvx2a hrunvx2b

  -- `is_nonzero` wants only `s62`, which these three are far inside
  have ht1aS62 : R43x6.S62 ((subFastVec vx2a (subOneAcp ysqa)).take R43x6.limbCount) := by
    have h1 : ∀ k, R43x6.FitsLong
        (R43x6.extractLimbs vx2a k - R43x6.extractLimbs (subOneAcp ysqa) k) := by
      intro k; have := hvx2aB k; have := hacpaB k; simp only [R43x6.FitsLong]; omega
    have h2 : ∀ k, R43x6.FitsLong
        (R43x6.extractLimbs vx2a k - R43x6.extractLimbs (subOneAcp ysqa) k + subFastLimb k) := by
      intro k
      have := hvx2aB k; have := hacpaB k; have := subFastLimb_bounds k
      simp only [R43x6.FitsLong]; omega
    constructor <;> intro i <;>
      rw [R43x6.toInts_take, extractLimbs_subFastVec h1 h2 i] <;>
      · have := hvx2aB i; have := hacpaB i; have := subFastLimb_bounds i; omega
  have ht1bS62 : R43x6.S62 ((subFastVec vx2b (subOneAcp ysqb)).take R43x6.limbCount) := by
    have h1 : ∀ k, R43x6.FitsLong
        (R43x6.extractLimbs vx2b k - R43x6.extractLimbs (subOneAcp ysqb) k) := by
      intro k; have := hvx2bB k; have := hacpbB k; simp only [R43x6.FitsLong]; omega
    have h2 : ∀ k, R43x6.FitsLong
        (R43x6.extractLimbs vx2b k - R43x6.extractLimbs (subOneAcp ysqb) k + subFastLimb k) := by
      intro k
      have := hvx2bB k; have := hacpbB k; have := subFastLimb_bounds k
      simp only [R43x6.FitsLong]; omega
    constructor <;> intro i <;>
      rw [R43x6.toInts_take, extractLimbs_subFastVec h1 h2 i] <;>
      · have := hvx2bB i; have := hacpbB i; have := subFastLimb_bounds i; omega
  have ht2aS62 : R43x6.S62 ((Vector.ofFn fun i : Fin 8 =>
      vx2a[i.val] + ua[i.val]).take R43x6.limbCount) := by
    have hb : ∀ k, R43x6.FitsLong (R43x6.extractLimbs vx2a k + R43x6.extractLimbs ua k) := by
      intro k; have := hvx2aB k; have := huaB k; simp only [R43x6.FitsLong]; omega
    constructor <;> intro i <;>
      rw [R43x6.toInts_take, extractLimbs_add vx2a ua hb i] <;>
      · have := hvx2aB i; have := huaB i; omega

  -- %190-%192: `t1nza`, `t1nzb`, `t2nza`
  refine name_of (u₂₉.popFrame u₂₉.mem) fun u₃₀ hu₃₀ => ?_
  have hrunT1a := is_nonzero_step ht1aS62 u₂₉ u₃₀ hu₃₀
  rw [← hv186] at hrunT1a
  peel_call hrunT1a
  refine name_of (u₃₀.popFrame u₃₀.mem) fun u₃₁ hu₃₁ => ?_
  have hrunT1b := is_nonzero_step ht1bS62 u₃₀ u₃₁ hu₃₁
  rw [← hv188] at hrunT1b
  peel_call hrunT1b
  refine name_of (u₃₁.popFrame u₃₁.mem) fun u₃₂ hu₃₂ => ?_
  have hrunT2a := is_nonzero_step ht2aS62 u₃₁ u₃₂ hu₃₂
  rw [← hv189] at hrunT2a
  peel_call hrunT2a


  -- %193-%194: `t1nza & t2nza`, and the test the branch reads. The `and` of
  -- two `is_nonzero`s is zero exactly when one of them is, so the `icmp` is
  -- the disjunction the C's `if( t1nza & t2nza ) goto faila` negates.
  denote_step_all v 194
  denote_eval v 193 194
  replace hv194 : v194 = PoisonOr.value
      (if ((R43x6.decode' (Vector.ofFn fun i : Fin 8 => vx2a[i.val] + ua[i.val]) : ℤ) : ZMod p) = 0
          ∨ ((R43x6.decode' (subFastVec vx2a (subOneAcp ysqa)) : ℤ) : ZMod p) = 0
        then 1 else 0) := by
    rw [hv194, hv193, hv17]
    by_cases h1 : ((R43x6.decode' (Vector.ofFn fun i : Fin 8 =>
        vx2a[i.val] + ua[i.val]) : ℤ) : ZMod p) = 0
    · rw [if_pos h1, if_pos (Or.inl h1)]
      simp [LLVM.and, LLVM.and?, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
    · by_cases h2 : ((R43x6.decode' (subFastVec vx2a (subOneAcp ysqa)) : ℤ) : ZMod p) = 0
      · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2)]
        simp [LLVM.and, LLVM.and?, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
      · rw [if_neg h1, if_neg h2, if_neg (fun h => h.elim h1 h2)]
        simp [LLVM.and, LLVM.and?, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  denote_clear v 193 193

  -- The constants the tail blocks read, in the shapes `EntryEnv` states them.
  -- `^bb0` folded some of these into its own form; the rest are still the
  -- `denote_dense` literals the prologue left.
  have hsubNeg : subFastConst = negConst := rfl
  replace hv18 : v18 = toBitVecValue 64 negConst := by rw [hv18, hsubNeg]
  replace hv24 : v24 = zeroVec.map PoisonOr.value := by rw [hv24, zeroVec_eq]
  replace hv19 : v19 = oneVec.map PoisonOr.value := by
    rw [hv19]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [toBitVecValue, addOneConst, oneVec]
  replace hv16 : v16 = PoisonOr.value (-1#32) := by rw [hv16]; rfl
  replace hv15 : v15 = PoisonOr.value (-2#32) := by rw [hv15]; rfl
  replace hv13 : v13 = sqrtM1Vec.map PoisonOr.value := by
    have h : v13 = toBitVecValue 64 #v[3467281080496, 6582290652611, 5210002954932,
        329084955603, 4526638806224, 373767602335, 0, 0] := by denote_dense hv13
    rw [h]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [toBitVecValue, sqrtM1Vec]
  replace hv12 : v12 = toBitVecValue 64 #v[0, 1, 8, 9, 4, 5, 12, 13] := by denote_dense hv12
  replace hv11 : v11 = toBitVecValue 64 #v[2, 3, 10, 11, 6, 7, 12, 13] := by denote_dense hv11
  replace hv10 : v10 = toBitVecValue 64 quadShift43 := by
    simp only [quadShift43]; denote_dense hv10
  replace hv9 : v9 = toBitVecValue 64 quadShift48 := by
    simp only [quadShift48]; denote_dense hv9
  replace hv1 : v1 = toBitVecValue 64 quadMask43 := by
    simp only [quadMask43]; denote_dense hv1
  replace hv0 : v0 = toBitVecValue 64 quadMask48 := by
    simp only [quadMask48]; denote_dense hv0

  -- `%44` is the `undef`/`insertelement` chain rather than a dense constant:
  -- `19` in the top four lanes, poison in the bottom four.
  replace hv44 : v44 = quadMul19 := by
    simp only [hv44, hv43, hv42, hv41, hv40, hv39, hv38, hv37, hv36, hv8, hv35,
      hv17, hv28, hv7, hv6, hv5, hv4, hv3, hv2]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, quadMul19]

  -- the `i32` the sign test compares: bit 63 of the encoding's last lane
  have hbit : ∀ x : BitVec 64,
      (BitVec.setWidth 32 (x >>> (63 : BitVec 64)) : BitVec 32)
        = if x.getLsbD 63 then 1 else 0 := by
    intro x
    by_cases h : x.getLsbD 63 = true
    · rw [if_pos h]; bv_decide
    · rw [if_neg h]; bv_decide

  -- `addVec`, the shape `^bb1` states its operand in
  have haddVec : ∀ x y : Vector (BitVec 64) 8,
      GeDecode2.addVec x y = Vector.ofFn fun i : Fin 8 => x[i.val] + y[i.val] :=
    fun _ _ => rfl

  -- what the four vectors hold, in the field
  have hUa : vecValue ua = ya ^ 2 - 1 := by
    rw [← decode'_cast_eq_vecValue ua huaB]; exact huaValue
  have hVa : vecValue va = d * ya ^ 2 + 1 := by
    rw [← decode'_cast_eq_vecValue62 va (fun k => ⟨(hvaB k).1, by have := (hvaB k).2; omega⟩)]
    exact hvaValue
  have hUb : vecValue ub = yb ^ 2 - 1 := by
    rw [← decode'_cast_eq_vecValue ub hubB]; exact hubValue
  have hVb : vecValue vb = d * yb ^ 2 + 1 := by
    rw [← decode'_cast_eq_vecValue62 vb (fun k => ⟨(hvbB k).1, by have := (hvbB k).2; omega⟩)]
    exact hvbValue

  -- the candidate roots, in the shape `Curve.lean`'s `sqrtCandidate_iff` tests:
  -- `x = u v³ (u v⁷)^((p-5)/8)`
  have hXa : vecValue xa
      = vecValue ua * vecValue va ^ 3 * (vecValue ua * vecValue va ^ 7) ^ ((p - 5) / 8) := by
    have h3 : vecValue uv3a = vecValue ua * vecValue va ^ 3 := by
      rw [hmuluv3a.value, hmulv3a.value, hsqr2a.value]; ring
    have h7 : vecValue uv7a = vecValue ua * vecValue va ^ 7 := by
      rw [hmuluv7a.value, h3, hsqrv4a.value, hsqr2a.value]; ring
    rw [hmulxa.value, hvalT0a, h3, h7, p_sub_five_div_eight]
  have hXb : vecValue xb
      = vecValue ub * vecValue vb ^ 3 * (vecValue ub * vecValue vb ^ 7) ^ ((p - 5) / 8) := by
    have h3 : vecValue uv3b = vecValue ub * vecValue vb ^ 3 := by
      rw [hmuluv3b.value, hmulv3b.value, hsqrv2b.value]; ring
    have h7 : vecValue uv7b = vecValue ub * vecValue vb ^ 7 := by
      rw [hmuluv7b.value, h3, hsqrv4b.value, hsqrv2b.value]; ring
    rw [hmulxb.value, hvalT0b, h3, h7, p_sub_five_div_eight]

  -- ... and what the two `is_nonzero` operands hold
  have hVX2a : ((R43x6.decode' vx2a : ℤ) : ZMod p) = (d * ya ^ 2 + 1) * vecValue xa ^ 2 := by
    rw [decode'_cast_eq_vecValue vx2a hvx2aB, hmulvx2a.value, hsqrx2a.value, hVa]
  have hVX2b : ((R43x6.decode' vx2b : ℤ) : ZMod p) = (d * yb ^ 2 + 1) * vecValue xb ^ 2 := by
    rw [decode'_cast_eq_vecValue vx2b hvx2bB, hmulvx2b.value, hsqrx2b.value, hVb]
  have ht1a : ((R43x6.decode' (subFastVec vx2a (subOneAcp ysqa)) : ℤ) : ZMod p)
      = (d * ya ^ 2 + 1) * vecValue xa ^ 2 - (ya ^ 2 - 1) := by
    rw [decode'_subFast_subOneAcp hvx2aB hysqaB, ← huadef, hVX2a, huaValue]
  have ht1b : ((R43x6.decode' (subFastVec vx2b (subOneAcp ysqb)) : ℤ) : ZMod p)
      = (d * yb ^ 2 + 1) * vecValue xb ^ 2 - (yb ^ 2 - 1) := by
    rw [decode'_subFast_subOneAcp hvx2bB hysqbB, ← hubdef, hVX2b, hubValue]
  have ht2a : ((R43x6.decode' (Vector.ofFn fun i : Fin 8 => vx2a[i.val] + ua[i.val]) : ℤ)
      : ZMod p) = (d * ya ^ 2 + 1) * vecValue xa ^ 2 + (ya ^ 2 - 1) := by
    rw [decode'_addVec_cast hvx2aB huaB, hVX2a, huaValue]
  have ht2b : ((R43x6.decode' (GeDecode2.addVec vx2b ub) : ℤ) : ZMod p)
      = (d * yb ^ 2 + 1) * vecValue xb ^ 2 + (yb ^ 2 - 1) := by
    rw [haddVec, decode'_addVec_cast hvx2bB hubB, hVX2b, hubValue]

  -- the branch conditions *are* `Decodable`, which is what `sqrtCandidate_iff`
  -- says: `x² v = ±u` exactly when `u/v` is a square
  have hdefA : Decodable (readWv hvsa) ↔ IsSquare ((ya ^ 2 - 1) / (d * ya ^ 2 + 1)) := by
    rw [hya]
  have hdefB : Decodable (readWv hvsb) ↔ IsSquare ((yb ^ 2 - 1) / (d * yb ^ 2 + 1)) := by
    rw [hyb]
  have hsqA : (((d * ya ^ 2 + 1) * vecValue xa ^ 2 + (ya ^ 2 - 1) = 0)
        ∨ ((d * ya ^ 2 + 1) * vecValue xa ^ 2 - (ya ^ 2 - 1) = 0))
      ↔ Decodable (readWv hvsa) := by
    rw [hdefA, ← sqrtCandidate_iff (u := ya ^ 2 - 1) (v := d * ya ^ 2 + 1)
      (x := vecValue xa) (denom_ne_zero ya) (by rw [hXa, hUa, hVa])]
    constructor
    · rintro (h | h)
      · exact Or.inr (by linear_combination h)
      · exact Or.inl (by linear_combination h)
    · rintro (h | h)
      · exact Or.inr (by linear_combination h)
      · exact Or.inl (by linear_combination h)
  have hsqB : (((d * yb ^ 2 + 1) * vecValue xb ^ 2 + (yb ^ 2 - 1) = 0)
        ∨ ((d * yb ^ 2 + 1) * vecValue xb ^ 2 - (yb ^ 2 - 1) = 0))
      ↔ Decodable (readWv hvsb) := by
    rw [hdefB, ← sqrtCandidate_iff (u := yb ^ 2 - 1) (v := d * yb ^ 2 + 1)
      (x := vecValue xb) (denom_ne_zero yb) (by rw [hXb, hUb, hVb])]
    constructor
    · rintro (h | h)
      · exact Or.inr (by linear_combination h)
      · exact Or.inl (by linear_combination h)
    · rintro (h | h)
      · exact Or.inr (by linear_combination h)
      · exact Or.inl (by linear_combination h)

  -- `^bb1`'s remaining `is_nonzero` input
  have ht2bS62 : R43x6.S62 ((GeDecode2.addVec vx2b ub).take R43x6.limbCount) := by
    have hb : ∀ k, R43x6.FitsLong (R43x6.extractLimbs vx2b k + R43x6.extractLimbs ub k) := by
      intro k; have := hvx2bB k; have := hubB k; simp only [R43x6.FitsLong]; omega
    rw [haddVec]
    constructor <;> intro i <;>
      rw [R43x6.toInts_take, extractLimbs_add vx2b ub hb i] <;>
      · have := hvx2bB i; have := hubB i; omega

  -- the caller's blocks, across the prologue and the twenty-odd calls
  have hidLt : ∀ q : Pointer, IsVecPtr s.mem q → q.id.id < s.alloc.nextFreeBlock :=
    fun q hq => lt_nextFreeBlock_of_fits hs hq.1
  have w₂₃ : u₂₃.WF := wroteT0.wf
  have e₂₄ : u₂₃ ≈ u₂₄ := hu₂₄ ▸ w₂₃.popFrame_equiv
  have w₂₄ : u₂₄.WF := w₂₃.of_equiv e₂₄
  have e₂₅ : u₂₄ ≈ u₂₅ := hu₂₅ ▸ w₂₄.popFrame_equiv
  have w₂₅ : u₂₅.WF := w₂₄.of_equiv e₂₅
  have e₂₆ : u₂₅ ≈ u₂₆ := hu₂₆ ▸ w₂₅.popFrame_equiv
  have w₂₆ : u₂₆.WF := w₂₅.of_equiv e₂₆
  have e₂₇ : u₂₆ ≈ u₂₇ := hu₂₇ ▸ w₂₆.popFrame_equiv
  have w₂₇ : u₂₇.WF := w₂₆.of_equiv e₂₇
  have e₂₈ : u₂₇ ≈ u₂₈ := hu₂₈ ▸ w₂₇.popFrame_equiv
  have w₂₈ : u₂₈.WF := w₂₇.of_equiv e₂₈
  have e₂₉ : u₂₈ ≈ u₂₉ := hu₂₉ ▸ w₂₈.popFrame_equiv
  have w₂₉ : u₂₉.WF := w₂₈.of_equiv e₂₉
  have e₃₀ : u₂₉ ≈ u₃₀ := hu₃₀ ▸ w₂₉.popFrame_equiv
  have w₃₀ : u₃₀.WF := w₂₉.of_equiv e₃₀
  have e₃₁ : u₃₀ ≈ u₃₁ := hu₃₁ ▸ w₃₀.popFrame_equiv
  have w₃₁ : u₃₁.WF := w₃₀.of_equiv e₃₁
  have e₃₂ : u₃₁ ≈ u₃₂ := hu₃₂ ▸ w₃₁.popFrame_equiv
  have w₃₂ : u₃₂.WF := w₃₁.of_equiv e₃₂
  have echain : u₂₃ ≈ u₃₂ :=
    e₂₄.trans (e₂₅.trans (e₂₆.trans (e₂₇.trans (e₂₈.trans (e₂₉.trans
      (e₃₀.trans (e₃₁.trans e₃₂)))))))
  have hcaller : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock →
      u₃₂.mem.live? b = s.mem.live? b := by
    intro b hb
    have hneSlot : ∀ k, (slotPtr s k).id ≠ b := fun k he => by
      have := slots.id k; rw [he] at this; omega
    have h₄ : m₄.mem.live? b = s.mem.live? b := by
      rw [hm₄, live?_splice_ne (by simpa [pb_high, Pointer.withOffset] using hneSlot Slot.sb),
        hm₃, live?_splice_ne (by simpa [pa_high, Pointer.withOffset] using hneSlot Slot.sa),
        hm₂, live?_splice_ne (hneSlot Slot.sb), hm₁, live?_splice_ne (hneSlot Slot.sa)]
      exact frame.fb b hb
    refine (echain.live b).symm.trans ?_
    exact (wroteT0.other b (Ne.symm (hneSlot Slot.t0a)) (Ne.symm (hneSlot Slot.t0b))).trans
      ((heq₂₂.live b).symm.trans h₄)
  -- the six blocks the region writes are the caller's own
  have hbelow : ∀ c : BlockId,
      (c = a03.id ∨ c = a14.id ∨ c = a25.id ∨ c = b03.id ∨ c = b14.id ∨ c = b25.id)
        → c.id < s.alloc.nextFreeBlock := by
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [hidLt a03 ha03, hidLt a14 ha14, hidLt a25 ha25,
      hidLt b03 hb03, hidLt b14 hb14, hidLt b25 hb25]

  -- the branch: `^bb1` when one of `a`'s two roots works, `^bb3` -- `faila` --
  -- when neither does. `%194` is `1` exactly on the disjunction, and
  -- `sqrtCandidate_iff` is what makes that disjunction `Decodable`.
  simp only [BlockCom.denote_term, Terminator.denote_condBr, Ctxt.Valuation.cons_zero, hv194]
  by_cases hcondA :
      ((R43x6.decode' (Vector.ofFn fun i : Fin 8 => vx2a[i.val] + ua[i.val]) : ℤ) : ZMod p) = 0
        ∨ ((R43x6.decode' (subFastVec vx2a (subOneAcp ysqa)) : ℤ) : ZMod p) = 0
  · -- `^bb1`: `_vsa` names a point, and `^bb1` makes the same test for `_vsb`
    have hda : Decodable (readWv hvsa) :=
      hsqA.mp (hcondA.imp (fun h => by rw [← ht2a]; exact h) (fun h => by rw [← ht1a]; exact h))
    rw [if_pos hcondA, if_pos rfl]
    simp only [pure_bind, Target.denote_mk, HVector.map]
    -- v4.34: the walk's valuation is only a `Γout.Valuation` past `implicit` transparency
    set_option backward.isDefEq.respectTransparency false in
    rw [bb1_run (env := ?envA) (h184 := hv184) (h90 := hv90) (h191 := by rfl)
      (hs62 := ht2bS62) (s := u₃₂)]
    case envA => exact ⟨hv32, hv33, hv34, hv27, hv25, hv24, hv23, hv22, hv21, hv19, hv18, hv17,
      hv16, hv15, hv14, hv13, hv12, hv11, hv10, hv9, hv44, hv1, hv0,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
    -- the state `^bb1` hands on, and the caller's six out-vectors in it
    have e₃₃ : u₃₂ ≈ u₃₂.popFrame u₃₂.mem := w₃₂.popFrame_equiv
    have w₃₃ : (u₃₂.popFrame u₃₂.mem).WF := w₃₂.of_equiv e₃₃
    have hc₃₃ : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock →
        (u₃₂.popFrame u₃₂.mem).mem.live? b = s.mem.live? b :=
      fun b hb => (e₃₃.live b).symm.trans (hcaller b hb)
    have qa03 : IsVecPtr (u₃₂.popFrame u₃₂.mem).mem a03 :=
      ⟨fits_of_live?_eq (hc₃₃ a03.id (hidLt a03 ha03)) ha03.1, ha03.2⟩
    have qa14 : IsVecPtr (u₃₂.popFrame u₃₂.mem).mem a14 :=
      ⟨fits_of_live?_eq (hc₃₃ a14.id (hidLt a14 ha14)) ha14.1, ha14.2⟩
    have qa25 : IsVecPtr (u₃₂.popFrame u₃₂.mem).mem a25 :=
      ⟨fits_of_live?_eq (hc₃₃ a25.id (hidLt a25 ha25)) ha25.1, ha25.2⟩
    have qb03 : IsVecPtr (u₃₂.popFrame u₃₂.mem).mem b03 :=
      ⟨fits_of_live?_eq (hc₃₃ b03.id (hidLt b03 hb03)) hb03.1, hb03.2⟩
    have qb14 : IsVecPtr (u₃₂.popFrame u₃₂.mem).mem b14 :=
      ⟨fits_of_live?_eq (hc₃₃ b14.id (hidLt b14 hb14)) hb14.1, hb14.2⟩
    have qb25 : IsVecPtr (u₃₂.popFrame u₃₂.mem).mem b25 :=
      ⟨fits_of_live?_eq (hc₃₃ b25.id (hidLt b25 hb25)) hb25.1, hb25.2⟩
    by_cases hcondB :
        ((R43x6.decode' (GeDecode2.addVec vx2b ub) : ℤ) : ZMod p) = 0
          ∨ ((R43x6.decode' (subFastVec vx2b (subOneAcp ysqb)) : ℤ) : ZMod p) = 0
    · -- both encodings name a point: `^bb2`, and `0`
      have hdb : Decodable (readWv hvsb) :=
        hsqB.mp (hcondB.imp (fun h => by rw [← ht2b]; exact h) (fun h => by rw [← ht1b]; exact h))
      rw [if_pos (show GeDecode2.nonzeroBit (GeDecode2.addVec vx2b ub)
            &&& (if ((R43x6.decode' (subFastVec vx2b (subOneAcp ysqb)) : ℤ) : ZMod p) = 0
              then 0 else 1) = 0 from by
          rcases hcondB with h | h
          · simp [GeDecode2.nonzeroBit, h]
          · simp [h])]
      refine GeDecode2.bb2_full (V := ?vv)
        (xa := xa) (xb := xb) (ya := yaVec) (yb := ybVec)
        (sgnA := BitVec.setWidth 32 ((readWv hvsa)[3] >>> (63 : BitVec 64)))
        (sgnB := BitVec.setWidth 32 ((readWv hvsb)[3] >>> (63 : BitVec 64)))
        (t1nza := if ((R43x6.decode' (subFastVec vx2a (subOneAcp ysqa)) : ℤ) : ZMod p) = 0
          then 0 else 1)
        (t1nzb := if ((R43x6.decode' (subFastVec vx2b (subOneAcp ysqb)) : ℤ) : ZMod p) = 0
          then 0 else 1)
        (ua := readWv hvsa) (ub := readWv hvsb) (s := u₃₂.popFrame u₃₂.mem)
        (env := ?env2) (inp := ?inp2)
        (hya := hdecA) (hyb := hdecB) (hsgnA := hbit _) (hsgnB := hbit _)
        (h190 := ?h190) (h191 := ?h191) (hrootA := ?hrootA) (hrootB := ?hrootB)
        (ht1nza := by split <;> simp) (ht1nzb := by split <;> simp)
        (hxaU := hmulxa.u44) (hxa6 := hmulxa.z6) (hxa7 := hmulxa.z7)
        (hxbU := hmulxb.u44) (hxb6 := hmulxb.z6) (hxb7 := hmulxb.z7)
        (hyaU := hunpA) (hya6 := h6A) (hya7 := h7A)
        (hybU := hunpB) (hyb6 := h6B) (hyb7 := h7B)
        (hs := w₃₃) (pa03 := qa03) (pa14 := qa14) (pa25 := qa25)
        (pb03 := qb03) (pb14 := qb14) (pb25 := qb25) (hne := hne)
        fun va03 va14 va25 vb03 vb14 vb25 s₂ hrun2 hmem2 hDa hDb => ?main
      case main =>
        refine ⟨s₂, ?_, va03, va14, va25, vb03, vb14, vb25, ?_, ?_, ?_, ?_⟩
        · rw [if_pos hda, if_pos hdb]; exact hrun2
        · exact GeDecode2.outMem_popFrame_equiv hs hbelow hc₃₃ hmem2
        · exact fun _ _ => ⟨by rw [if_pos hda, if_pos hdb], hDa, hDb⟩
        · exact fun h => absurd hda h
        · exact fun _ h => absurd hdb h
      case env2 => exact ⟨hv32, hv33, hv34, hv27, hv25, hv24, hv23, hv22, hv21, hv19, hv18, hv17,
        hv16, hv15, hv14, hv13, hv12, hv11, hv10, hv9, hv44, hv1, hv0,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
      case inp2 => exact ⟨hv159, hv164, rfl, rfl, hv54, hv56, rfl, rfl⟩
      case h190 =>
        rw [← hya]
        constructor
        · intro h
          have h0 : ((R43x6.decode' (subFastVec vx2a (subOneAcp ysqa)) : ℤ) : ZMod p) = 0 := by
            by_contra hcx
            rw [if_neg hcx] at h
            exact absurd h (by decide)
          rw [ht1a] at h0
          linear_combination h0
        · intro h
          refine if_pos ?_
          rw [ht1a]
          linear_combination h
      case h191 =>
        rw [← hyb]
        constructor
        · intro h
          have h0 : ((R43x6.decode' (subFastVec vx2b (subOneAcp ysqb)) : ℤ) : ZMod p) = 0 := by
            by_contra hcx
            rw [if_neg hcx] at h
            exact absurd h (by decide)
          rw [ht1b] at h0
          linear_combination h0
        · intro h
          refine if_pos ?_
          rw [ht1b]
          linear_combination h
      case hrootA =>
        rw [← hya]
        rcases hcondA with h | h
        · refine Or.inr ?_
          rw [ht2a] at h
          linear_combination h
        · exact Or.inl (if_pos h)
      case hrootB =>
        rw [← hyb]
        rcases hcondB with h | h
        · refine Or.inr ?_
          rw [ht2b] at h
          linear_combination h
        · exact Or.inl (if_pos h)
    · -- `_vsb` does not: `^bb4`, and `-2`
      have hdb : ¬ Decodable (readWv hvsb) := fun h => hcondB (by
        rcases hsqB.mpr h with h' | h'
        · exact Or.inl (by rw [ht2b]; exact h')
        · exact Or.inr (by rw [ht1b]; exact h'))
      push_neg at hcondB
      rw [if_neg (show ¬(GeDecode2.nonzeroBit (GeDecode2.addVec vx2b ub)
            &&& (if ((R43x6.decode' (subFastVec vx2b (subOneAcp ysqb)) : ℤ) : ZMod p) = 0
              then 0 else 1) = 0) from by
          simp [GeDecode2.nonzeroBit, hcondB.1, hcondB.2]),
        bb4_run (env := ?env4) (ha03 := qa03.1) (ha14 := qa14.1) (ha25 := qa25.1)
          (hb03 := qb03.1) (hb14 := qb14.1) (hb25 := qb25.1)]
      case env4 => exact ⟨hv32, hv33, hv34, hv27, hv25, hv24, hv23, hv22, hv21, hv19, hv18, hv17,
        hv16, hv15, hv14, hv13, hv12, hv11, hv10, hv9, hv44, hv1, hv0,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨({ (u₃₂.popFrame u₃₂.mem) with mem := GeDecode2.zeroOutMem (u₃₂.popFrame u₃₂.mem).mem a03 a14 a25 b03 b14 b25 } : GlobalState), ?_,
        zeroVec, zeroVec, zeroVec, zeroVec, zeroVec, zeroVec, ?_, ?_, ?_, ?_⟩
      · rw [if_pos hda, if_neg hdb]
      · exact GeDecode2.outMem_popFrame_equiv hs hbelow hc₃₃
          (GeDecode2.zeroOutMem_equiv hne (u₃₂.popFrame u₃₂.mem))
      · exact fun _ h => absurd h hdb
      · exact fun h => absurd hda h
      · exact fun _ _ => ⟨by rw [if_pos hda, if_neg hdb], rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- `^bb3`: neither root works, so `_vsa` does not decode -- the `-1` path
    have hda : ¬ Decodable (readWv hvsa) := fun h => hcondA (by
      rcases hsqA.mpr h with h' | h'
      · exact Or.inl (by rw [ht2a]; exact h')
      · exact Or.inr (by rw [ht1a]; exact h'))
    rw [if_neg hcondA, if_neg (by decide : ¬((0 : BitVec 1) = 1))]
    simp only [pure_bind, Target.denote_mk, HVector.map]
    have ra03 : IsVecPtr u₃₂.mem a03 :=
      ⟨fits_of_live?_eq (hcaller a03.id (hidLt a03 ha03)) ha03.1, ha03.2⟩
    have ra14 : IsVecPtr u₃₂.mem a14 :=
      ⟨fits_of_live?_eq (hcaller a14.id (hidLt a14 ha14)) ha14.1, ha14.2⟩
    have ra25 : IsVecPtr u₃₂.mem a25 :=
      ⟨fits_of_live?_eq (hcaller a25.id (hidLt a25 ha25)) ha25.1, ha25.2⟩
    have rb03 : IsVecPtr u₃₂.mem b03 :=
      ⟨fits_of_live?_eq (hcaller b03.id (hidLt b03 hb03)) hb03.1, hb03.2⟩
    have rb14 : IsVecPtr u₃₂.mem b14 :=
      ⟨fits_of_live?_eq (hcaller b14.id (hidLt b14 hb14)) hb14.1, hb14.2⟩
    have rb25 : IsVecPtr u₃₂.mem b25 :=
      ⟨fits_of_live?_eq (hcaller b25.id (hidLt b25 hb25)) hb25.1, hb25.2⟩
    set_option backward.isDefEq.respectTransparency false in
    rw [bb3_run (env := ?env3) (ha03 := ra03.1) (ha14 := ra14.1) (ha25 := ra25.1)
      (hb03 := rb03.1) (hb14 := rb14.1) (hb25 := rb25.1)]
    case env3 => exact ⟨hv32, hv33, hv34, hv27, hv25, hv24, hv23, hv22, hv21, hv19, hv18, hv17,
      hv16, hv15, hv14, hv13, hv12, hv11, hv10, hv9, hv44, hv1, hv0,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨({ u₃₂ with mem := GeDecode2.zeroOutMem u₃₂.mem a03 a14 a25 b03 b14 b25 } : GlobalState), ?_,
      zeroVec, zeroVec, zeroVec, zeroVec, zeroVec, zeroVec, ?_, ?_, ?_, ?_⟩
    · rw [if_neg hda]
    · exact GeDecode2.outMem_popFrame_equiv hs hbelow hcaller
        (GeDecode2.zeroOutMem_equiv hne u₃₂)
    · exact fun h => absurd h hda
    · exact fun _ => ⟨by rw [if_neg hda], rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact fun h => absurd h hda

end Firedancer.Avx512
