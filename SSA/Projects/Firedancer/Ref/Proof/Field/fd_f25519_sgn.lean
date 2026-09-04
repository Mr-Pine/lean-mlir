import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_sgn
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Limb
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_tobytes

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The region serialises `q` into a 32-byte local, loads its first byte and
masks off the low bit. Pending `fd_f25519_tobytes` conformance, which supplies
the encoding of `readFieldElem hq`; the low byte's low bit is then that
element's canonical representative mod 2. The local dies with the frame, so the
state comes back equivalent. -/
theorem fd_f25519_sgn_conforms (q : Pointer) (s : GlobalState)
    (hs : s.WF)
    (hq : IsFieldElemPtr s.mem q)
    (hqlimb : LimbBounds hq) :
    fd_f25519_sgn_spec q s hq := by
  simp only [fd_f25519_sgn_spec, Cfg.denote]

  obtain ⟨t, s₁, htdef, hs₁def, hs₁WF, htfits, htid, htoff, -, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (32 * 8)
  have fb : FrameBelow s.alloc.nextFreeBlock s s₁ :=
    hs₁def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
  have hnq : q.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hq.left
  have htq : t.id ≠ q.id := fun h => by rw [h] at htid; omega
  have hbuf₁ : IsByteBufPtr s₁.mem t := ⟨htfits, by simp [htoff]⟩
  have pq₁ : IsFieldElemPtr s₁.mem q := isFieldElemPtr_of_live?_eq (fb q.id hnq) hq
  have hvq₁ : readFieldElem pq₁ = readFieldElem hq :=
    readFieldElem_eq_of
      ((readFieldElem?_of_live?_eq (fb q.id hnq)).trans (Option.some_get _).symm)
  have hqlimb₁ : LimbBounds pq₁ :=
    limbBounds_of_readLimb? pq₁
      (limbBounds_of_live?_eq (fb q.id hnq) (limbBounds_readLimb? hq hqlimb))

  obtain ⟨out, hout, s₂, hrun, heq⟩ :=
    fd_f25519_tobytes_conforms t q s₁ hs₁WF hbuf₁ pq₁ hqlimb₁

  have hout' : out = BitVec.ofNat 256 (readFieldElem hq).val := by
    rw [← hvq₁, ← hout, readBuf_splice out hbuf₁]

  have hzext : BitVec.setWidth 32 (BitVec.ofNat 8 ((readFieldElem hq).val % 2))
      = BitVec.ofNat 32 ((readFieldElem hq).val % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
    omega

  -- §4 the frame held only `buf`, so popping it restores `s`
  have fbEnd : FrameBelow s.alloc.nextFreeBlock s s₂ :=
    FrameBelow.of_equiv heq (FrameBelow.splice (by omega) fb)

  refine ⟨s.popFrame s₂.mem, run_runFunction (s' := s₂) ?walk,
    GlobalState.Equiv.symm (FrameBelow.popFrame_equiv hs fbEnd)⟩

  denote_step_all v 1
  peel_alloca from s as s₁ with hs₁def
  rw [← htdef]
  peel_lifetime
  peel_call hrun

  -- the buffer's block in `s₂`: the load reads byte 0 of what `tobytes` wrote
  have hbuf₂ : IsByteBufPtr s₂.mem t :=
    ⟨fits_equiv heq (by simpa using fits_splice hbuf₁.left), hbuf₁.right⟩
  obtain ⟨blk, hblk, hlen⟩ := id hbuf₂.left
  have hblkbuf : blk.bytes.extractLsb' t.offsetInBits 256 = out := by
    have hread : readBuf? t s₂.mem = some out := by
      rw [readBuf?_eq_readWord?, readWord?_of_live?_eq (heq.live t.id).symm,
        ← readBuf?_eq_readWord?]
      exact readBuf?_splice out hbuf₁.left
    simpa [readBuf?, MemoryState.live?, hblk] using hread
  have hbyte₀ : blk.bytes.extractLsb' t.offsetInBits 8 = out.extractLsb' 0 8 := by
    rw [← hblkbuf, extractLsb'_extractLsb' _ (by omega), Nat.add_zero]

  peel_load (.bitvec (.concrete 8)), blk, t, hblk, s₂

  denote_step_all v 6
  peel_lifetime
  simp_return

  denote_eval v 0 1
  denote_eval v 5 6
  simp [hv6, hv5, LLVM.and, LLVM.and?, LLVM.zext, LLVM.zext?, hv1, LLVM.const?, hbyte₀]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (b := 2^32) ((show (readFieldElem hq).val % 2 < 2 from by omega).trans (by omega)),
    BitVec.toNat_and, Nat.mod_eq_of_lt (a := 1) (b := 2^32) (by simp),
    Nat.and_one_is_mod,
    BitVec.toNat_setWidth,
    Nat.mod_mod_of_dvd (b := 2^32) (c := 2) _ (by omega),
    Nat.mod_mod_of_dvd (b := 2^8) (c := 2) _ (by omega),
    hout',
    Nat.mod_mod_of_dvd (b := 2^256) (c := 2) _ (by omega)]

end Firedancer.Ref
