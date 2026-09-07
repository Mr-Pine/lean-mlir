import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_is_zero
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_set_zero
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_ge_is_eq


namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem fd_ed25519_point_is_zero_conforms (p: Pointer) (s: GlobalState)
  (hs : s.WF)
  (hp : IsQuadPtr s.mem p)
  (hpU46 : (readQuad hp).U46)
  (hpzUnit : IsUnit (readQuad hp).toPoint.Z) :
  fd_ed25519_point_is_zero_spec p s hp := by
    simp only [fd_ed25519_point_is_zero_spec, Cfg.denote]

    obtain ⟨q, sAlloc, hqdef, hsAlloc, -, -, -, -, -, -⟩ :=
      GlobalState.exists_afterAlloca_facts s hs (3 * 8 * 64)
    obtain ⟨zquad, hzquadU46, hzquad, hzzUnit, ⟨zstate, hzstate, hzstate_eq⟩⟩ := fd_ed25519_point_set_zero_conforms _ _ (hs.afterAlloca _) ⟨fits_afterAlloca s _, by simp⟩
    rw [← hsAlloc] at hzstate
    let pQuad := readQuad hp
    obtain ⟨eqstate, heqstate, heqstate_eq⟩ := spec_run_fd_r43x6_ge_is_eq pQuad zquad hpU46 hzquadU46 hpzUnit hzzUnit zstate
        (((hs.afterAlloca _).splice).of_equiv hzstate_eq)

    -- the frame holds only the `fd_ed25519_point_t z[1]` slot: `set_zero` writes
    -- it, `ge_is_eq` only reads
    have fbZ : FrameBelow s.alloc.nextFreeBlock s zstate :=
      FrameBelow.of_equiv hzstate_eq
        (FrameBelow.splice (le_refl _) (FrameBelow.afterAlloca (le_refl _) (.refl _ _)))

    refine ⟨s.popFrame eqstate.mem, run_runFunction (s' := eqstate) ?_,
      GlobalState.Equiv.symm (FrameBelow.popFrame_equiv hs
        (FrameBelow.of_equiv (GlobalState.Equiv.symm heqstate_eq) fbZ))⟩

    denote_step_all v 2
    denote_eval v 0 2
    simp only [LLVM.const?] at hv0 hv1 hv2
    subst hv0 hv1 hv2

    peel_alloca from s as sAlloc with hsAlloc
    peel_lifetime

    peel_call hzstate

    obtain ⟨pblk, hpblk, hplen⟩ := hp.1
    have hplt : p.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hp.1
    have hplive : s.mem.live? p.id = some pblk := by simp [MemoryState.live?, hpblk]
    have hzp : zstate.mem[p.id]? = some (.live pblk) :=
      getElem?_of_live? ((fbZ p.id hplt).trans hplive)

    peel_load (.vector 8 (.bitvec (.concrete 64))), pblk, p, hzp, zstate
    rw [unflatten_readQuad_v03 hp hplive]

    have hzfits : Fits zstate.mem p (3 * 8 * 64) := ⟨pblk, hzp, hplen⟩

    peel_gep 64 with p, hzfits, zstate as pField

    have h64 : (64 : BitVec 64).toNat = 64 := rfl
    have hoff : pField.offsetInBits = p.offsetInBits + 512 := by
      have hb := hp.2
      simp only [pField, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h64] at hb ⊢
      omega
    have hzpField : zstate.mem[pField.id]? = some (.live pblk) := hzp

    peel_load (.vector 8 (.bitvec (.concrete 64))), pblk, pField, hzpField, zstate
    rw [hoff, unflatten_readQuad_v14 hp hplive]

    peel_gep 128 with p, hzfits, zstate as pField25

    have h128 : (128 : BitVec 64).toNat = 128 := rfl
    have hoff25 : pField25.offsetInBits = p.offsetInBits + 1024 := by
      have hb := hp.2
      simp only [pField25, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h128] at hb ⊢
      omega
    have hzpField25 : zstate.mem[pField25.id]? = some (.live pblk) := hzp

    peel_load (.vector 8 (.bitvec (.concrete 64))), pblk, pField25, hzpField25, zstate
    rw [hoff25, unflatten_readQuad_v25 hp hplive]

    -- The zero point: `set_zero` wrote `zquad.BV` over the whole alloca'd slot.
    let slot : Pointer := ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩
    let zblk : LiveBlock := ⟨192, spliceBits (0#1536) 0 zquad.BV⟩
    have hzblkBytes : zblk.bytes = spliceBits (0#1536) 0 zquad.BV := rfl
    have hslotAlloc : (s.afterAlloca (3 * 8 * 64)).mem.live? slot.id = some ⟨192, 0#1536⟩ :=
      live?_afterAlloca_self s (3 * 8 * 64)
    have hzslotE : zstate.mem[slot.id]? = some (.live zblk) :=
      getElem?_of_live? <| (hzstate_eq.live _).symm.trans <| splicedLive _ slot _ hslotAlloc zquad.BV
    have hzslotFits : Fits zstate.mem slot (3 * 8 * 64) :=
      ⟨zblk, hzslotE, by simp [slot, zblk, Pointer.offsetInBits, LiveBlock.lengthInBits]⟩
    have hslotOff : slot.offsetInBits = 0 := by simp [slot, Pointer.offsetInBits]
    have hslotLen : slot.offsetInBits + 512 ≤ zblk.lengthInBits := by
      simp [slot, zblk, Pointer.offsetInBits, LiveBlock.lengthInBits]

    peel_load (.vector 8 (.bitvec (.concrete 64))), zblk, slot, hzslotE, zstate
    rw [hslotOff, hzblkBytes, unflatten_spliced_v03 (0#1536) zquad (by omega)]

    peel_gep 64 with (⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ : Pointer), hzslotFits, zstate as slotField
    have hslotFieldOff : slotField.offsetInBits = 512 := by
      simp [slotField, Pointer.withOffset, Pointer.offsetInBits]
    have hslotFieldLen : slotField.offsetInBits + 512 ≤ zblk.lengthInBits := by
      simp [hslotFieldOff, zblk, LiveBlock.lengthInBits]

    have hzslotFieldE : zstate.mem[slotField.id]? = some (.live zblk) := hzslotE
    peel_load (.vector 8 (.bitvec (.concrete 64))), zblk, slotField, hzslotFieldE, zstate
    rw [hslotFieldOff, hzblkBytes, unflatten_spliced_v14 (0#1536) zquad (by omega)]

    peel_gep 128 with (⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ : Pointer), hzslotFits, zstate as slotField25
    have hslotField25Off : slotField25.offsetInBits = 1024 := by
      simp [slotField25, Pointer.withOffset, Pointer.offsetInBits]
    have hslotField25Len : slotField25.offsetInBits + 512 ≤ zblk.lengthInBits := by
      simp [hslotField25Off, zblk, LiveBlock.lengthInBits]

    have hzslotField25E : zstate.mem[slotField25.id]? = some (.live zblk) := hzslotE
    peel_load (.vector 8 (.bitvec (.concrete 64))), zblk, slotField25, hzslotField25E, zstate
    rw [hslotField25Off, hzblkBytes, unflatten_spliced_v25 (0#1536) zquad (by omega)]


    peel_call heqstate
    peel_lifetime
    simp_return
    subst pQuad
    have hiff : (readQuad hp).toPoint.SamePoint zquad.toPoint ↔
             (readQuad hp).toPoint.SamePoint Point.zero := by
      constructor
      · intro h
        exact Point.samePoint_equivalence.trans h hzquad
      · intro h
        exact Point.samePoint_equivalence.trans h (Point.samePoint_equivalence.symm hzquad)
    simp [hiff]

end Firedancer.Avx512
