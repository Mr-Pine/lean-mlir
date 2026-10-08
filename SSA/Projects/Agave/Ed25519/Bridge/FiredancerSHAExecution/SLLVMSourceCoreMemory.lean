import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreContract
import SSA.Projects.Firedancer.Proof.Tactics

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
set_option maxHeartbeats 1000000
variable {m m' : MemoryState} {p : Pointer} {s : GlobalState} {bytes n k w : Nat}

theorem SmallRange.fits (h : SmallRange m p bytes) : Fits m p (8 * bytes) := by
  obtain ⟨b, hb, _, hsz⟩ := h
  exact ⟨b, getElem?_of_live? hb, by
    simpa only [Pointer.offsetInBits, LiveBlock.lengthInBits, Nat.mul_add] using
      Nat.mul_le_mul_left 8 hsz⟩

theorem SmallRange.offset_lt (h : SmallRange m p bytes) : p.offset.toNat + bytes < 2^63 := by
  obtain ⟨b, _, hb, hs⟩ := h
  omega

theorem SmallRange.mono (h : SmallRange m p bytes) (hle : n ≤ bytes) : SmallRange m p n := by
  obtain ⟨b, hb, hs, ho⟩ := h
  exact ⟨b, hb, hs, by omega⟩

theorem SmallRange.of_live_eq (h : SmallRange m p bytes)
    (he : m'.live? p.id = m.live? p.id) : SmallRange m' p bytes := by
  obtain ⟨b, hb, hs, ho⟩ := h
  exact ⟨b, he.trans hb, hs, ho⟩

theorem SmallRange.afterAlloca (h : SmallRange s.mem p bytes) (hwf : s.WF) (bits : Nat) :
    SmallRange (s.afterAlloca bits).mem p bytes :=
  h.of_live_eq (live?_afterAlloca_of_fits hwf bits h.fits)

theorem SmallRange.add (h : SmallRange m p bytes) (hk : k + n ≤ bytes) :
    SmallRange m (p.withOffset (BitVec.ofNat 64 k)) n := by
  obtain ⟨b, hb, hs, ho⟩ := h
  have hk64 : k < 2^64 := by omega
  have hsum : p.offset.toNat + k < 2^64 := by omega
  refine ⟨b, hb, hs, ?_⟩
  simpa only [Pointer.withOffset, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hsum] using (by omega : p.offset.toNat + k + n ≤ b.length)

theorem SmallRange.splice (h : SmallRange m p bytes) (q : Pointer) (value : BitVec w) :
    SmallRange (m.splice q value) p bytes := by
  obtain ⟨b, hb, hs, ho⟩ := h
  by_cases he : q.id = p.id
  · refine ⟨{b with bytes := spliceBits b.bytes q.offsetInBits value}, ?_, hs, ho⟩
    have hq : m.live? q.id = some b := he.symm ▸ hb
    simpa only [he] using splicedLive m q b hq value
  · exact ⟨b, (live?_splice_ne he).trans hb, hs, ho⟩

theorem readBits_eq_readWord (h : Fits m p w) : readBits m p w = readWord h := by
  simp only [readBits, readWord?_eq_some h rfl, Option.getD_some]

theorem readBits_of_live_eq (he : m'.live? p.id = m.live? p.id) :
    readBits m' p w = readBits m p w := by
  simp only [readBits, readWord?, he]

theorem readBits_afterAlloca (h : Fits s.mem p w) (hwf : s.WF) (bits : Nat) :
    readBits (s.afterAlloca bits).mem p w = readBits s.mem p w :=
  readBits_of_live_eq (live?_afterAlloca_of_fits hwf bits h)

/-- Run the actual scalar load, exposing only its block-byte observation. -/
theorem run_load_readBits (h : Fits m p w) :
    StateT.run (SLLVM.load (.value p) (.bitvec (.concrete w))) m =
      .value (.value (readBits m p w), m) := by
  obtain ⟨b, hb, hs⟩ := h
  rw [run_load (t := .bitvec (.concrete w)) hb hs]
  have hl : m.live? p.id = some b := by simp only [MemoryState.live?, hb]
  simp only [readBits, readWord?, hl, Option.bind_some, Option.pure_def, Option.getD_some]
  rfl

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
