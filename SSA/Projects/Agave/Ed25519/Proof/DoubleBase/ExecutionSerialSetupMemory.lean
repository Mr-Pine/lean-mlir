import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSetup

/-! Readback and contextual global facts for the real serial setup writes. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readField readPoint readCached readProjective)
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

def serialIdentityPoint : SerialPoint.LimbPoint :=
  ⟨fun _ => 0, ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], fun _ => 0⟩

theorem serialIdentity_fields (s : GlobalState) (p : Pointer) (hp : Buffer s.mem p 120) :
    (serialIdentityState s p).mem.readAt p 320 = 0#320 ∧
    (serialIdentityState s p).mem.readAt (p.add 40#64) 320 = 1#320 ∧
    (serialIdentityState s p).mem.readAt (p.add 80#64) 320 = 1#320 := by
  have h80_0 := SerialPoint.Execution.subranges_disjoint hp
    (i := 80) (ni := 40) (j := 0) (nj := 40) (by decide) (by decide) (by decide)
  have h40_0 := SerialPoint.Execution.subranges_disjoint hp
    (i := 40) (ni := 40) (j := 0) (nj := 40) (by decide) (by decide) (by decide)
  have h80_40 := SerialPoint.Execution.subranges_disjoint hp
    (i := 80) (ni := 40) (j := 40) (nj := 40) (by decide) (by decide) (by decide)
  simp only [Pointer.add_zero] at h80_0 h40_0
  have h0 := hp.fits_at 0 40 (by decide)
  simp only [Pointer.add_zero] at h0
  refine ⟨?_, ?_, ?_⟩
  · unfold serialIdentityState serialIdentityY serialIdentityZero
    erw [MemoryState.readAt_storeAt_disjoint h80_0,
      MemoryState.readAt_storeAt_disjoint h40_0, MemoryState.readAt_storeAt_self h0]
  · unfold serialIdentityState serialIdentityY serialIdentityZero
    erw [MemoryState.readAt_storeAt_disjoint h80_40,
      MemoryState.readAt_storeAt_self (hp.fits_at 40 40 (by decide)).storeAt]
  · unfold serialIdentityState serialIdentityY serialIdentityZero
    exact MemoryState.readAt_storeAt_self (hp.fits_at 80 40 (by decide)).storeAt.storeAt _

/-- Five actual u64 loads are slices of the physical 40-byte coordinate. -/
theorem setup_readLimbs_of_readAt (s : GlobalState) (p : Pointer) (hp : Buffer s.mem p 40)
    (value : BitVec 320) (hread : s.mem.readAt p 320 = value) (i : Fin 5) :
    SerialFieldMul.readLimbs s p i = value.extractLsb' (64 * i.val) 64 := by
  have hk : 8 * i.val < 2^64 := by omega
  have he := MemoryState.readAt_add_of_readAt hp.fits
    (hp.offset_noOverflow (8*i.val) (by omega))
    (show (BitVec.ofNat 64 (8*i.val)).toNat * 8 + 64 ≤ 320 by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; omega) hread
  simpa only [SerialFieldMul.readLimbs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
    show 8 * i.val * 8 = 64 * i.val by omega] using he

theorem serialIdentity_readProjective (s : GlobalState) (p : Pointer)
    (hp : Buffer s.mem p 120) :
    readProjective (serialIdentityState s p) p = serialIdentityPoint := by
  obtain ⟨hX, hY, hZ⟩ := serialIdentity_fields s p hp
  have hf := serialIdentity_buffer (p := p) hp
  have hf0 := hf.slice 0 40 (by decide)
  simp only [Pointer.add_zero] at hf0
  apply PointArithmetic.Extended.ext
  · funext i
    change (SerialFieldMul.readLimbs _ _ i).toNat = 0
    erw [setup_readLimbs_of_readAt _ _ hf0 _ hX]
    fin_cases i <;> decide +kernel
  · funext i
    change (SerialFieldMul.readLimbs _ _ i).toNat = (![1, 0, 0, 0, 0] : Fin 5 → Nat) i
    erw [setup_readLimbs_of_readAt _ _ (hf.slice 40 40 (by decide)) _ hY]
    fin_cases i <;> decide +kernel
  · funext i
    change (SerialFieldMul.readLimbs _ _ i).toNat = (![1, 0, 0, 0, 0] : Fin 5 → Nat) i
    erw [setup_readLimbs_of_readAt _ _ (hf.slice 80 40 (by decide)) _ hZ]
    fin_cases i <;> decide +kernel
  · rfl

theorem serialIdentity_pointTight : SerialPoint.PointTight serialIdentityPoint := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro i; fin_cases i <;> decide +kernel

theorem serialIdentity_readField_ne (s : GlobalState) (p q : Pointer)
    (hne : p.id ≠ q.id) :
    readField (serialIdentityState s p) q = readField s q := by
  unfold readField SerialFieldMul.unsigned
  funext i
  unfold SerialFieldMul.readLimbs serialIdentityState serialIdentityY serialIdentityZero
  rw [MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne)),
    MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne)),
    MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne))]

theorem serialIdentity_readCached_ne (s : GlobalState) (p q : Pointer)
    (hne : p.id ≠ q.id) :
    readCached (serialIdentityState s p) q = readCached s q := by
  apply PointArithmetic.Extended.ext
  all_goals apply serialIdentity_readField_ne; simpa only [Pointer.add_id] using hne

/-- Exact identity initializer, with only the live identity global required. -/
structure SerialIdentityReady (identity : Pointer) (s : GlobalState) : Prop where
  offsetZero : identity.offset = 0
  present : Verifier.Execution.identityOne.Present identity.id s.mem

theorem SerialIdentityReady.buffer (h : SerialIdentityReady identity s) :
    Buffer s.mem identity 40 := by
  refine ⟨⟨40, 1#320⟩, h.present, by decide, ?_⟩
  simp [h.offsetZero]

theorem SerialIdentityReady.read (h : SerialIdentityReady identity s) :
    s.mem.readAt identity 320 = 1#320 :=
  Verifier.Execution.Dalek.identity_global_read s identity h.offsetZero h.present

/-- The 40-byte constant cannot alias any larger live scratch object. -/
theorem SerialIdentityReady.separate (h : SerialIdentityReady identity s)
    (hq : Buffer s.mem q bytes) (hbytes : 40 < bytes) : q.id ≠ identity.id := by
  intro heq
  obtain ⟨b, hb, _, hfit⟩ := hq
  rw [heq, h.present] at hb
  cases hb
  change q.offset.toNat + bytes ≤ 40 at hfit
  omega

theorem SerialIdentityReady.writesOnly (h : SerialIdentityReady identity s)
    (hf : WritesOnly out bytes s t)
    (hd : (Range.of identity 320).Disjoint (Range.of out (8*bytes))) :
    SerialIdentityReady identity t := by
  refine ⟨h.offsetZero, ?_⟩
  have hs := hf.allocationShape identity.id
  rw [h.present] at hs
  cases hb : t.mem[identity.id]? with
  | none => simp [hb] at hs
  | some b =>
      have hl : b.length = 40 := by simpa [hb, Verifier.Execution.identityOne] using hs
      cases b with
      | mk n value =>
          dsimp only at hl
          subst n
          have hr := hf.readFrame identity 320 hd
          have hv : t.mem.readAt identity 320 = value := by
            simp [MemoryState.readAt, hb, Pointer.offsetInBits, h.offsetZero]
          rw [h.read, hv] at hr
          subst value
          exact hb

end Agave.Ed25519.DoubleBase.RIR
