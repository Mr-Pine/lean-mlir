import SSA.Projects.Agave.Ed25519.Bridge.FiredancerBaseTableCertificates
import SSA.Projects.Firedancer.Ref.Proof.Point

/-! The source-byte loader boundary for the Firedancer reference base table.
The hypothesis below describes only a named initialized allocation. Every
entry bound and mathematical table value is derived from its pinned bytes. -/
namespace Agave.Ed25519.Bridge.FiredancerBaseInitializer
open LeanMLIR SLLVM Firedancer Firedancer.Ref

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual scalar initializer data in one zero-offset global allocation. -/
structure Loaded (state : GlobalState) (q : Pointer) : Prop where
  address : GlobalPtr state symbol q
  offset : q.offset = 0#64
  contents : state.mem.live? q.id = some ⟨20480, bytes⟩

def entryPtr (q : Pointer) (k : Fin 128) : Pointer :=
  q.withOffset (BitVec.ofNat 64 (160*k.val))

private theorem entry_offset (q : Pointer) (hz : q.offset = 0#64) (k : Fin 128) :
    (entryPtr q k).offset.toNat = 160*k.val := by
  have hk := k.isLt
  simp only [entryPtr, Pointer.withOffset, hz, BitVec.zero_add, BitVec.toNat_ofNat]
  omega

private theorem coordinate_offset (q : Pointer) (hz : q.offset = 0#64)
    (k : Fin 128) (c : Fin 4) :
    ((entryPtr q k).withOffset (c * (5 * 8))).offset.toNat = 160*k.val + 40*c.val := by
  have hk := k.isLt
  fin_cases c <;>
    simp [entryPtr, Pointer.withOffset, hz, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

theorem Loaded.pointPtr (h : Loaded state q) (k : Fin 128) :
    IsPointPtr state.mem (entryPtr q k) := by
  have hk := k.isLt
  refine ⟨⟨⟨20480, bytes⟩, getElem?_of_live? h.contents, ?_⟩, ?_⟩
  · simp only [Pointer.offsetInBits, entry_offset q h.offset k, LiveBlock.lengthInBits]
    omega
  · rw [entry_offset q h.offset k]
    omega

theorem Loaded.readLimb_exact (h : Loaded state q) (k : Fin 128) (c : Fin 4) (i : Fin 5) :
    readLimb? ((entryPtr q k).withOffset (c * (5 * 8))) i state.mem = some (limb k c i) := by
  have hoff : ((entryPtr q k).withOffset (c * (5 * 8))).offsetInBits + 64*i.val =
      64*(20*k.val + 5*c.val + i.val) := by
    rw [Pointer.offsetInBits, coordinate_offset q h.offset k c]
    omega
  unfold readLimb?
  rw [show ((entryPtr q k).withOffset (c * (5 * 8))).id = q.id from rfl, h.contents]
  change some ((bytes.extractLsb'
    (((entryPtr q k).withOffset (c * (5 * 8))).offsetInBits + 64*i.val) 64).toNat) = _
  rw [hoff]
  rfl

theorem Loaded.limbBounds (h : Loaded state q) (k : Fin 128) :
    ∀ c, LimbBounds.Loose (isCoordPtr (h.pointPtr k) c) := by
  intro c i
  simpa only [readLimb, h.readLimb_exact k c i, Option.get_some] using limb_bounds k c i

theorem Loaded.readPoint (h : Loaded state q) (k : Fin 128) :
    _root_.Ed25519.PrecomputedPoint.ofSlots (readPoint (h.pointPtr k)) = cache k := by
  have hc (c : Fin 4) : readCoordinate? (entryPtr q k) c state.mem = some (coordinate k c) := by
    simp only [readCoordinate?, readFieldElem?, h.readLimb_exact,
      Option.pure_def, coordinate, decodeFieldElem]
    rfl
  rw [readPoint_eq (h.pointPtr k) hc]
  rfl

/-- A physical source initializer entails the existing table contract, with
no per-entry semantic table hypothesis. -/
theorem Loaded.baseTableHolds (h : Loaded state q) :
    BaseTableHolds state firedancerBaseTable := by
  apply firedancerBaseTable_holds_of_entries state q h.address
  intro k hk
  let i : Fin 128 := ⟨k, hk⟩
  exact ⟨h.pointPtr i, h.limbBounds i, (h.readPoint i).trans (cache_eq_mathematical i)⟩

/-- The memory model's initializer installs exactly the pinned source bytes. -/
def initialized (state : GlobalState) : GlobalState := state.withGlobal symbol bytes

def initializerPtr (state : GlobalState) : Pointer := ⟨⟨state.alloc.nextFreeBlock⟩, 0#64⟩

private theorem splice_full (v : BitVec n) : spliceBits (0#n) 0 v = v := by
  simp [spliceBits]

theorem initialize_loaded (state : GlobalState) : Loaded (initialized state) (initializerPtr state) := by
  refine ⟨GlobalState.withGlobal_ptr state symbol bytes, rfl, ?_⟩
  have ha : (state.afterAlloca 163840).mem.live? (initializerPtr state).id =
      some (⟨20480, 0#163840⟩ : LiveBlock) := live?_afterAlloca_self state 163840
  have hs := splicedLive (state.afterAlloca 163840).mem (initializerPtr state)
    (⟨20480, 0#163840⟩ : LiveBlock) ha bytes
  change ((state.afterAlloca 163840).mem.splice (initializerPtr state) bytes).live?
    (initializerPtr state).id = some ⟨20480, spliceBits (0#163840) 0 bytes⟩ at hs
  rw [splice_full] at hs
  exact hs

theorem initialize_baseTableHolds (state : GlobalState) :
    BaseTableHolds (initialized state) firedancerBaseTable :=
  (initialize_loaded state).baseTableHolds

theorem initialize_wf (state : GlobalState) (hwf : state.WF) : (initialized state).WF :=
  hwf.withGlobal symbol bytes

/-- Replace the former mathematical table assumption by actual initialized
source data. The unrelated curve and SHA global obligations remain explicit. -/
theorem globalsReady_of_loaded (state : GlobalState) (kbits : BitVec (80*64))
    (href : state.RefWF [])
    (hsha : ∃ p, HoldsGlobal state "fd_sha512_core_ref.K" p kbits)
    (q : Pointer) (hload : Loaded state q) : FiredancerGlobalsReady state kbits :=
  ⟨href, hsha, hload.baseTableHolds⟩

end Agave.Ed25519.Bridge.FiredancerBaseInitializer
