import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreMemory
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.RingSchedule
import SSA.Projects.Agave.Ed25519.Proof.SHA512.InputByteOrder
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.EntryTail

/-! Byte observations and private-ring invariants for the imported SLLVM core.
Only concrete block bytes and splice operations occur in these premises. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Bridge.FiredancerSHAExecution.Core (Ring ringWord ringStep initialRing)
open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

variable {m : MemoryState} {p q : Pointer} {bytes k w w' : Nat}

theorem ring_offset (h : SmallRange m p bytes) (hk : k ≤ bytes) :
    (p.withOffset (BitVec.ofNat 64 k)).offsetInBits = p.offsetInBits + 8*k := by
  have hb := h.offset_lt
  have hk64 : k < 2^64 := by omega
  have hsum : p.offset.toNat + k < 2^64 := by omega
  simp only [Pointer.offsetInBits, Pointer.withOffset, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hsum, Nat.mul_add]

theorem readBits_splice_self (x : BitVec w) (h : Fits m p w) :
    readBits (m.splice p x) p w = x := by
  simp only [readBits, readWord?_splice_self x h, Option.getD_some]

theorem readBits_splice_ne (x : BitVec w') (h : q.id ≠ p.id) :
    readBits (m.splice q x) p w = readBits m p w :=
  readBits_of_live_eq (live?_splice_ne h)

theorem readBits_splice_disjoint (x : BitVec w')
    (h : q.id ≠ p.id ∨ p.offsetInBits + w ≤ q.offsetInBits ∨
      q.offsetInBits + w' ≤ p.offsetInBits) :
    readBits (m.splice q x) p w = readBits m p w := by
  by_cases he : q.id = p.id
  · rcases h with hn | hd
    · exact False.elim (hn he)
    cases hb : m.live? p.id with
    | none =>
      simp only [readBits, readWord?, live?_splice_eq_none hb, hb, Option.bind_none, Option.getD_none]
    | some b =>
      have hq : m.live? q.id = some b := he.symm ▸ hb
      have hsp := splicedLive m q b hq x
      rw [he] at hsp
      simp only [readBits, readWord?, hsp, hb, Option.bind_some, Option.pure_def,
        Option.getD_some]
      exact extractLsb'_spliceBits_of_disjoint _ _ _ _ hd
  · exact readBits_splice_ne x he

theorem readBits_ring_splice_other (h : SmallRange m p 128) (i j : Nat)
    (hi : i < 16) (hj : j < 16) (hne : i ≠ j) (x : Word) :
    readBits (m.splice (p.withOffset (BitVec.ofNat 64 (8*i))) x)
      (p.withOffset (BitVec.ofNat 64 (8*j))) 64 =
      readBits m (p.withOffset (BitVec.ofNat 64 (8*j))) 64 := by
  apply readBits_splice_disjoint
  rw [ring_offset h (k := 8*i) (by omega), ring_offset h (k := 8*j) (by omega)]
  exact Or.inr (by omega)

def inputMemory (m : MemoryState) (stack : Pointer) (r : Nat) (native : Word) : MemoryState :=
  m.splice (stack.withOffset (BitVec.ofNat 64 (8*r))) (swapBytes native)

def scheduleMemory (m : MemoryState) (stack : Pointer) (q : Ring) (r : Nat) : MemoryState :=
  m.splice (stack.withOffset (BitVec.ofNat 64 (8*(r%16)))) (ringWord q r)

def InitialRingMemory (m : MemoryState) (stack : Pointer) (block : Bytes) (r : Nat) : Prop :=
  ∀ j, j < r → readBits m (stack.withOffset (BitVec.ofNat 64 (8*j))) 64 = readWordBE block j

theorem initialRingMemory_zero (m : MemoryState) (stack : Pointer) (block : Bytes) :
    InitialRingMemory m stack block 0 := by
  intro j hj
  omega

theorem inputMemory_initial_step (m : MemoryState) (stack : Pointer) (block : Bytes)
    (r : Nat) (native : Word) (hr : r < 16) (hs : SmallRange m stack 128)
    (h : InitialRingMemory m stack block r) (hword : swapBytes native = readWordBE block r) :
    InitialRingMemory (inputMemory m stack r native) stack block (r+1) := by
  intro j hj
  by_cases he : j = r
  · subst j
    rw [inputMemory, readBits_splice_self _ (hs.add (k := 8*r) (n := 8) (by omega)).fits, hword]
  · rw [inputMemory, readBits_ring_splice_other hs r j hr (by omega) (Ne.symm he)]
    exact h j (by omega)

theorem initialRingMemory_full (m : MemoryState) (stack : Pointer) (block : Bytes)
    (h : InitialRingMemory m stack block 16) :
    ∀ j, j < 16 → readBits m (stack.withOffset (BitVec.ofNat 64 (8*j))) 64 = initialRing block j := h

structure LaterMemory (m : MemoryState) (stack kp : Pointer) (q : Ring) : Prop where
  liveStack : SmallRange m stack 128
  liveConstants : SmallRange m kp 640
  distinct : stack.id ≠ kp.id
  ring : ∀ j, j < 16 → readBits m (stack.withOffset (BitVec.ofNat 64 (8*j))) 64 = q j
  table : ∀ j, j < 80 → readBits m (kp.withOffset (BitVec.ofNat 64 (8*j))) 64 = Spec.constants.toList.getD j 0

theorem scheduleMemory_read (m : MemoryState) (stack : Pointer) (q : Ring) (r j : Nat)
    (hs : SmallRange m stack 128) (hj : j < 16)
    (hread : readBits m (stack.withOffset (BitVec.ofNat 64 (8*j))) 64 = q j) :
    readBits (scheduleMemory m stack q r) (stack.withOffset (BitVec.ofNat 64 (8*j))) 64 =
      ringStep q r j := by
  by_cases he : j = r%16
  · subst j
    rw [scheduleMemory, readBits_splice_self _ (hs.add (k := 8*(r%16)) (n := 8) (by omega)).fits]
    simp only [ringStep, ite_true]
  · rw [scheduleMemory, readBits_ring_splice_other hs (r%16) j (by omega) hj (Ne.symm he), hread]
    simp only [ringStep, ite_eq_right he]

theorem LaterMemory.step {m : MemoryState} {stack kp : Pointer} {q : Ring}
    (h : LaterMemory m stack kp q) (r : Nat) :
    LaterMemory (scheduleMemory m stack q r) stack kp (ringStep q r) := by
  refine ⟨h.liveStack.splice _ _, h.liveConstants.splice _ _, h.distinct, ?_, ?_⟩
  · intro j hj
    exact scheduleMemory_read m stack q r j h.liveStack hj (h.ring j hj)
  · intro j hj
    rw [scheduleMemory, readBits_splice_ne (p := kp.withOffset (BitVec.ofNat 64 (8*j)))
      (q := stack.withOffset (BitVec.ofNat 64 (8*(r%16)))) _ h.distinct]
    exact h.table j hj

theorem readBytes_splice_ne (x : BitVec w') (h : q.id ≠ p.id) (n : Nat) :
    readBytes (m.splice q x) p n = readBytes m p n := by
  rw [readBytes, readBits_splice_ne x h]
  rfl

theorem inputMemory_preserves_data (m : MemoryState) (stack data : Pointer)
    (r : Nat) (native : Word) (hne : stack.id ≠ data.id) :
    readBytes (inputMemory m stack r native) data 128 = readBytes m data 128 := by
  unfold inputMemory
  apply readBytes_splice_ne
  exact hne

private theorem readWordNative_bytesOf (v : BitVec 1024) (i : Nat) (hi : i < 16) :
    readWordNative (Firedancer.Common.bytesOf (n := 128) v) i = v.extractLsb' (64*i) 64 := by
  simp only [readWordNative, Firedancer.Common.bytesOf]
  have h0 : 8*i < 128 := by omega
  have h1 : 8*i+1 < 128 := by omega
  have h2 : 8*i+2 < 128 := by omega
  have h3 : 8*i+3 < 128 := by omega
  have h4 : 8*i+4 < 128 := by omega
  have h5 : 8*i+5 < 128 := by omega
  have h6 : 8*i+6 < 128 := by omega
  have h7 : 8*i+7 < 128 := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h0, h1, h2, h3, h4,
    h5, h6, h7, dite_eq_left, Option.getD_some]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  grind

theorem input_readWordNative (m : MemoryState) (data : Pointer) (r : Nat)
    (hd : SmallRange m data 128) (hr : r < 16) :
    readBits m (data.withOffset (BitVec.ofNat 64 (8*r))) 64 =
      readWordNative (readBytes m data 128) r := by
  rw [readBytes, readWordNative_bytesOf _ r hr]
  have hoff := ring_offset hd (k := 8*r) (by omega)
  obtain ⟨b, hb, _, _⟩ := hd
  simp only [readBits, readWord?, Pointer.withOffset, hb, Option.bind_some,
    Option.pure_def, Option.getD_some]
  change b.bytes.extractLsb' (data.withOffset (BitVec.ofNat 64 (8*r))).offsetInBits 64 =
    (b.bytes.extractLsb' data.offsetInBits 1024).extractLsb' (64*r) 64
  rw [hoff, BitVec.extractLsb'_extractLsb'_add_of_le (by omega)]
  congr 1
  omega

theorem input_swap_eq (m : MemoryState) (data : Pointer) (r : Nat)
    (hd : SmallRange m data 128) (hr : r < 16) :
    swapBytes (readBits m (data.withOffset (BitVec.ofNat 64 (8*r))) 64) =
      readWordBE (readBytes m data 128) r := by
  rw [input_readWordNative m data r hd hr]
  have h := bswap_native_readWordBE (readBytes m data 128) r
  change LeanMLIR.RIR.PoisonOr.value (swapBytes (readWordNative (readBytes m data 128) r)) =
    LeanMLIR.RIR.PoisonOr.value (readWordBE (readBytes m data 128) r) at h
  exact LeanMLIR.RIR.PoisonOr.value_inj.mp h

/-- Subword observations come from the same underlying block bytes. -/
theorem readBits_add_extract (m : MemoryState) (p : Pointer) (bytes k w : Nat)
    (h : SmallRange m p bytes) (hk : k ≤ bytes) (hw : 8*k+w ≤ bytes*8) :
    readBits m (p.withOffset (BitVec.ofNat 64 k)) w =
      (readBits m p (bytes*8)).extractLsb' (8*k) w := by
  have hoff := ring_offset h hk
  obtain ⟨b, hb, _, _⟩ := h
  simp only [readBits, readWord?, Pointer.withOffset, hb, Option.pure_def]
  change b.bytes.extractLsb' (p.withOffset (BitVec.ofNat 64 k)).offsetInBits w =
    (b.bytes.extractLsb' p.offsetInBits (bytes*8)).extractLsb' (8*k) w
  rw [hoff, BitVec.extractLsb'_extractLsb'_add_of_le hw]

theorem constants_word (m : MemoryState) (kp : Pointer)
    (hk : SmallRange m kp 640) (hv : readBits m kp 5120 = constantsBytes)
    (r : Nat) (hr : r < 80) :
    readBits m (kp.withOffset (BitVec.ofNat 64 (8*r))) 64 =
      Spec.constants.toList.getD r 0 := by
  rw [readBits_add_extract m kp 640 (8*r) 64 hk (by omega) (by omega)]
  change (readBits m kp 5120).extractLsb' (8*(8*r)) 64 = _
  rw [hv, constants_eq_standard, show 8*(8*r) = r*64 by omega,
    BitVec.extractLsb'_packLanes Spec.constants r hr]
  simp [Vector.getElem?_eq_getElem hr]

/-- A compositional frame for the two loops' private stack writes. -/
inductive RingWrites (stack : Pointer) : GlobalState → GlobalState → Prop
  | refl (state) : RingWrites stack state state
  | step {before middle} (h : RingWrites stack before middle) (q : Ring) (r : Nat) :
      RingWrites stack before {middle with mem := scheduleMemory middle.mem stack q r}
  | input {before middle} (h : RingWrites stack before middle) (r : Nat) (native : Word) :
      RingWrites stack before {middle with mem := inputMemory middle.mem stack r native}

theorem RingWrites.trans {stack : Pointer} {a b c : GlobalState}
    (hab : RingWrites stack a b) (hbc : RingWrites stack b c) : RingWrites stack a c := by
  induction hbc with
  | refl => exact hab
  | step h q r ih => exact .step ih q r
  | input h r native ih => exact .input ih r native

theorem RingWrites.live {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) (id : BlockId) (hne : stack.id ≠ id) :
    b.mem.live? id = a.mem.live? id := by
  induction h with
  | refl => rfl
  | step h q r ih =>
    exact (live?_splice_ne (p := stack.withOffset (BitVec.ofNat 64 (8*(r%16)))) hne).trans ih
  | input h r native ih =>
    exact (live?_splice_ne (p := stack.withOffset (BitVec.ofNat 64 (8*r))) hne).trans ih

theorem RingWrites.readBits {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) (p : Pointer) (bits : Nat) (hne : stack.id ≠ p.id) :
    readBits b.mem p bits = readBits a.mem p bits :=
  readBits_of_live_eq (h.live p.id hne)

theorem RingWrites.readBytes {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) (p : Pointer) (bytes : Nat) (hne : stack.id ≠ p.id) :
    readBytes b.mem p bytes = readBytes a.mem p bytes := by
  unfold Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.readBytes
  rw [h.readBits p (bytes*8) hne]

theorem RingWrites.smallRange {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) (p : Pointer) (bytes : Nat) (hp : SmallRange a.mem p bytes) :
    SmallRange b.mem p bytes := by
  induction h with
  | refl => exact hp
  | step h q r ih => exact ih.splice _ _
  | input h r native ih => exact ih.splice _ _

theorem RingWrites.alloc {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) : b.alloc = a.alloc := by
  induction h with
  | refl => rfl
  | step h q r ih => exact ih
  | input h r native ih => exact ih

theorem RingWrites.globals {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) : b.globals = a.globals := by
  induction h with
  | refl => rfl
  | step h q r ih => exact ih
  | input h r native ih => exact ih

theorem RingWrites.wf {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) (ha : a.WF) : b.WF := by
  induction h with
  | refl => exact ha
  | step h q r ih => exact ih.splice
  | input h r native ih => exact ih.splice

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
