import SSA.Projects.RIR.Syntax.Elab
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionControl
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory

/-! Exact entry allocation and key small-order check of the imported verifier. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- Byte sizes of the thirteen stack allocations, in emitted order (%20..%32). -/
def stackBytes : Nat → Nat
  | 0 | 6 | 7 | 12 => 32
  | 8 => 168
  | 9 | 10 => 166
  | _ => 160

def stackState (s : GlobalState) : Nat → GlobalState
  | 0 => s
  | n + 1 => (stackState s n).alloca (stackBytes n)

def stackSlot (s : GlobalState) (n : Nat) : Pointer := (stackState s n).allocaPtr

def allocated (s : GlobalState) : GlobalState := stackState s 13

@[simp] theorem stackState_counter (s : GlobalState) (n : Nat) :
    (stackState s n).alloc.nextFreeBlock = s.alloc.nextFreeBlock + n := by
  induction n with
  | zero => simp [stackState]
  | succ n ih => simp [stackState, GlobalState.alloca, ih, Nat.add_assoc]

@[simp] theorem stackSlot_id (s : GlobalState) (n : Nat) :
    (stackSlot s n).id.id = s.alloc.nextFreeBlock + n := by
  simp [stackSlot, GlobalState.allocaPtr]

@[simp] theorem stackSlot_offset (s : GlobalState) (n : Nat) :
    (stackSlot s n).offset = 0 := rfl

theorem stackState_wf (s : GlobalState) (h : s.WF) (n : Nat) :
    (stackState s n).WF := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca

theorem smallRange_alloca (s : GlobalState) (h : s.WF) (hr : SmallRange s.mem q count)
    (bytes : Nat) : SmallRange (s.alloca bytes).mem q count := by
  obtain ⟨b, hb, hs, hrange⟩ := hr
  refine ⟨b, ?_, hs, hrange⟩
  rw [GlobalState.getElem?_alloca (GlobalState.ne_allocaPtr_of_fits h (SmallRange.fits ⟨b, hb, hs, hrange⟩))]
  exact hb

theorem stackState_live (s : GlobalState) (h : s.WF) (n : Nat)
    (hr : SmallRange s.mem q count) : SmallRange (stackState s n).mem q count := by
  induction n with
  | zero => exact hr
  | succ n ih => exact smallRange_alloca _ (stackState_wf s h n) ih _

theorem stackState_read (s : GlobalState) (h : s.WF) (n : Nat)
    (hr : SmallRange s.mem q count) (w : Nat) :
    (stackState s n).mem.readAt q w = s.mem.readAt q w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (MemoryState.readAt_alloca (stackState_wf s h n)
      (stackState_live s h n hr).fits).trans ih

theorem stackState_readBytes (s : GlobalState) (h : s.WF) (n : Nat)
    (hr : ReadBytes s q count value) : ReadBytes (stackState s n) q count value :=
  ⟨stackState_live s h n hr.1, (stackState_read s h n hr.1 _).trans hr.2⟩

theorem stackSlot_ne_caller (s : GlobalState) (h : s.WF) (n : Nat)
    (hr : SmallRange s.mem q count) : (stackSlot s n).id ≠ q.id := by
  intro heq
  have hq := h.lt hr.fits.mem
  have hid := congrArg BlockId.id heq
  simp only [stackSlot_id] at hid
  omega

/-- Fresh stack storage is disjoint from every live caller/global range. -/
theorem stackSlot_disjoint_caller (s : GlobalState) (h : s.WF) (i : Nat)
    (hr : SmallRange s.mem q count) (w v : Nat) :
    (Range.of (stackSlot s i) w).Disjoint (Range.of q v) :=
  Range.disjoint_of_id_ne (stackSlot_ne_caller s h i hr)

theorem stackSlot_disjoint (s : GlobalState) (i j : Nat) (hne : i ≠ j) (w v : Nat) :
    (Range.of (stackSlot s i) w).Disjoint (Range.of (stackSlot s j) v) := by
  apply Range.disjoint_of_id_ne
  intro heq
  have hid := congrArg BlockId.id heq
  simp only [stackSlot_id] at hid
  omega

theorem stackSlot_live (s : GlobalState) (h : s.WF) (i n : Nat) (hi : i < n) :
    SmallRange (stackState s n).mem (stackSlot s i) (stackBytes i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact smallRange_alloca _ (stackState_wf s h n) (ih hi) _
    · refine ⟨(⟨stackBytes i, 0⟩ : MemoryBlock), ?_, ?_, ?_⟩
      · simp [stackState, stackSlot, GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
      · change stackBytes i < 2^63; unfold stackBytes; split <;> norm_num
      · simp [stackSlot, GlobalState.allocaPtr]

/-- All thirteen emitted stack objects remain live across the entry's three
primitive calls and four identity stores, using only the primitives' frames. -/
theorem entry_stack_live (initial challenged multiplied compared : GlobalState)
    (hwf : initial.WF)
    (hc : OutputFrame (allocated initial) challenged (stackSlot initial 12) 32)
    (hm : OutputFrame challenged multiplied (stackSlot initial 4) 160)
    (he : ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared)
    (i : Nat) (hi : i < 13) :
    SmallRange compared.mem (stackSlot initial i) (stackBytes i) := by
  apply he.live
  exact ((((hm.live _ _ (hc.live _ _ (stackSlot_live initial hwf i 13 hi))).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

/-- Input bytes are preserved whenever their
range is disjoint from each entry output. No validity of those bytes is required. -/
theorem entry_readBytes (initial challenged multiplied compared : GlobalState)
    (hc : OutputFrame (allocated initial) challenged (stackSlot initial 12) 32)
    (hm : OutputFrame challenged multiplied (stackSlot initial 4) 160)
    (he : ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared)
    (hid : SmallRange multiplied.mem (stackSlot initial 3) 160)
    (q : Pointer) (count : Nat) (value : BitVec (8 * count))
    (hr : ReadBytes (allocated initial) q count value)
    (hdc : (Range.of q (8 * count)).Disjoint (Range.of (stackSlot initial 12) 256))
    (hdm : (Range.of q (8 * count)).Disjoint (Range.of (stackSlot initial 4) 1280))
    (hdi : (Range.of q (8 * count)).Disjoint (Range.of (stackSlot initial 3) 1280)) :
    ReadBytes compared q count value := by
  have h1 := hc.readBytes _ _ _ _ _ _ _ hr hdc
  have h2 := hm.readBytes _ _ _ _ _ _ _ h1 hdm
  have hf := identity_frame multiplied (stackSlot initial 3) hm.wellFormed hid
  exact he.readBytes _ _ _ _ _ (hf.readBytes _ _ _ _ _ _ _ h2 hdi)

/-- Register values after the constants and stack allocations. -/
def entryBaseEnv (E : Env program.Γ) (g : Globals) (s : GlobalState) : Env program.Γ :=
  E[%0 := .value 1, %1 := .value 32, %2 := .value 3, %3 := .value 0,
    %4 := .value 40, %5 := .value g.address0, %6 := .value 80, %7 := .value 120,
    %8 := .value 2, %9 := .value 8, %10 := .value 6, %11 := .value 160,
    %12 := .value 63, %13 := .value 255, %14 := .value 1, %15 := .value 33,
    %16 := .value 1, %17 := .value 31, %18 := .value g.address1, %19 := .value 0,
    %20 := .value (stackSlot s 0), %21 := .value (stackSlot s 1),
    %22 := .value (stackSlot s 2), %23 := .value (stackSlot s 3),
    %24 := .value (stackSlot s 4), %25 := .value (stackSlot s 5),
    %26 := .value (stackSlot s 6), %27 := .value (stackSlot s 7),
    %28 := .value (stackSlot s 8), %29 := .value (stackSlot s 9),
    %30 := .value (stackSlot s 10), %31 := .value (stackSlot s 11),
    %32 := .value (stackSlot s 12)]

def entryEnv (E : Env program.Γ) (g : Globals) (s : GlobalState) (key : Pointer)
    (small : Bool) : Env program.Γ :=
  (entryBaseEnv E g s)[%33 := .value (key.add 32),
    %34 := .value ((stackSlot s 3).add 40),
    %35 := .value ((stackSlot s 3).add 80),
    %36 := .value ((stackSlot s 3).add 120),
    %37 := .value (choiceByte small), %38 := .value (BitVec.ofBool (!small))]


private theorem modifyGet_run (f : GlobalState → α × GlobalState) (s : GlobalState) :
    (modifyGet f : EffectM α) s = .value (f s) := rfl

/-- Exact entry execution. The premises name only the three external primitive
calls and the live ranges used by the emitted identity initialization. -/
theorem entry_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (initial challenged multiplied compared : GlobalState)
    (key signature message : Pointer) (length : BitVec 64) (small : Bool)
    (hkey : E.read (%arg0) = .value key)
    (hsig : E.read (%arg1) = .value signature)
    (hmsg : E.read (%arg2) = .value message)
    (hlen : E.read (%arg3) = .value length)
    (hchallenge : p.challengeScalar
      (.cons (.value (stackSlot initial 12)) (.cons (.value key) (.cons (.value signature)
        (.cons (.value message) (.cons (.value length) .nil))))) (allocated initial) =
      .value (.nil, challenged))
    (hkeyRange : SmallRange challenged.mem key 192)
    (hmul : p.pointMulByPow2 (.cons (.value (stackSlot initial 4))
      (.cons (.value (key.add 32)) (.cons (.value 3) .nil))) challenged =
        .value (.nil, multiplied))
    (hidRange : SmallRange multiplied.mem (stackSlot initial 3) 160)
    (hglobal : ReadBytes multiplied g.address0 40 (1#320))
    (hdis : (Range.of g.address0 320).Disjoint (Range.of (stackSlot initial 3) 1280))
    (heq : p.pointConstantTimeEq (args2 (stackSlot initial 4) (stackSlot initial 3))
      (identityStoreState multiplied (stackSlot initial 3)) =
        .value (.cons (.value (choiceByte small)) .nil, compared)) :
    (program p g).runFrom E 0 initial =
      if small then (program p g).runFrom ((entryEnv E g initial key small)[%71 := .value 2]) 13 compared
      else (program p g).runFrom (entryEnv E g initial key small) 1 compared := by
  change E.args 0 = .value key at hkey
  change E.args 1 = .value signature at hsig
  change E.args 2 = .value message at hmsg
  change E.args 3 = .value length at hlen
  let dst := stackSlot initial 3
  have hgkey := hkeyRange.gep (k := 32) (by decide)
  have hg40 := (hidRange.storeAt dst (0#320)).gep (k := 40) (by decide)
  have hg80 := ((hidRange.storeAt dst (0#320)).storeAt (dst.add 40) (1#320)).gep (k := 80) (by decide)
  have hg120 := (((hidRange.storeAt dst (0#320)).storeAt (dst.add 40) (1#320)).storeAt (dst.add 80) (1#320)).gep (k := 120) (by decide)
  change Operation.gepInboundsLive challenged.mem (.value key) [.value (32 : Int)] =
    .value (key.add 32#64) at hgkey
  change Operation.gepInboundsLive (multiplied.mem.storeAt dst (0#320))
    (.value dst) [.value (40 : Int)] = .value (dst.add 40#64) at hg40
  change Operation.gepInboundsLive ((multiplied.mem.storeAt dst (0#320)).storeAt (dst.add 40#64) (1#320))
    (.value dst) [.value (80 : Int)] = .value (dst.add 80#64) at hg80
  change Operation.gepInboundsLive (((multiplied.mem.storeAt dst (0#320)).storeAt (dst.add 40#64) (1#320)).storeAt (dst.add 80#64) (1#320))
    (.value dst) [.value (120 : Int)] = .value (dst.add 120#64) at hg120
  have hf0 := hidRange.fits_add (k := 0) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hf0
  have hf40 := (hidRange.storeAt dst (0#320)).fits_add (k := 40) (count := 40) (by decide)
  have hf80 := ((hidRange.storeAt dst (0#320)).storeAt (dst.add 40) (1#320)).fits_add (k := 80) (count := 40) (by decide)
  have hf120 := (((hidRange.storeAt dst (0#320)).storeAt (dst.add 40) (1#320)).storeAt (dst.add 80) (1#320)).fits_add (k := 120) (count := 40) (by decide)
  have hd0 := disjoint_add_subrange hidRange hdis (k := 0) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hd0
  have hd40 := disjoint_add_subrange hidRange hdis (k := 40) (count := 40) (by decide)
  have hd80 := disjoint_add_subrange hidRange hdis (k := 80) (count := 40) (by decide)
  have hg0 := hglobal.1.fits.storeAt (q := dst) (x := 0#320)
  have hg1 := hg0.storeAt (q := dst.add 40) (x := 1#320)
  have hr0 : (multiplied.mem.storeAt dst (0#320)).readAt g.address0 320 = 1#320 :=
    (MemoryState.readAt_storeAt_disjoint hd0.symm _).trans hglobal.2
  have hr1 : ((multiplied.mem.storeAt dst (0#320)).storeAt (dst.add 40) (1#320)).readAt g.address0 320 = 1#320 :=
    (MemoryState.readAt_storeAt_disjoint hd40.symm _).trans hr0
  dsimp only [args2, identityStoreState] at heq
  simp [dst, allocated, stackSlot, stackState, stackBytes] at hchallenge hmul heq hg40 hg80 hg120 hf0 hf40 hf80 hf120 hg0 hg1 hr0 hr1 hd40 hd80
  have hb : (program.bb0 p g).run program.blockParams E initial =
      .value ((if small then (entryEnv E g initial key small)[%71 := .value 2]
        else entryEnv E g initial key small, .inr (if small then 13 else 1)), compared) := by
    cases small <;>
      simp [BasicBlock.run, program.bb0, entryEnv, entryBaseEnv,
        List.foldlM_cons, List.foldlM_nil, Instr.run, run_alloca, modifyGet_run, Ty.wrap,
        EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
        Operation.memset, Operation.memcpy, BinOp.compute, Operation.icmp,
        Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
        Env.writeMany_cons, Env.writeMany_nil,
        GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
        hkey, hsig, hmsg, hlen, hchallenge, hmul, heq,
        hgkey, hg40, hg80, hg120, hf0, hf40, hf80, hf120,
        hg0, hg1, hr0, hr1, hd40.symm, hd80.symm, choiceByte,
        throwUBIf, ofBool_eq_one_iff, dst,
        allocated, stackSlot, stackState, stackBytes]
  rw [Func.runFrom_eq, block_0, hb]
  cases small <;> rfl


/-- Derive the entry's three primitive invocations from their local contracts.
The returned frames expose all memory transport needed by the remaining CFG. -/
theorem entry_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (hchallenge : ChallengeContract p.challengeScalar layout challenge)
    (hmul : CofactorContract p.pointMulByPow2 layout)
    (heq : SmallOrderEqContract p.pointConstantTimeEq layout shared)
    (hidLayout : layout.identity = identityBytes)
    (E : Env program.Γ) (initial : GlobalState) (key signature message : Pointer)
    (a r : Bytes32) (A : Point) (msg : List (BitVec 8))
    (hkeyE : E.read (%arg0) = .value key)
    (hsigE : E.read (%arg1) = .value signature)
    (hmsgE : E.read (%arg2) = .value message)
    (hlenE : E.read (%arg3) = .value (BitVec.ofNat 64 msg.length))
    (hwf : initial.WF) (hk : SmallRange initial.mem key 192)
    (hsig : SmallRange initial.mem signature 64)
    (hmsg : SmallRange initial.mem message msg.length)
    (ha : initial.mem.readAt key 256 = a)
    (hr : initial.mem.readAt signature 256 = r)
    (hA : ReadBytes initial (key.add 32) 160 (layout.point A))
    (hmbytes : ∀ (i : Nat) (hi : i < msg.length),
      initial.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i])
    (hmlen : msg.length < 2^63)
    (hglobal : ReadBytes initial g.address0 40 (1#320)) :
    ∃ challenged multiplied compared,
      OutputFrame (allocated initial) challenged (stackSlot initial 12) 32 ∧
      ReadBytes challenged (stackSlot initial 12) 32 (layout.scalar (challenge r a msg)) ∧
      OutputFrame challenged multiplied (stackSlot initial 4) 160 ∧
      ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared ∧
      (program p g).runFrom E 0 initial =
        if shared.smallOrder A then
          (program p g).runFrom ((entryEnv E g initial key (shared.smallOrder A))[%71 := .value 2]) 13 compared
        else (program p g).runFrom (entryEnv E g initial key (shared.smallOrder A)) 1 compared := by
  have hwf0 : (allocated initial).WF := stackState_wf initial hwf 13
  have hk0 := stackState_live initial hwf 13 hk
  have hs0 := stackState_live initial hwf 13 hsig
  have hm0 := stackState_live initial hwf 13 hmsg
  have hA0 := stackState_readBytes initial hwf 13 hA
  have hg0 := stackState_readBytes initial hwf 13 hglobal
  have hstack (i : Nat) (hi : i < 13) := stackSlot_live initial hwf i 13 hi
  have hbytes : ∀ (i : Nat) (hi : i < msg.length),
      (allocated initial).mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i] := by
    intro i hi
    exact (stackState_read initial hwf 13
      (smallRange_add hmsg (k := i) (count := 1) (by omega)) 8).trans (hmbytes i hi)
  obtain ⟨challenged, hccall, hc, hchallengeRead⟩ := hchallenge (stackSlot initial 12)
    key signature message (allocated initial) a r msg hwf0 (hstack 12 (by decide)) hk0 hs0 hm0
    ((stackState_read initial hwf 13 hk 256).trans ha)
    ((stackState_read initial hwf 13 hsig 256).trans hr) hbytes hmlen
    (stackSlot_disjoint_caller initial hwf 12 hk 256 1536)
    (stackSlot_disjoint_caller initial hwf 12 hsig 256 512)
    (stackSlot_disjoint_caller initial hwf 12 hmsg 256 (8 * msg.length))
  have hAc : ReadBytes challenged (key.add 32) 160 (layout.point A) :=
    hc.readBytes _ _ _ _ _ _ _ hA0
      (stackSlot_disjoint_caller initial hwf 12 hA.1 256 1280).symm
  have hgc : ReadBytes challenged g.address0 40 (1#320) :=
    hc.readBytes _ _ _ _ _ _ _ hg0
      (stackSlot_disjoint_caller initial hwf 12 hglobal.1 256 320).symm
  obtain ⟨multiplied, hmcall, hm, hcofactor⟩ := hmul (stackSlot initial 4) (key.add 32)
    challenged A hc.wellFormed (hc.live _ _ (hstack 4 (by decide))) hAc
    (stackSlot_disjoint_caller initial hwf 4 hA.1 1280 1280)
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ (hstack 3 (by decide)))
  have hgm : ReadBytes multiplied g.address0 40 (1#320) :=
    hm.readBytes _ _ _ _ _ _ _ hgc
      (stackSlot_disjoint_caller initial hwf 4 hglobal.1 1280 320).symm
  have hiFrame := identity_frame multiplied (stackSlot initial 3) hm.wellFormed hid
  have hcofactor' := hiFrame.readBytes _ _ _ _ _ _ _ hcofactor
    (stackSlot_disjoint initial 4 3 (by decide) 1280 1280)
  have hidentity : ReadBytes (identityStoreState multiplied (stackSlot initial 3))
      (stackSlot initial 3) 160 layout.identity := by
    rw [hidLayout]
    exact identity_readback multiplied (stackSlot initial 3) hid
  obtain ⟨compared, hecall, he⟩ := heq (stackSlot initial 4) (stackSlot initial 3)
    (identityStoreState multiplied (stackSlot initial 3)) A hiFrame.wellFormed
    hcofactor' hidentity
  refine ⟨challenged, multiplied, compared, hc, hchallengeRead, hm, he, ?_⟩
  exact entry_block p g E initial challenged multiplied compared key signature message
    (BitVec.ofNat 64 msg.length) (shared.smallOrder A) hkeyE hsigE hmsgE hlenE hccall
    (hc.live _ _ hk0) hmcall hid hgm
    (stackSlot_disjoint_caller initial hwf 3 hglobal.1 1280 320).symm hecall

end Agave.Ed25519.Verifier.Execution.Dalek
