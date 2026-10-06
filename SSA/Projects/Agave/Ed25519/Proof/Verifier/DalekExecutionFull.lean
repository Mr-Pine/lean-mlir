import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionEntry
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionBody

/-! Entry-to-return composition for the actual extracted Dalek program. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

def entryTailPointers (initial : GlobalState) (key signature : Pointer) (g : Globals) : TailPointers :=
  ⟨stackSlot initial 5, stackSlot initial 6, stackSlot initial 12, key.add 32#64,
    stackSlot initial 7, signature, g.address1⟩

def entryPointPointers (initial : GlobalState) (g : Globals) : PointPointers :=
  ⟨stackSlot initial 8, stackSlot initial 9, stackSlot initial 10, stackSlot initial 11,
    stackSlot initial 2, stackSlot initial 1, g.address0⟩

theorem stackSlot_id_ne (initial : GlobalState) {i j : Nat} (hne : i ≠ j) :
    (stackSlot initial i).id ≠ (stackSlot initial j).id := by
  intro heq
  have he := congrArg BlockId.id heq
  simp only [stackSlot_id] at he
  omega

/-- The entry's emitted constants and allocations establish all body registers. -/
theorem entry_body_registers (E : Env program.Γ) (initial : GlobalState)
    (key signature : Pointer) (g : Globals) (small : Bool)
    (hsig : E.read (%arg1) = .value signature) :
    BodyRegisters (entryTailPointers initial key signature g) (entryPointPointers initial g)
      (stackSlot initial 0) (entryEnv E g initial key small) := by
  change E.args 1 = .value signature at hsig
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp [entryTailPointers, entryEnv, entryBaseEnv, mlir_env, hsig]
  · constructor <;> simp [entryPointPointers, entryEnv, entryBaseEnv, mlir_env]
  all_goals simp [entryEnv, entryBaseEnv, mlir_env]

/-- Fresh allocations discharge the body's internal nonalias conditions.
The two cache conditions are caller-visible read/write separation. -/
theorem entry_body_disjoint (initial : GlobalState) (hwf : initial.WF)
    (key signature : Pointer) (g : Globals)
    (hkey : SmallRange initial.mem (key.add 32#64) 160)
    (hsig : SmallRange initial.mem signature 64)
    (hone : SmallRange initial.mem g.address0 40)
    (hcache : SmallRange initial.mem g.address1 1)
    (hkeyCache : (Range.of (key.add 32#64) 1280).Disjoint (Range.of g.address1 8))
    (hsigCache : (Range.of signature 256).Disjoint (Range.of g.address1 8)) :
    BodyDisjoint (entryTailPointers initial key signature g) (entryPointPointers initial g)
      (stackSlot initial 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    all_goals simp only [entryPointPointers]
    all_goals first
      | exact stackSlot_id_ne initial (by decide)
      | exact (stackSlot_ne_caller initial hwf _ hone).symm
  · intro ptr hp dst hd
    simp [bodyReaders, entryTailPointers, entryPointPointers, pointDestinations] at hp hd
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact stackSlot_id_ne initial (by decide)
      | exact (stackSlot_ne_caller initial hwf _ hkey).symm
      | exact (stackSlot_ne_caller initial hwf _ hsig).symm
      | exact (stackSlot_ne_caller initial hwf _ hone).symm
  · exact stackSlot_ne_caller initial hwf 0 hsig
  · exact stackSlot_id_ne initial (by decide)
  · exact (stackSlot_ne_caller initial hwf 0 hkey).symm
  · exact (stackSlot_ne_caller initial hwf 7 hsig).symm
  · refine ⟨?_, hkeyCache, ?_, hsigCache⟩
    · exact stackSlot_disjoint_caller initial hwf 12 hcache 256 8
    · exact stackSlot_disjoint_caller initial hwf 7 hcache 256 8

/-- The entry's local primitive frames establish the complete body memory
invariant, including the challenge output and arbitrary original R/S bytes. -/
theorem entry_body_memory {Point Scalar Result : Type}
    (initial challenged multiplied compared : GlobalState) (hwf : initial.WF)
    (key signature : Pointer) (g : Globals) (layout : Layout Point Scalar Result)
    (h : Scalar) (a : Point) (r bytes : Bytes32)
    (hc : OutputFrame (allocated initial) challenged (stackSlot initial 12) 32)
    (hchallenge : ReadBytes challenged (stackSlot initial 12) 32 (layout.scalar h))
    (hm : OutputFrame challenged multiplied (stackSlot initial 4) 160)
    (he : ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared)
    (hkey : ReadBytes initial (key.add 32#64) 160 (layout.point a))
    (hsig : SmallRange initial.mem signature 64)
    (hr : ReadBytes initial signature 32 r)
    (hs : ReadBytes initial (signature.add 32#64) 32 bytes)
    (hone : ReadBytes initial g.address0 40 (1#320))
    (hcache : SmallRange initial.mem g.address1 1) :
    BodyMemory (entryTailPointers initial key signature g) (entryPointPointers initial g)
      (stackSlot initial 0) compared layout h a r bytes := by
  have hstack (i : Nat) (hi : i < 13) := entry_stack_live initial challenged multiplied compared
    hwf hc hm he i hi
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ (stackSlot_live initial hwf 3 13 (by decide)))
  have hcaller {ptr : Pointer} {n : Nat} {value : BitVec (8 * n)}
      (hv : ReadBytes initial ptr n value) : ReadBytes compared ptr n value := by
    apply entry_readBytes initial challenged multiplied compared hc hm he hid ptr n value
      (stackState_readBytes initial hwf 13 hv)
    · exact (stackSlot_disjoint_caller initial hwf 12 hv.1 256 (8 * n)).symm
    · exact (stackSlot_disjoint_caller initial hwf 4 hv.1 1280 (8 * n)).symm
    · exact (stackSlot_disjoint_caller initial hwf 3 hv.1 1280 (8 * n)).symm
  have hlive {ptr : Pointer} {n : Nat} (hv : SmallRange initial.mem ptr n) :
      SmallRange compared.mem ptr n := by
    apply he.live ptr n
    exact ((((hm.live ptr n (hc.live ptr n (stackState_live initial hwf 13 hv))).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _
  have hfidentity := identity_frame multiplied (stackSlot initial 3) hm.wellFormed hid
  have hchallengeFinal : ReadBytes compared (stackSlot initial 12) 32 (layout.scalar h) := by
    have hcm := OutputFrame.readBytes challenged multiplied (stackSlot initial 4) (stackSlot initial 12)
      160 32 (layout.scalar h) hm hchallenge (stackSlot_disjoint initial 12 4 (by decide) 256 1280)
    have hci := OutputFrame.readBytes multiplied (identityStoreState multiplied (stackSlot initial 3))
      (stackSlot initial 3) (stackSlot initial 12) 160 32 (layout.scalar h) hfidentity hcm
      (stackSlot_disjoint initial 12 3 (by decide) 256 1280)
    exact ReadOnlyFrame.readBytes _ _ _ _ _ he hci
  refine ⟨?_, hlive hsig, hcaller hs, ?_, hlive hcache, ?_, ?_, ?_, ?_, ?_, ?_, hcaller hone⟩
  · refine ⟨he.wellFormed, ?_, ?_, hchallengeFinal, hcaller hkey, ?_, hcaller hr,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hstack 5 (by decide)
    · exact hstack 6 (by decide)
    · exact hstack 7 (by decide)
    · exact stackSlot_disjoint initial 5 12 (by decide) 1280 256
    · exact stackSlot_disjoint_caller initial hwf 5 hkey.1 1280 1280
    · exact stackSlot_disjoint initial 5 7 (by decide) 1280 256
    · exact (stackSlot_disjoint_caller initial hwf 5 hr.1 1280 256).symm
    · exact stackSlot_disjoint initial 6 5 (by decide) 256 1280
    · exact (stackSlot_disjoint_caller initial hwf 6 hr.1 256 256).symm
    · exact stackSlot_disjoint initial 12 7 (by decide) 256 256
    · exact (stackSlot_disjoint_caller initial hwf 7 hkey.1 256 1280).symm
    · exact (stackSlot_disjoint_caller initial hwf 7 hr.1 256 256).symm
  all_goals first
    | exact hstack 0 (by decide)
    | exact hstack 8 (by decide)
    | exact hstack 9 (by decide)
    | exact hstack 10 (by decide)
    | exact hstack 11 (by decide)
    | exact hstack 2 (by decide)
    | exact hstack 1 (by decide)

/-- Full entry-to-return refinement for arbitrary signature and message bytes.
Every semantic premise is one named primitive contract. All remaining premises
are initial byte layout, live ranges, the fixed identity, and cache separation. -/
theorem program_from_entry_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : PrimitiveContracts p g layout shared doubleBase compress challenge)
    (hidentity : layout.identity = identityBytes)
    (E : Env program.Γ) (initial : GlobalState) (key signature message : Pointer)
    (a r bytes : Bytes32) (minusA : Point) (msg : List (BitVec 8))
    (hkeyE : E.read (%arg0) = .value key)
    (hsigE : E.read (%arg1) = .value signature)
    (hmsgE : E.read (%arg2) = .value message)
    (hlenE : E.read (%arg3) = .value (BitVec.ofNat 64 msg.length))
    (hwf : initial.WF) (hk : SmallRange initial.mem key 192)
    (hsig : SmallRange initial.mem signature 64)
    (hmsg : SmallRange initial.mem message msg.length)
    (ha : initial.mem.readAt key 256 = a)
    (hr : initial.mem.readAt signature 256 = r)
    (hs : initial.mem.readAt (signature.add 32#64) 256 = bytes)
    (hA : ReadBytes initial (key.add 32#64) 160 (layout.point minusA))
    (hmbytes : ∀ (i : Nat) (hi : i < msg.length),
      initial.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i])
    (hmlen : msg.length < 2^63)
    (hglobal : ReadBytes initial g.address0 40 (1#320))
    (hcache : SmallRange initial.mem g.address1 1)
    (hkeyCache : (Range.of (key.add 32#64) 1280).Disjoint (Range.of g.address1 8))
    (hsigCache : (Range.of signature 256).Disjoint (Range.of g.address1 8)) :
    ∃ after, (program p g).runFrom E 0 initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
  obtain ⟨challenged, multiplied, compared, hc, hchallenge, hm, he, hentry⟩ :=
    entry_of_contracts p g layout shared challenge contracts.challengeScalar contracts.pointMulByPow2
      contracts.pointConstantTimeEq hidentity E initial key signature message a r minusA msg
      hkeyE hsigE hmsgE hlenE hwf hk hsig hmsg ha hr hA hmbytes hmlen hglobal
  have hrbytes : ReadBytes initial signature 32 r :=
    ⟨by simpa only [Pointer.add_zero] using smallRange_add hsig (k := 0) (count := 32) (by decide), hr⟩
  have hsbytes : ReadBytes initial (signature.add 32#64) 32 bytes :=
    ⟨smallRange_add hsig (k := 32) (count := 32) (by decide), hs⟩
  by_cases hsmall : shared.smallOrder minusA = true
  · refine ⟨compared, ?_⟩
    rw [hentry, hsmall]
    have hret := return_block p g ((entryEnv E g initial key true)[%71 := .value 2#8])
      compared 2#8 (by simp [mlir_env])
    simpa [prehashed, hsmall, code] using hret
  · have hfalse : shared.smallOrder minusA = false := by
      cases h : shared.smallOrder minusA with
      | false => rfl
      | true => exact False.elim (hsmall h)
    have hregs := entry_body_registers E initial key signature g false hsigE
    have hmemory := entry_body_memory initial challenged multiplied compared hwf key signature g
      layout (challenge r a msg) minusA r bytes hc hchallenge hm he hA hsig hrbytes hsbytes hglobal hcache
    have hdisjoint := entry_body_disjoint initial hwf key signature g hA.1 hsig hglobal.1
      hcache hkeyCache hsigCache
    obtain ⟨after, hbody⟩ := body_of_contracts p g layout shared doubleBase compress challenge
      contracts hidentity (entryTailPointers initial key signature g) (entryPointPointers initial g)
      (stackSlot initial 0) rfl (entryEnv E g initial key false) compared (challenge r a msg)
      minusA r bytes hregs hmemory hdisjoint
    have hspec : prehashed shared doubleBase compress minusA r bytes (challenge r a msg) =
        bodySuffix shared doubleBase compress (challenge r a msg) minusA r bytes := by
      unfold prehashed bodySuffix scalarSuffix
      rw [hfalse]
      rfl
    refine ⟨after, ?_⟩
    rw [hentry, hfalse, hspec]
    exact hbody

def inputArgs (key signature message : Pointer) (length : Nat) :
    Vals [.ptr, .ptr, .ptr, .bv 64] :=
  .cons (.value key) (.cons (.value signature) (.cons (.value message)
    (.cons (.value (BitVec.ofNat 64 length)) .nil)))

/-- The public RIR `run` entry, with arbitrary encoded public key, R, S and
message bytes and an already constructed cached minus-A point. -/
theorem program_run_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : PrimitiveContracts p g layout shared doubleBase compress challenge)
    (hidentity : layout.identity = identityBytes)
    (initial : GlobalState) (key signature message : Pointer)
    (a r bytes : Bytes32) (minusA : Point) (msg : List (BitVec 8))
    (hwf : initial.WF) (hk : SmallRange initial.mem key 192)
    (hsig : SmallRange initial.mem signature 64)
    (hmsg : SmallRange initial.mem message msg.length)
    (ha : initial.mem.readAt key 256 = a)
    (hr : initial.mem.readAt signature 256 = r)
    (hs : initial.mem.readAt (signature.add 32#64) 256 = bytes)
    (hA : ReadBytes initial (key.add 32#64) 160 (layout.point minusA))
    (hmbytes : ∀ (i : Nat) (hi : i < msg.length),
      initial.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i])
    (hmlen : msg.length < 2^63)
    (hglobal : ReadBytes initial g.address0 40 (1#320))
    (hcache : SmallRange initial.mem g.address1 1)
    (hkeyCache : (Range.of (key.add 32#64) 1280).Disjoint (Range.of g.address1 8))
    (hsigCache : (Range.of signature 256).Disjoint (Range.of g.address1 8)) :
    ∃ after, (program p g).run (inputArgs key signature message msg.length) initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
  rw [Func.run_runFrom_eq]
  exact program_from_entry_of_contracts p g layout shared doubleBase compress challenge
    contracts hidentity _ initial key signature message a r bytes minusA msg
    rfl rfl rfl rfl hwf hk hsig hmsg ha hr hs hA hmbytes hmlen hglobal hcache hkeyCache hsigCache

/-- The callee entry also erases its actual stack frame. -/
theorem program_call_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : PrimitiveContracts p g layout shared doubleBase compress challenge)
    (hidentity : layout.identity = identityBytes)
    (initial : GlobalState) (key signature message : Pointer)
    (a r bytes : Bytes32) (minusA : Point) (msg : List (BitVec 8))
    (hwf : initial.WF) (hk : SmallRange initial.mem key 192)
    (hsig : SmallRange initial.mem signature 64)
    (hmsg : SmallRange initial.mem message msg.length)
    (ha : initial.mem.readAt key 256 = a)
    (hr : initial.mem.readAt signature 256 = r)
    (hs : initial.mem.readAt (signature.add 32#64) 256 = bytes)
    (hA : ReadBytes initial (key.add 32#64) 160 (layout.point minusA))
    (hmbytes : ∀ (i : Nat) (hi : i < msg.length),
      initial.mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i])
    (hmlen : msg.length < 2^63)
    (hglobal : ReadBytes initial g.address0 40 (1#320))
    (hcache : SmallRange initial.mem g.address1 1)
    (hkeyCache : (Range.of (key.add 32#64) 1280).Disjoint (Range.of g.address1 8))
    (hsigCache : (Range.of signature 256).Disjoint (Range.of g.address1 8)) :
    ∃ after, (program p g).call (inputArgs key signature message msg.length) initial =
      .value (.cons (.value (code (prehashed shared doubleBase compress minusA r bytes
        (challenge r a msg)))) .nil, after) := by
  obtain ⟨after, hrun⟩ := program_run_of_contracts p g layout shared doubleBase compress challenge
    contracts hidentity initial key signature message a r bytes minusA msg hwf hk hsig hmsg
    ha hr hs hA hmbytes hmlen hglobal hcache hkeyCache hsigCache
  exact ⟨_, Func.call_of_run hrun⟩

end Agave.Ed25519.Verifier.Execution.Dalek
