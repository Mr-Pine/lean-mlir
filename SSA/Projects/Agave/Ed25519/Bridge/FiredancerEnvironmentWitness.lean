import SSA.Projects.Agave.Ed25519.Bridge.FiredancerFieldInitializer
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReachableRawLoaded
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.InitializerData

/-! A simultaneous raw-memory witness. This is a mathematical loader layout,
not an assertion that a C/LLVM initialization routine has executed. Caller
contents are arbitrary; the only restriction is the message allocation size. -/
namespace Agave.Ed25519.Bridge.FiredancerEnvironmentWitness
open LeanMLIR SLLVM Firedancer Firedancer.Common

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def ptr (n : Nat) : Pointer := ⟨⟨n⟩, 0⟩

def initial {n : Nat} (message : BitVec (8*n)) (signature : BitVec 512)
    (publicKey : BitVec 256) : GlobalState :=
  { alloc := ⟨13⟩,
    «globals» := (∅ : Std.HashMap String Pointer) |>.insert "fd_f25519_d" (ptr 1)
       |>.insert "fd_f25519_one" (ptr 2)
       |>.insert "fd_f25519_sqrtm1" (ptr 3)
       |>.insert "fd_ed25519_order8_point_y0" (ptr 4)
       |>.insert "fd_ed25519_order8_point_y1" (ptr 5)
       |>.insert "fd_f25519_k" (ptr 6)
       |>.insert "fd_f25519_zero" (ptr 7)
       |>.insert "fd_ed25519_base_point_wnaf_table" (ptr 8)
       |>.insert "fd_sha512_core_ref.K" (ptr 9),
    mem := ⟨(∅ : Std.HashMap BlockId Block)
      |>.insert ⟨1⟩ (.live ⟨40, FiredancerFieldInitializer.bytes 0⟩)
      |>.insert ⟨2⟩ (.live ⟨40, FiredancerFieldInitializer.bytes 1⟩)
      |>.insert ⟨3⟩ (.live ⟨40, FiredancerFieldInitializer.bytes 2⟩)
      |>.insert ⟨4⟩ (.live ⟨40, FiredancerFieldInitializer.bytes 3⟩)
      |>.insert ⟨5⟩ (.live ⟨40, FiredancerFieldInitializer.bytes 4⟩)
      |>.insert ⟨6⟩ (.live ⟨40, FiredancerFieldInitializer.bytes 5⟩)
      |>.insert ⟨7⟩ (.live ⟨40, FiredancerFieldInitializer.bytes 6⟩)
      |>.insert ⟨8⟩ (.live ⟨20480, FiredancerBaseInitializer.bytes⟩)
      |>.insert ⟨9⟩ (.live ⟨640, FiredancerSHAExecution.constantsBytes⟩)
      |>.insert ⟨10⟩ (.live ⟨n, message⟩)
      |>.insert ⟨11⟩ (.live ⟨64, signature⟩)
      |>.insert ⟨12⟩ (.live ⟨32, publicKey⟩)⟩ }

variable {n : Nat} (message : BitVec (8*n)) (signature : BitVec 512)
  (publicKey : BitVec 256)

@[simp] private theorem mem_lookup (m : Std.HashMap BlockId Block) (q : BlockId) :
    (⟨m⟩ : MemoryState)[q]? = m[q]? := rfl

private theorem id_ne (q : BlockId) (h : 13 ≤ q.id) (i : Nat) (hi : i < 13) :
    q ≠ ⟨i⟩ := by
  intro he; have := congrArg BlockId.id he; dsimp at this; omega

theorem wf : (initial message signature publicKey).WF := by
  intro q hq
  change 13 ≤ q.id at hq
  have hn (i : Nat) (hi : i < 13) := id_ne q hq i hi
  simp [initial, MemoryState.live?, Ne.symm (hn 1 (by decide)),
    Ne.symm (hn 2 (by decide)), Ne.symm (hn 3 (by decide)),
    Ne.symm (hn 4 (by decide)), Ne.symm (hn 5 (by decide)),
    Ne.symm (hn 6 (by decide)), Ne.symm (hn 7 (by decide)),
    Ne.symm (hn 8 (by decide)), Ne.symm (hn 9 (by decide)),
    Ne.symm (hn 10 (by decide)), Ne.symm (hn 11 (by decide)),
    Ne.symm (hn 12 (by decide))]

theorem fields : FiredancerFieldInitializer.Loaded (initial message signature publicKey) := by
  intro k
  refine ⟨ptr (k.val+1), ?_⟩
  fin_cases k <;> constructor <;>
    simp [GlobalPtr, initial, FiredancerFieldInitializer.symbol, ptr, MemoryState.live?, Std.HashMap.getElem_insert]

theorem base : FiredancerBaseInitializer.Loaded (initial message signature publicKey) (ptr 8) := by
  constructor <;> simp [GlobalPtr, initial, FiredancerBaseInitializer.symbol, ptr, MemoryState.live?, Std.HashMap.getElem_insert]

theorem sha : FiredancerShaRawLoaded (initial message signature publicKey) (ptr 9)
    FiredancerSHAExecution.constantsBytes := by
  constructor <;> simp [GlobalPtr, initial, ptr, MemoryState.live?, Std.HashMap.getElem_insert]

theorem reference : (initial message signature publicKey).RefWF [] :=
  (fields message signature publicKey).refWF (wf message signature publicKey)
    (base message signature publicKey)

theorem message_live : (initial message signature publicKey).mem.live? (ptr 10).id =
    some ⟨n, message⟩ := by simp [initial, ptr, MemoryState.live?, Std.HashMap.getElem_insert]

theorem signature_live : (initial message signature publicKey).mem.live? (ptr 11).id =
    some ⟨64, signature⟩ := by simp [initial, ptr, MemoryState.live?, Std.HashMap.getElem_insert]

theorem publicKey_live : (initial message signature publicKey).mem.live? (ptr 12).id =
    some ⟨32, publicKey⟩ := by simp [initial, ptr, MemoryState.live?]

theorem input (hn : n < 2^63) : FiredancerInputReady (initial message signature publicKey)
    (ptr 10) (BitVec.ofNat 64 n) (ptr 11) (ptr 12) := by
  have h64 : n < 18446744073709551616 := by omega
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨n, message⟩, getElem?_of_live? (message_live message signature publicKey), ?_⟩
    simp [ptr, Pointer.offsetInBits, LiveBlock.lengthInBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mul_comm]
  · refine ⟨⟨64, signature⟩, getElem?_of_live? (signature_live message signature publicKey), ?_⟩
    simp [ptr, Pointer.offsetInBits, LiveBlock.lengthInBits]
  · refine ⟨⟨32, publicKey⟩, getElem?_of_live? (publicKey_live message signature publicKey), ?_⟩
    simp [ptr, Pointer.offsetInBits, LiveBlock.lengthInBits]
  · simp [ptr]
  · decide
  · simp [ptr]
  · simp [ptr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    omega

theorem small (hn : n < 2^63) :
    FiredancerBlockSmall (initial message signature publicKey).mem (ptr 10).id ∧
    FiredancerBlockSmall (initial message signature publicKey).mem (ptr 11).id ∧
    FiredancerBlockSmall (initial message signature publicKey).mem (ptr 12).id := by
  constructor
  · intro b hb
    have he := Option.some.inj ((message_live message signature publicKey).symm.trans hb)
    subst b
    exact hn
  constructor
  · intro b hb
    have he := Option.some.inj ((signature_live message signature publicKey).symm.trans hb)
    subst b
    change (64 : Nat) < 2^63
    decide
  · intro b hb
    have he := Option.some.inj ((publicKey_live message signature publicKey).symm.trans hb)
    subst b
    change (32 : Nat) < 2^63
    decide

/-- All raw Firedancer allocation premises hold simultaneously for every
message shorter than the signed LLVM object-size limit and arbitrary signature
and public-key bytes. No verifier or hash execution premise occurs here. -/
theorem ready (hn : n < 2^63) :
    (initial message signature publicKey).WF ∧
    FiredancerFieldInitializer.Loaded (initial message signature publicKey) ∧
    FiredancerBaseInitializer.Loaded (initial message signature publicKey) (ptr 8) ∧
    FiredancerShaRawLoaded (initial message signature publicKey) (ptr 9)
      FiredancerSHAExecution.constantsBytes ∧
    FiredancerInputReady (initial message signature publicKey)
      (ptr 10) (BitVec.ofNat 64 n) (ptr 11) (ptr 12) ∧
    FiredancerBlockSmall (initial message signature publicKey).mem (ptr 10).id ∧
    FiredancerBlockSmall (initial message signature publicKey).mem (ptr 11).id ∧
    FiredancerBlockSmall (initial message signature publicKey).mem (ptr 12).id :=
  ⟨wf message signature publicKey, fields message signature publicKey,
    base message signature publicKey, sha message signature publicKey,
    input message signature publicKey hn, small message signature publicKey hn⟩

end Agave.Ed25519.Bridge.FiredancerEnvironmentWitness
