import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialMemory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialScanPrefix
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorContext
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory

/-! Exact execution of the original serial block 16. The constructor's
contextual call is followed by the three projective-identity writes and all
nineteen original inbounds scratch addresses, entering block 18. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readField readPoint readCached readProjective)
set_option maxRecDepth 10000

/-- Slots zero through six are registers 32 through 38. -/
abbrev SerialSetupSlots := Fin 7 → Pointer

def serialIdentityZero (s : GlobalState) (p : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt p (0#320)}

def serialIdentityY (s : GlobalState) (p : Pointer) : GlobalState :=
  {serialIdentityZero s p with mem := (serialIdentityZero s p).mem.storeAt (p.add 40#64) (1#320)}

def serialIdentityState (s : GlobalState) (p : Pointer) : GlobalState :=
  {serialIdentityY s p with mem := (serialIdentityY s p).mem.storeAt (p.add 80#64) (1#320)}

theorem serialIdentity_buffer {p : Pointer} (h : Buffer s.mem q bytes) :
    Buffer (serialIdentityState s p).mem q bytes :=
  ((h.storeAt _ _).storeAt _ _).storeAt _ _

theorem serialIdentity_frame (s : GlobalState) (p : Pointer)
    (hwf : s.WF) (hp : Buffer s.mem p 120) :
    WritesOnly p 120 s (serialIdentityState s p) := by
  refine ⟨?_, le_refl _, ?_, ?_⟩
  · simpa only [serialIdentityState, serialIdentityY, serialIdentityZero,
      GlobalState.WF_storeAt] using hwf
  · intro id
    simp only [serialIdentityState, serialIdentityY, serialIdentityZero,
      SerialPoint.Execution.storeAt_allocationShape]
  · intro q bits hd
    have h0 := range_disjoint_subrange hp hd (k := 0) (count := 40) (by decide)
    have h40 := range_disjoint_subrange hp hd (k := 40) (count := 40) (by decide)
    have h80 := range_disjoint_subrange hp hd (k := 80) (count := 40) (by decide)
    simp only [Pointer.add_zero] at h0
    unfold serialIdentityState serialIdentityY serialIdentityZero
    erw [MemoryState.readAt_storeAt_disjoint h80.symm,
      MemoryState.readAt_storeAt_disjoint h40.symm,
      MemoryState.readAt_storeAt_disjoint h0.symm]

def serialSetupInput (E : ⟪serialKernel.Γ⟫) (slots : SerialSetupSlots)
    (table identity : Pointer) (pos : Fin 256) : ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8, %20 := .value 40#64, %21 := .value identity,
    %22 := .value 80#64, %23 := .value 120#64,
    %32 := .value (slots 0), %33 := .value (slots 1), %34 := .value (slots 2),
    %35 := .value (slots 3), %36 := .value (slots 4), %37 := .value (slots 5),
    %38 := .value (slots 6), %39 := .value table,
    %103 := .value (BitVec.ofNat 64 pos.val)]

def serialSetupResult (E : ⟪serialKernel.Γ⟫) (slots : SerialSetupSlots)
    (table identity : Pointer) (pos : Fin 256) : ⟪serialKernel.Γ⟫ :=
  (serialSetupInput E slots table identity pos)[
    %107 := .value ((slots 6).add 40#64), %108 := .value ((slots 6).add 80#64),
    %109 := .value ((slots 5).add 120#64), %110 := .value ((slots 5).add 40#64),
    %111 := .value ((slots 5).add 80#64), %112 := .value ((slots 4).add 40#64),
    %113 := .value ((slots 4).add 80#64), %114 := .value ((slots 4).add 120#64),
    %115 := .value ((slots 3).add 40#64), %116 := .value ((slots 3).add 80#64),
    %117 := .value ((slots 3).add 120#64), %118 := .value ((slots 2).add 40#64),
    %119 := .value ((slots 2).add 80#64), %120 := .value ((slots 2).add 120#64),
    %121 := .value ((slots 1).add 40#64), %122 := .value ((slots 1).add 80#64),
    %123 := .value ((slots 1).add 120#64), %124 := .value ((slots 0).add 40#64),
    %125 := .value ((slots 0).add 80#64), %131 := .value (BitVec.ofNat 64 pos.val)]

/-- All incoming arguments, constants, and original scratch registers survive. -/
theorem serialSetupResult_frame (E : ⟪serialKernel.Γ⟫) (slots : SerialSetupSlots)
    (table identity : Pointer) (pos : Fin 256) :
    PrefixEq (serialSetupInput E slots table identity pos)
      (serialSetupResult E slots table identity pos) 107 := by
  unfold serialSetupResult
  iterate 20 apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

set_option maxHeartbeats 2000000 in
/-- A local operational equation, retaining the constructor call as a callee
boundary. The contextual contract below discharges that boundary. -/
theorem serial_setup_block (p : SerialCFG.Primitives) (E : ⟪serialKernel.Γ⟫)
    (slots : SerialSetupSlots) (table identity input : Pointer) (pos : Fin 256)
    (s t : GlobalState) (harg : E.args 2 = .value input)
    (hcall : p.call0 (.cons (.value table) (.cons (.value input) .nil)) s = .value (.nil, t))
    (hslots : ∀ i, Buffer t.mem (slots i) 120)
    (hidentity : Buffer t.mem identity 40) (hone : t.mem.readAt identity 320 = 1#320)
    (hne : (slots 6).id ≠ identity.id) :
    (serialKernel.bb16 p).run serialKernel.blockParams
      (serialSetupInput E slots table identity pos) s =
      .value ((serialSetupResult E slots table identity pos, .inr 18),
        serialIdentityState t (slots 6)) := by
  let q := slots 6
  have hzero (env : ⟪serialKernel.Γ⟫) :=
    Verifier.Execution.Dalek.identity_zero_operation t q env (by simpa only [Pointer.add_zero] using (hslots 6).fits_at 0 40 (by decide))
  have hg40 := ((hslots 6).storeAt q (0#320)).gep 40 (by decide)
  have hi0 : (serialIdentityZero t q).mem.readAt identity 320 = 1#320 := by
    rw [serialIdentityZero, MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hne), hone]
  have hcopyY (env : ⟪serialKernel.Γ⟫) :=
    Verifier.Execution.Dalek.identity_one_operation (serialIdentityZero t q)
      (q.add 40#64) identity env (((hslots 6).storeAt q (0#320)).fits_at 40 40 (by decide))
      (hidentity.storeAt q (0#320)).fits hi0
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne))
  have hg80 := (((hslots 6).storeAt q (0#320)).storeAt (q.add 40#64) (1#320)).gep 80 (by decide)
  have hi1 : (serialIdentityY t q).mem.readAt identity 320 = 1#320 := by
    rw [serialIdentityY, MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne)), hi0]
  have hcopyZ (env : ⟪serialKernel.Γ⟫) :=
    Verifier.Execution.Dalek.identity_one_operation (serialIdentityY t q)
      (q.add 80#64) identity env
      ((((hslots 6).storeAt q (0#320)).storeAt (q.add 40#64) (1#320)).fits_at 80 40 (by decide))
      ((hidentity.storeAt q (0#320)).storeAt (q.add 40#64) (1#320)).fits hi1
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne))
  have hg40' (i : Fin 7) := (serialIdentity_buffer (p := q) (hslots i)).gep 40 (by decide)
  have hg80' (i : Fin 7) := (serialIdentity_buffer (p := q) (hslots i)).gep 80 (by decide)
  have hg120' (i : Fin 7) := (serialIdentity_buffer (p := q) (hslots i)).gep 120 (by decide)
  simp only [Int.cast_ofNat_Int] at hg40 hg80 hg40' hg80' hg120'
  change ∀ env, Operation.memset _ _ _ env t = .value (env, serialIdentityZero t q) at hzero
  change ∀ env, Operation.memcpy _ _ _ env (serialIdentityZero t q) = .value (env, serialIdentityY t q) at hcopyY
  change ∀ env, Operation.memcpy _ _ _ env (serialIdentityY t q) = .value (env, serialIdentityState t q) at hcopyZ
  change Operation.gepInboundsLive (serialIdentityZero t q).mem _ _ = _ at hg40
  change Operation.gepInboundsLive (serialIdentityY t q).mem _ _ = _ at hg80
  simp only [q] at hzero hcopyY hcopyZ hg40 hg80 hg40' hg80' hg120'
  simp [BasicBlock.run, serialKernel.bb16, serialSetupInput, serialSetupResult,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    harg, hcall, hzero, hcopyY, hcopyZ,
    hg40, hg80, hg40', hg80', hg120',
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

set_option maxHeartbeats 2000000 in
/-- The scalar-preparation register frame supplies every setup input except
its cursor, which is the proved scan result. -/
theorem serialSetupInput_of_prefix (E F : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) (pos : Fin 256)
    (hframe : PrefixEq (serialInitial5 E g s) F 43)
    (hpos : F.read (%103) = .value (BitVec.ofNat 64 pos.val)) :
    serialSetupInput F (fun i => serialStackPtr s (i.val + 2))
      (serialStackPtr s 9) g.address0 pos = F := by
  have h1 : F.read (%1) = .value 0#8 := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h20 : F.read (%20) = .value 40#64 := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h21 : F.read (%21) = .value g.address0 := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h22 : F.read (%22) = .value 80#64 := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h23 : F.read (%23) = .value 120#64 := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h32 : F.read (%32) = .value (serialStackPtr s 2) := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h33 : F.read (%33) = .value (serialStackPtr s 3) := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h34 : F.read (%34) = .value (serialStackPtr s 4) := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h35 : F.read (%35) = .value (serialStackPtr s 5) := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h36 : F.read (%36) = .value (serialStackPtr s 6) := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h37 : F.read (%37) = .value (serialStackPtr s 7) := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h38 : F.read (%38) = .value (serialStackPtr s 8) := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h39 : F.read (%39) = .value (serialStackPtr s 9) := by
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  unfold serialSetupInput
  erw [Env.write_of_read F (%1) h1,
    Env.write_of_read F (%20) h20,
    Env.write_of_read F (%21) h21,
    Env.write_of_read F (%22) h22,
    Env.write_of_read F (%23) h23,
    Env.write_of_read F (%32) h32,
    Env.write_of_read F (%33) h33,
    Env.write_of_read F (%34) h34,
    Env.write_of_read F (%35) h35,
    Env.write_of_read F (%36) h36,
    Env.write_of_read F (%37) h37,
    Env.write_of_read F (%38) h38,
    Env.write_of_read F (%39) h39,
    Env.write_of_read F (%103) hpos]

end Agave.Ed25519.DoubleBase.RIR
