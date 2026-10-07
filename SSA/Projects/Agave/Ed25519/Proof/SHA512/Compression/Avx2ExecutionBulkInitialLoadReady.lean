import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialLoad
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairStep
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairGroupReady
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialEntryReady

/-! Concrete entry invariant of the original bb11/bb12 bulk loop. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 3500000
set_option linter.unusedSimpArgs false

theorem BulkInitialLoadReady.of_entry (g : Globals) (E : Env program.Γ)
    (data scratch cache : Pointer) (n : Nat)
    (h : BulkInitialEntryReady g E) (hp : BulkInitialPointers E scratch cache)
    (hd : E.read (%arg1) = .value data) (hn : E.read (%358) = .value (BitVec.ofNat 64 n)) :
    BulkInitialLoadReady E data scratch cache n := by
  refine ⟨hp, hd, hn, h.v1, h.v4, h.v6, h.v8, h.v15, h.v17, h.v19, h.v21, h.v47, h.v52, h.v54, h.v56, h.v58, h.v60, h.v62, h.v64, ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · exact h.v51
  · exact h.v53
  · exact h.v55
  · exact h.v57
  · exact h.v59
  · exact h.v61
  · exact h.v63
  · exact h.v65

def bulkInitialPairEnv (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) : Env program.Γ :=
  bulkGroupPairEnv (bulkGroupSetupEnv
    (bulkInitialGroupEnv (bulkInitialLoadEnv E data n first second)) cache 1)

theorem bulkInitialGroupEnv_frame (E : Env program.Γ) : RegFrame 450 467 E (bulkInitialGroupEnv E) := by
  unfold bulkInitialGroupEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem bulkInitialSetupStage_frame (B : Env program.Γ) (cache : Pointer) :
    RegFrame 468 469 B (bulkGroupSetupEnv B cache 1) := by
  unfold bulkGroupSetupEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ B

private theorem bulkInitialPairStage_frame (B : Env program.Γ) :
    RegFrame 470 487 B (bulkGroupPairEnv B) := by
  unfold bulkGroupPairEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ B

theorem bulkInitialPairEnv_frame (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) : RegFrame 360 487 E (bulkInitialPairEnv E data cache n first second) := by
  have h : RegFrame 360 487 E (bulkInitialLoadEnv E data n first second) :=
    (bulkInitialLoadEnv_frame E data n first second).enlarge (by decide) (by decide)
  have h' := h.trans ((bulkInitialGroupEnv_frame _).enlarge (by decide) (by decide))
  have h'' := h'.trans ((bulkInitialSetupStage_frame _ cache).enlarge (by decide) (by decide))
  exact h''.trans ((bulkInitialPairStage_frame _).enlarge (by decide) (by decide))

theorem bulkInitialLoadEnv_word0 (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialLoadEnv E data n first second).read (%367) =
      bulkVec (readWordBE first 0) (readWordBE first 1)
        (readWordBE second 0) (readWordBE second 1) := by
  unfold bulkInitialLoadEnv
  rw [(bulkInitialSlice7Env_frame _ _ _ _ _ _).read (%367)]
  rw [(bulkInitialSlice6Env_frame _ _ _ _ _ _).read (%367)]
  rw [(bulkInitialSlice5Env_frame _ _ _ _ _ _).read (%367)]
  rw [(bulkInitialSlice4Env_frame _ _ _ _ _ _).read (%367)]
  rw [(bulkInitialSlice3Env_frame _ _ _ _ _ _).read (%367)]
  rw [(bulkInitialSlice2Env_frame _ _ _ _ _ _).read (%367)]
  rw [(bulkInitialSlice1Env_frame _ _ _ _ _ _).read (%367)]
  simp [bulkInitialSlice0Env, mlir_env]

theorem bulkInitialLoadEnv_word1 (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialLoadEnv E data n first second).read (%378) =
      bulkVec (readWordBE first 2) (readWordBE first 3)
        (readWordBE second 2) (readWordBE second 3) := by
  unfold bulkInitialLoadEnv
  rw [(bulkInitialSlice7Env_frame _ _ _ _ _ _).read (%378)]
  rw [(bulkInitialSlice6Env_frame _ _ _ _ _ _).read (%378)]
  rw [(bulkInitialSlice5Env_frame _ _ _ _ _ _).read (%378)]
  rw [(bulkInitialSlice4Env_frame _ _ _ _ _ _).read (%378)]
  rw [(bulkInitialSlice3Env_frame _ _ _ _ _ _).read (%378)]
  rw [(bulkInitialSlice2Env_frame _ _ _ _ _ _).read (%378)]
  simp [bulkInitialSlice1Env, mlir_env]

theorem bulkInitialLoadEnv_word2 (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialLoadEnv E data n first second).read (%389) =
      bulkVec (readWordBE first 4) (readWordBE first 5)
        (readWordBE second 4) (readWordBE second 5) := by
  unfold bulkInitialLoadEnv
  rw [(bulkInitialSlice7Env_frame _ _ _ _ _ _).read (%389)]
  rw [(bulkInitialSlice6Env_frame _ _ _ _ _ _).read (%389)]
  rw [(bulkInitialSlice5Env_frame _ _ _ _ _ _).read (%389)]
  rw [(bulkInitialSlice4Env_frame _ _ _ _ _ _).read (%389)]
  rw [(bulkInitialSlice3Env_frame _ _ _ _ _ _).read (%389)]
  simp [bulkInitialSlice2Env, mlir_env]

theorem bulkInitialLoadEnv_word3 (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialLoadEnv E data n first second).read (%400) =
      bulkVec (readWordBE first 6) (readWordBE first 7)
        (readWordBE second 6) (readWordBE second 7) := by
  unfold bulkInitialLoadEnv
  rw [(bulkInitialSlice7Env_frame _ _ _ _ _ _).read (%400)]
  rw [(bulkInitialSlice6Env_frame _ _ _ _ _ _).read (%400)]
  rw [(bulkInitialSlice5Env_frame _ _ _ _ _ _).read (%400)]
  rw [(bulkInitialSlice4Env_frame _ _ _ _ _ _).read (%400)]
  simp [bulkInitialSlice3Env, mlir_env]

theorem bulkInitialLoadEnv_word4 (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialLoadEnv E data n first second).read (%411) =
      bulkVec (readWordBE first 8) (readWordBE first 9)
        (readWordBE second 8) (readWordBE second 9) := by
  unfold bulkInitialLoadEnv
  rw [(bulkInitialSlice7Env_frame _ _ _ _ _ _).read (%411)]
  rw [(bulkInitialSlice6Env_frame _ _ _ _ _ _).read (%411)]
  rw [(bulkInitialSlice5Env_frame _ _ _ _ _ _).read (%411)]
  simp [bulkInitialSlice4Env, mlir_env]

theorem bulkInitialLoadEnv_word5 (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialLoadEnv E data n first second).read (%422) =
      bulkVec (readWordBE first 10) (readWordBE first 11)
        (readWordBE second 10) (readWordBE second 11) := by
  unfold bulkInitialLoadEnv
  rw [(bulkInitialSlice7Env_frame _ _ _ _ _ _).read (%422)]
  rw [(bulkInitialSlice6Env_frame _ _ _ _ _ _).read (%422)]
  simp [bulkInitialSlice5Env, mlir_env]

theorem bulkInitialLoadEnv_word6 (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialLoadEnv E data n first second).read (%433) =
      bulkVec (readWordBE first 12) (readWordBE first 13)
        (readWordBE second 12) (readWordBE second 13) := by
  unfold bulkInitialLoadEnv
  rw [(bulkInitialSlice7Env_frame _ _ _ _ _ _).read (%433)]
  simp [bulkInitialSlice6Env, mlir_env]

theorem bulkInitialLoadEnv_word7 (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialLoadEnv E data n first second).read (%444) =
      bulkVec (readWordBE first 14) (readWordBE first 15)
        (readWordBE second 14) (readWordBE second 15) := by
  unfold bulkInitialLoadEnv
  simp [bulkInitialSlice7Env, mlir_env]

theorem bulkInitialPairEnv_window (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    BulkPairWindowReady (bulkInitialPairEnv E data cache n first second)
      (specWindow first 0) (specWindow second 0) := by
  rw [← initialWindow_eq, ← initialWindow_eq]
  constructor <;>
    simp only [bulkInitialPairEnv, bulkGroupPairEnv, bulkGroupSetupEnv,
      bulkInitialGroupEnv, mlir_env, bulkInitialLoadEnv_word0, bulkInitialLoadEnv_word1, bulkInitialLoadEnv_word2, bulkInitialLoadEnv_word3, bulkInitialLoadEnv_word4, bulkInitialLoadEnv_word5, bulkInitialLoadEnv_word6, bulkInitialLoadEnv_word7] <;> rfl

private theorem bulkInitialPairStage_read470 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%470) = B.read (%450) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read470 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%450) = B.read (%450) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read470 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%450) = B.read (%4) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read470 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%470) =
      B.read (%4) := by
  rw [bulkInitialPairStage_read470, bulkInitialSetupStage_read470, bulkInitialGroupStage_read470]

theorem bulkInitialPairEnv_read470 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%470) = E.read (%4) :=
  (bulkInitialEnter_read470 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%4))

private theorem bulkInitialPairStage_read471 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%471) = B.read (%2) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read471 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%2) = B.read (%2) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read471 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%2) = B.read (%2) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read471 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%471) =
      B.read (%2) := by
  rw [bulkInitialPairStage_read471, bulkInitialSetupStage_read471, bulkInitialGroupStage_read471]

theorem bulkInitialPairEnv_read471 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%471) = E.read (%2) :=
  (bulkInitialEnter_read471 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%2))

private theorem bulkInitialPairStage_read480 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%480) = B.read (%460) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read480 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%460) = B.read (%460) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read480 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%460) = B.read (%350) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read480 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%480) =
      B.read (%350) := by
  rw [bulkInitialPairStage_read480, bulkInitialSetupStage_read480, bulkInitialGroupStage_read480]

theorem bulkInitialPairEnv_read480 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%480) = E.read (%350) :=
  (bulkInitialEnter_read480 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%350))

private theorem bulkInitialPairStage_read481 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%481) = B.read (%461) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read481 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%461) = B.read (%461) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read481 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%461) = B.read (%353) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read481 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%481) =
      B.read (%353) := by
  rw [bulkInitialPairStage_read481, bulkInitialSetupStage_read481, bulkInitialGroupStage_read481]

theorem bulkInitialPairEnv_read481 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%481) = E.read (%353) :=
  (bulkInitialEnter_read481 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%353))

private theorem bulkInitialPairStage_read482 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%482) = B.read (%462) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read482 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%462) = B.read (%462) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read482 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%462) = B.read (%351) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read482 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%482) =
      B.read (%351) := by
  rw [bulkInitialPairStage_read482, bulkInitialSetupStage_read482, bulkInitialGroupStage_read482]

theorem bulkInitialPairEnv_read482 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%482) = E.read (%351) :=
  (bulkInitialEnter_read482 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%351))

private theorem bulkInitialPairStage_read483 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%483) = B.read (%463) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read483 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%463) = B.read (%463) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read483 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%463) = B.read (%352) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read483 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%483) =
      B.read (%352) := by
  rw [bulkInitialPairStage_read483, bulkInitialSetupStage_read483, bulkInitialGroupStage_read483]

theorem bulkInitialPairEnv_read483 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%483) = E.read (%352) :=
  (bulkInitialEnter_read483 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%352))

private theorem bulkInitialPairStage_read484 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%484) = B.read (%464) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read484 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%464) = B.read (%464) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read484 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%464) = B.read (%357) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read484 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%484) =
      B.read (%357) := by
  rw [bulkInitialPairStage_read484, bulkInitialSetupStage_read484, bulkInitialGroupStage_read484]

theorem bulkInitialPairEnv_read484 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%484) = E.read (%357) :=
  (bulkInitialEnter_read484 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%357))

private theorem bulkInitialPairStage_read485 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%485) = B.read (%465) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read485 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%465) = B.read (%465) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read485 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%465) = B.read (%356) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read485 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%485) =
      B.read (%356) := by
  rw [bulkInitialPairStage_read485, bulkInitialSetupStage_read485, bulkInitialGroupStage_read485]

theorem bulkInitialPairEnv_read485 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%485) = E.read (%356) :=
  (bulkInitialEnter_read485 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%356))

private theorem bulkInitialPairStage_read486 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%486) = B.read (%466) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read486 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%466) = B.read (%466) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read486 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%466) = B.read (%355) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read486 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%486) =
      B.read (%355) := by
  rw [bulkInitialPairStage_read486, bulkInitialSetupStage_read486, bulkInitialGroupStage_read486]

theorem bulkInitialPairEnv_read486 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%486) = E.read (%355) :=
  (bulkInitialEnter_read486 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%355))

private theorem bulkInitialPairStage_read487 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%487) = B.read (%467) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read487 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%467) = B.read (%467) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read487 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%467) = B.read (%354) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read487 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%487) =
      B.read (%354) := by
  rw [bulkInitialPairStage_read487, bulkInitialSetupStage_read487, bulkInitialGroupStage_read487]

theorem bulkInitialPairEnv_read487 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%487) = E.read (%354) :=
  (bulkInitialEnter_read487 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%354))

private theorem bulkInitialPairStage_read451 (B : Env program.Γ) :
    (bulkGroupPairEnv B).read (%451) = B.read (%451) := by
  simp [bulkGroupPairEnv, mlir_env]

private theorem bulkInitialSetupStage_read451 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupSetupEnv B cache 1).read (%451) = B.read (%451) := by
  simp [bulkGroupSetupEnv, mlir_env]

private theorem bulkInitialGroupStage_read451 (B : Env program.Γ) :
    (bulkInitialGroupEnv B).read (%451) = B.read (%1) := by
  simp [bulkInitialGroupEnv, mlir_env]

private theorem bulkInitialEnter_read451 (B : Env program.Γ) (cache : Pointer) :
    (bulkGroupPairEnv (bulkGroupSetupEnv (bulkInitialGroupEnv B) cache 1)).read (%451) =
      B.read (%1) := by
  rw [bulkInitialPairStage_read451, bulkInitialSetupStage_read451, bulkInitialGroupStage_read451]

theorem bulkInitialPairEnv_read451 (E : Env program.Γ) (data cache : Pointer) (n : Nat)
    (first second : Bytes) :
    (bulkInitialPairEnv E data cache n first second).read (%451) = E.read (%1) :=
  (bulkInitialEnter_read451 _ cache).trans ((bulkInitialLoadEnv_frame E data n first second).read (%1))

theorem bulkInitialPairEnv_ready (g : Globals) (E : Env program.Γ)
    (data scratch cache : Pointer) (n : Nat) (pairs : BitVec 64)
    (first second : Bytes) (s : Spec.State)
    (h : BulkInitialEntryReady g E) (hp : BulkInitialPointers E scratch cache)
    (ho : BulkOuterReady E s (BitVec.ofNat 64 n) pairs) :
    BulkPairSpecReady (bulkInitialPairEnv E data cache n first second)
      scratch cache g.address0 0 0 first second s := by
  have hf := bulkInitialPairEnv_frame E data cache n first second
  constructor
  · constructor
    · exact (hf.read (%24)).trans h.v24
    · exact (bulkInitialPairEnv_read470 E data cache n first second).trans h.v4
    · exact (bulkInitialPairEnv_read471 E data cache n first second).trans h.v2
    · exact (hf.read (%1)).trans h.v1
    · exact (hf.read (%68)).trans h.v68
    · exact (hf.read (%69)).trans h.v69
    · exact (hf.read (%70)).trans h.v70
    · exact (hf.read (%71)).trans h.v71
    · exact (hf.read (%72)).trans h.v72
    · exact (hf.read (%73)).trans h.v73
    · exact (hf.read (%74)).trans h.v74
    · exact (hf.read (%75)).trans h.v75
    · exact (hf.read (%76)).trans h.v76
    · exact (hf.read (%77)).trans h.v77
  · exact bulkInitialPairEnv_window E data cache n first second
  · constructor
    · exact (hf.read (%83)).trans hp.scratchPtr
    · exact (bulkInitialPairEnv_read471 E data cache n first second).trans h.v2
    · exact (bulkInitialPairEnv_read484 E data cache n first second).trans ho.a
    · exact (bulkInitialPairEnv_read485 E data cache n first second).trans ho.b
    · exact (bulkInitialPairEnv_read486 E data cache n first second).trans ho.c
    · exact (bulkInitialPairEnv_read487 E data cache n first second).trans ho.d
    · exact (bulkInitialPairEnv_read481 E data cache n first second).trans ho.e
    · exact (bulkInitialPairEnv_read483 E data cache n first second).trans ho.f
    · exact (bulkInitialPairEnv_read482 E data cache n first second).trans ho.g
    · exact (bulkInitialPairEnv_read480 E data cache n first second).trans ho.h
    · exact (hf.read (%3)).trans h.v3
    · exact (hf.read (%35)).trans h.v35
    · exact (hf.read (%36)).trans h.v36
    · exact (hf.read (%37)).trans h.v37
    · exact (hf.read (%38)).trans h.v38
    · exact (hf.read (%39)).trans h.v39
    · exact (hf.read (%40)).trans h.v40
    · exact (hf.read (%41)).trans h.v41
  · exact (hf.read (%42)).trans h.v42
  · simp [bulkInitialPairEnv, bulkGroupPairEnv, bulkGroupSetupEnv, mlir_env]

theorem bulkInitialPairEnv_group (g : Globals) (E : Env program.Γ)
    (data cache : Pointer) (n : Nat) (first second : Bytes) (h : BulkInitialEntryReady g E) :
    BulkGroupReady (bulkInitialPairEnv E data cache n first second) 1 := by
  have hf := bulkInitialPairEnv_frame E data cache n first second
  constructor
  · exact (bulkInitialPairEnv_read451 E data cache n first second).trans h.v1
  · exact (hf.read (%1)).trans h.v1
  · exact (hf.read (%78)).trans h.v78

theorem bulkInitialPairEnv_loopConstants (g : Globals) (E : Env program.Γ)
    (data scratch cache : Pointer) (n : Nat) (first second : Bytes)
    (h : BulkInitialEntryReady g E) (hp : BulkInitialPointers E scratch cache) :
    BulkPairLoopConstants (bulkInitialPairEnv E data cache n first second) cache := by
  have hf := bulkInitialPairEnv_frame E data cache n first second
  exact ⟨(hf.read (%2)).trans h.v2, (hf.read (%15)).trans h.v15,
    (hf.read (%17)).trans h.v17, (hf.read (%44)).trans h.v44,
    (hf.read (%82)).trans hp.cachePtr, (hf.read (%66)).trans h.v66⟩

theorem bulk_initial_pair_setup_run (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (n : Nat) (first second : Bytes)
    (h : BulkInitialEntryReady g E) (hp : BulkInitialPointers E scratch cache)
    (hc : SmallRange mem.mem cache 640) :
    program.bb11.run program.blockParams
      (bulkInitialGroupEnv (bulkInitialLoadEnv E data n first second)) mem =
      .value ((bulkInitialPairEnv E data cache n first second, .inr 12), mem) := by
  have hl := bulkInitialLoadEnv_frame E data n first second
  apply bulk_group_setup_run _ mem cache 1 (by decide) hc
  · simp [bulkInitialGroupEnv, mlir_env, hl.read (%82), hp.cachePtr]
  · simp [bulkInitialGroupEnv, mlir_env, hl.read (%1), h.v1]
  · simp [bulkInitialGroupEnv, mlir_env, hl.read (%66), h.v66]

end Agave.Ed25519.SHA512.Execution.Avx2
