import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Scalar

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def copiedEnv (E : Env program.Γ) (u left : Pointer) : Env program.Γ :=
  copyEnv3 (copyEnv2 (copyEnv1 (copyEnv0 (E) u left) u left) u left) u left

def copiedState (s : GlobalState) (left : Pointer) (b : Fin 32 → BitVec 8) : GlobalState :=
  copyState3 (copyState2 (copyState1 (copyState0 (s) left b) left b) left b) left b

theorem copied_state (s : GlobalState) (left : Pointer) (b : Fin 32 → BitVec 8) :
    copiedState s left b = {s with mem := ToBytes.storeBytes s.mem left b} := by
  simp only [copiedState, copyState0, copyState1, copyState2, copyState3, ToBytes.storeBytes]

theorem copied_frame (E : Env program.Γ) (u left : Pointer) :
    Frame E (copiedEnv E u left) := by
  unfold copiedEnv
  apply frame_trans _ _ _ ?_ (copy_frame3 _ u left)
  apply frame_trans _ _ _ ?_ (copy_frame2 _ u left)
  apply frame_trans _ _ _ ?_ (copy_frame1 _ u left)
  apply frame_trans _ _ _ ?_ (copy_frame0 _ u left)
  exact frame_refl E _

theorem copied_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (u left : Pointer) (b : Fin 32 → BitVec 8)
    (hu : SmallRange s.mem u 40) (hl : SmallRange s.mem left 32)
    (hc : Constants E) (hb : Cached E b)
    (eu : E.read (%arg1) = .value u) (el : E.read (%65) = .value left) :
    Cutpoint.segment (program p g) 0 308 67 E s =
      .value (copiedEnv E u left, copiedState s left b) := by
  have hf0 : Frame E (E) := by
    exact frame_refl E _
  have hu0 : SmallRange (s).mem u 40 := by
    exact hu
  have hleft0 : SmallRange (s).mem left 32 := by
    exact hl
  have h0 := copy_segment0 p g (E) (s) u left b hu0 hleft0
    (frame_constants E _ hf0 hc) (frame_cached E _ hf0 hb)
    ((frame_arg E _ hf0 1 rfl).trans eu)
    ((frame_read E _ hf0 65 (by decide) rfl).trans el)
  have hf1 : Frame E (copyEnv0 (E) u left) := by
    apply frame_trans _ _ _ ?_ (copy_frame0 _ u left)
    exact frame_refl E _
  have hu1 : SmallRange (copyState0 (s) left b).mem u 40 := by
    simp only [copyState0]
    repeat apply SmallRange.storeAt
    exact hu
  have hleft1 : SmallRange (copyState0 (s) left b).mem left 32 := by
    simp only [copyState0]
    repeat apply SmallRange.storeAt
    exact hl
  have h1 := copy_segment1 p g (copyEnv0 (E) u left) (copyState0 (s) left b) u left b hu1 hleft1
    (frame_constants E _ hf1 hc) (frame_cached E _ hf1 hb)
    ((frame_arg E _ hf1 1 rfl).trans eu)
    ((frame_read E _ hf1 65 (by decide) rfl).trans el)
  have hf2 : Frame E (copyEnv1 (copyEnv0 (E) u left) u left) := by
    apply frame_trans _ _ _ ?_ (copy_frame1 _ u left)
    apply frame_trans _ _ _ ?_ (copy_frame0 _ u left)
    exact frame_refl E _
  have hu2 : SmallRange (copyState1 (copyState0 (s) left b) left b).mem u 40 := by
    simp only [copyState0, copyState1]
    repeat apply SmallRange.storeAt
    exact hu
  have hleft2 : SmallRange (copyState1 (copyState0 (s) left b) left b).mem left 32 := by
    simp only [copyState0, copyState1]
    repeat apply SmallRange.storeAt
    exact hl
  have h2 := copy_segment2 p g (copyEnv1 (copyEnv0 (E) u left) u left) (copyState1 (copyState0 (s) left b) left b) u left b hu2 hleft2
    (frame_constants E _ hf2 hc) (frame_cached E _ hf2 hb)
    ((frame_arg E _ hf2 1 rfl).trans eu)
    ((frame_read E _ hf2 65 (by decide) rfl).trans el)
  have hf3 : Frame E (copyEnv2 (copyEnv1 (copyEnv0 (E) u left) u left) u left) := by
    apply frame_trans _ _ _ ?_ (copy_frame2 _ u left)
    apply frame_trans _ _ _ ?_ (copy_frame1 _ u left)
    apply frame_trans _ _ _ ?_ (copy_frame0 _ u left)
    exact frame_refl E _
  have hu3 : SmallRange (copyState2 (copyState1 (copyState0 (s) left b) left b) left b).mem u 40 := by
    simp only [copyState0, copyState1, copyState2]
    repeat apply SmallRange.storeAt
    exact hu
  have hleft3 : SmallRange (copyState2 (copyState1 (copyState0 (s) left b) left b) left b).mem left 32 := by
    simp only [copyState0, copyState1, copyState2]
    repeat apply SmallRange.storeAt
    exact hl
  have h3 := copy_segment3 p g (copyEnv2 (copyEnv1 (copyEnv0 (E) u left) u left) u left) (copyState2 (copyState1 (copyState0 (s) left b) left b) left b) u left b hu3 hleft3
    (frame_constants E _ hf3 hc) (frame_cached E _ hf3 hb)
    ((frame_arg E _ hf3 1 rfl).trans eu)
    ((frame_read E _ hf3 65 (by decide) rfl).trans el)
  unfold copiedEnv copiedState
  rw [show 67 = 19 + 48 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h0, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 48 = 16 + 32 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h1, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 32 = 16 + 16 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h2, PoisonOr.value_bind, Nat.reduceAdd]
  exact h3

theorem setup_frame (E : Env program.Γ) (right neg : Pointer) :
    Frame E (setupEnv E right neg) := by
  unfold setupEnv
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem negative_frame (E : Env program.Γ) (x : Words) :
    Frame E (negativeEnv E x) 301 := by
  unfold negativeEnv
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem copied_read (s : GlobalState) (left u : Pointer) (b : Fin 32 → BitVec 8)
    (hne : left.id ≠ u.id) : readLimbs (copiedState s left b) u = readLimbs s u := by
  rw [copied_state]
  funext i
  exact ToBytes.readAt_storeBytes_of_ne s.mem left (u.add (BitVec.ofNat 64 (8 * i.val))) b 64
    (by simpa only [Pointer.add_id] using hne)

def preparedEnv (E : Env program.Γ) (u left right neg : Pointer) : Env program.Γ :=
  setupEnv (copiedEnv E u left) right neg

def resultEnv (E : Env program.Γ) (u left right neg : Pointer) (x : Words) : Env program.Γ :=
  scalarEnv (negativeEnv (preparedEnv E u left right neg) x) (negated x)

def resultState (s : GlobalState) (u left right : Pointer) (b : Fin 32 → BitVec 8) : GlobalState :=
  {s with mem := (ToBytes.storeBytes (ToBytes.storeBytes s.mem left b) right
    (ToBytes.machine (negated (readLimbs s u))))}

theorem result_frame (E : Env program.Γ) (u left right neg : Pointer) (x : Words) :
    Frame E (resultEnv E u left right neg x) := by
  exact frame_trans _ _ _ (frame_trans _ _ _ (frame_trans _ _ _
    (copied_frame E u left) (setup_frame _ right neg))
    (frame_mono (n := 237) _ _ (negative_frame _ x) (by decide)))
    (frame_mono (n := 237) _ _ (scalar_frame _ (negated x)) (by decide))

/-- Exact original bb0 instructions308--568, ending immediately before bytesEq.
All execution and flag checks are derived; the premises describe only live
input registers and allocated byte ranges. -/
theorem segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (u left right neg : Pointer) (b : Fin 32 → BitVec 8)
    (hu : SmallRange s.mem u 40) (hl : SmallRange s.mem left 32)
    (hr : SmallRange s.mem right 32) (hn : SmallRange s.mem neg 40)
    (hc : Constants E) (hb : Cached E b)
    (eu : E.read (%arg1) = .value u) (el : E.read (%65) = .value left)
    (er : E.read (%64) = .value right) (en : E.read (%72) = .value neg)
    (hlu : left.id ≠ u.id) :
    Cutpoint.segment (program p g) 0 308 261 E s =
      .value (resultEnv E u left right neg (readLimbs s u), resultState s u left right b) := by
  let C := copiedEnv E u left
  let S := copiedState s left b
  let P := preparedEnv E u left right neg
  let x := readLimbs s u
  have fc : Frame E C := copied_frame E u left
  have fp : Frame E P := frame_trans _ _ _ fc (setup_frame C right neg)
  have hcC := frame_constants E C fc hc
  have hcP := frame_constants E P fp hc
  have live {q : Pointer} {n : Nat} (h : SmallRange s.mem q n) : SmallRange S.mem q n := by
    change SmallRange (copiedState s left b).mem q n
    rw [copied_state]
    exact ToBytes.smallRange_storeBytes h left b
  have hcopy := copied_segment p g E s u left b hu hl hc hb eu el
  have hsetup := setup_segment p g C S right neg (live hr) (live hn) hcC
    ((frame_read E C fc 64 (by decide) rfl).trans er)
    ((frame_read E C fc 72 (by decide) rfl).trans en)
  have e237 : P.read (%237) = .value (u.add 8#64) := by
    dsimp [P, preparedEnv, copiedEnv, setupEnv, copyEnv0, copyEnv1, copyEnv2, copyEnv3]
    rfl
  have hneg := negative_segment p g P S u (live hu) hcP
    ((frame_arg E P fp 1 rfl).trans eu) e237
  have hx : readLimbs S u = x := copied_read s left u b hlu
  rw [hx] at hneg
  have fn : Frame P (negativeEnv P x) 301 := negative_frame P x
  have hptr : Pointers (negativeEnv P x) right := by
    intro i
    have erP : P.read (%64) = .value right := (frame_read E P fp 64 (by decide) rfl).trans er
    fin_cases i
    · change (negativeEnv P x).read (%64) = .value (right.add 0#64)
      rw [Pointer.add_zero]
      exact (frame_read P _ fn 64 (by decide) rfl).trans erP
    · exact (frame_read P _ fn 269 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 270 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 271 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 272 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 273 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 274 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 275 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 276 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 277 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 278 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 279 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 280 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 281 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 282 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 283 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 284 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 285 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 286 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 287 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 288 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 289 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 290 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 291 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 292 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 293 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 294 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 295 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 296 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 297 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 298 (by decide) rfl).trans (by rfl)
    · exact (frame_read P _ fn 299 (by decide) rfl).trans (by rfl)
  have hscalar := scalar_segment p g (negativeEnv P x) S right (negated x) (live hr)
    (frame_constants P _ (frame_mono (n := 237) _ _ fn (by decide)) hcP) hptr (by rfl) (by rfl)
  dsimp only [C, S, P, x, preparedEnv] at hsetup hneg hscalar
  rw [show 261 = 67 + 194 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, hcopy, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 194 = 33 + 161 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, hsetup, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 161 = 13 + 148 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, hneg, PoisonOr.value_bind, Nat.reduceAdd]
  rw [hscalar, scalar_state, copied_state]
  rfl

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
