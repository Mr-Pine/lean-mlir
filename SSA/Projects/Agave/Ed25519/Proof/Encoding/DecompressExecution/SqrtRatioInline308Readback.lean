import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Execution

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000

/-- The original comparison flag survives every instruction of this slice. -/
theorem result_flag (E : Env program.Γ) (u left right neg : Pointer) (x : Words) :
    (resultEnv E u left right neg x).read (%236) = E.read (%236) :=
  frame_read _ _ (result_frame E u left right neg x) 236 (by decide) rfl

theorem result_negative_low (E : Env program.Γ) (u left right neg : Pointer) (x : Words) :
    (resultEnv E u left right neg x).read (%312) = .value (negativeWords x 0) := by
  have h := frame_read _ _ (scalar_frame (negativeEnv (preparedEnv E u left right neg) x)
    (negated x)) 312 (by decide) rfl
  change (resultEnv E u left right neg x).read (%312) = .value (negated x 0) at h
  simpa only [negated_eq] using h

theorem result_negative_high (E : Env program.Γ) (u left right neg : Pointer) (x : Words) :
    (resultEnv E u left right neg x).read (%313) =
      Ty.wrap #v[negativeWords x 1, negativeWords x 2, negativeWords x 3, negativeWords x 4] := by
  have h := frame_read _ _ (scalar_frame (negativeEnv (preparedEnv E u left right neg) x)
    (negated x)) 313 (by decide) rfl
  have hn : (negativeEnv (preparedEnv E u left right neg) x).read (%313) =
      Ty.wrap #v[negated x 1, negated x 2, negated x 3, negated x 4] := by
    simp only [negativeEnv, mlir_env]
  exact h.trans (hn.trans (by rw [negated_eq]))

/-- Address consumed by the following packed negative-limb store at pc575. -/
theorem result_negative_ptr (E : Env program.Γ) (u left right neg : Pointer) (x : Words) :
    (resultEnv E u left right neg x).read (%300) = .value (neg.add 8#64) := by
  have hs := frame_read _ _ (scalar_frame (negativeEnv (preparedEnv E u left right neg) x)
    (negated x)) 300 (by decide) rfl
  have hn := frame_read _ _ (negative_frame (preparedEnv E u left right neg) x)
    300 (by decide) rfl
  exact hs.trans (hn.trans (by rfl))

theorem result_wf (s : GlobalState) (u left right : Pointer) (b : Fin 32 → BitVec 8)
    (h : s.WF) : (resultState s u left right b).WF :=
  ToBytes.wf_storeBytes (ToBytes.wf_storeBytes h left b) right _

theorem result_alloc (s : GlobalState) (u left right : Pointer) (b : Fin 32 → BitVec 8) :
    (resultState s u left right b).alloc = s.alloc := by
  simp only [resultState]

theorem result_live (s : GlobalState) (u left right q : Pointer) (b : Fin 32 → BitVec 8)
    (h : SmallRange s.mem q n) : SmallRange (resultState s u left right b).mem q n :=
  ToBytes.smallRange_storeBytes (ToBytes.smallRange_storeBytes h left b) right _

theorem result_read_ne (s : GlobalState) (u left right q : Pointer) (b : Fin 32 → BitVec 8)
    (hl : left.id ≠ q.id) (hr : right.id ≠ q.id) (w : Nat) :
    (resultState s u left right b).mem.readAt q w = s.mem.readAt q w := by
  simp only [resultState, ToBytes.readAt_storeBytes_of_ne _ right q _ w hr,
    ToBytes.readAt_storeBytes_of_ne _ left q _ w hl]

theorem storeBytes_erase (m : MemoryState) (p : Pointer) (b : Fin 32 → BitVec 8)
    (mark : Nat) (hp : mark ≤ p.id.id) :
    (ToBytes.storeBytes m p b).eraseFrom mark = m.eraseFrom mark := by
  simp only [ToBytes.storeBytes, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (p := p.add _) hp]

/-- The slice modifies only the two designated byte buffers. -/
theorem result_public (s : GlobalState) (u left right : Pointer) (b : Fin 32 → BitVec 8)
    (mark : Nat) (hl : mark ≤ left.id.id) (hr : mark ≤ right.id.id) :
    (resultState s u left right b).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  simp only [resultState, storeBytes_erase _ right _ mark hr,
    storeBytes_erase _ left _ mark hl]

theorem result_left (s : GlobalState) (u left right : Pointer) (check : Words)
    (hl : SmallRange s.mem left 32) (hne : right.id ≠ left.id) :
    (resultState s u left right (ToBytes.machine check)).mem.readAt left 256 =
      canonicalWord check := by
  unfold resultState
  rw [ToBytes.readAt_storeBytes_of_ne _ right left _ 256 hne]
  exact ToBytes.storeBytes_read256 s.mem left check hl

theorem result_right (s : GlobalState) (u left right : Pointer) (b : Fin 32 → BitVec 8)
    (hr : SmallRange s.mem right 32) :
    (resultState s u left right b).mem.readAt right 256 =
      canonicalWord (negativeWords (readLimbs s u)) := by
  unfold resultState
  rw [ToBytes.storeBytes_read256 _ right _ (ToBytes.smallRange_storeBytes hr left b)]
  rw [negated_eq]
  rfl

/-- The exact semantic byte flag that the pc569 bytesEq call will return. -/
theorem comparison (s : GlobalState) (u left right : Pointer) (check : Words)
    (hl : SmallRange s.mem left 32) (hr : SmallRange s.mem right 32)
    (hne : right.id ≠ left.id) (hu : Bounded (unsigned (readLimbs s u))) :
    BytesEq.comparison (resultState s u left right (ToBytes.machine check)) left right =
      if wordValue check = -wordValue (readLimbs s u) then 1 else 0 := by
  rw [BytesEq.comparison_exact _ _ _ (result_live s u left right left _ hl)
    (result_live s u left right right _ hr), result_left s u left right check hl hne,
    result_right s u left right _ hr]
  simp only [canonicalWord_eq_iff, negativeWords_value _ hu]
  split_ifs with h h' h'
  · rfl
  · exact False.elim (h' h)
  · exact False.elim (h h')
  · rfl

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
