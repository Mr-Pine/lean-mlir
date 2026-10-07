import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline117Loads
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Frame
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EnvironmentFrame

/-! Exact instructions 117 through 305 of the pinned sqrt CFG. The result
retains the concrete byte registers and allocation-relative memory frame. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117
open LeanMLIR.RIR SerialFieldMul SerializerRename
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes

def resultState (s : GlobalState) (r : Pointer) (x : Words) : GlobalState :=
  { s with mem := ToBytes.storeBytes s.mem r (ToBytes.machine x) }

theorem writes_above (p : Primitives) (g : Globals) :
    ∀ i ∈ (((program.entry p g).body.drop 117).take 189),
      SerializerFrame.writesAbove 84 i := by
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.forall_mem_cons, SerializerFrame.writesAbove, true_and]
  repeat' apply And.intro
  all_goals first | decide | simp

theorem tail_writes_above (p : Primitives) (g : Globals) :
    ∀ i ∈ (((program.entry p g).body.drop 130).take 175),
      SerializerFrame.writesAbove 93 i := by
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.forall_mem_cons, SerializerFrame.writesAbove, true_and]
  repeat' apply And.intro
  all_goals first | decide | simp

theorem writes_within (p : Primitives) (g : Globals) :
    ∀ i ∈ (((program.entry p g).body.drop 117).take 189),
      SmallOrder.Execution.EnvironmentFrame.WritesWithin 84 235 i := by
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.forall_mem_cons, SmallOrder.Execution.EnvironmentFrame.WritesWithin, true_and]
  repeat' apply And.intro
  all_goals first | decide | simp

/-- Every register outside 84..235, including all arguments, is preserved. -/
theorem register_frame (p : Primitives) (g : Globals) (E F : Env program.Γ)
    (s t : GlobalState) (r : Reg program.Γ ty)
    (hr : SmallOrder.Execution.EnvironmentFrame.Outside 84 235 r)
    (h : Cutpoint.segment (program p g) 0 117 189 E s = .value (F, t)) :
    F.read r = E.read r :=
  SmallOrder.Execution.EnvironmentFrame.fold_of_outside 84 235 r _
    (writes_within p g) hr E F s t h

theorem byte_names (i : Fin 32) :
    rename.reg (SerializerRename.byteRegister i) = Inline308.byteRegister i := by
  fin_cases i <;> rfl

/-- The exact slice, without any assumed serializer result. The five limbs
are loaded from the current memory; all arithmetic flags are preserved by
the checked instruction-list renaming. -/
theorem segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 32) (ha : SmallRange s.mem a 40)
    (hc : Inline308.Constants E)
    (er : E.read (%67) = .value r) (ea : E.read (%75) = .value a) :
    ∃ F, Cutpoint.segment (program p g) 0 117 189 E s =
        .value (F, resultState s r (readLimbs s a)) ∧
      SerializerFrame.Frame 84 E F ∧
      Inline308.Cached F (ToBytes.machine (readLimbs s a)) ∧
      F.read (%85) = .value (a.add 8#64) ∧
      F.read (%87) = .value (a.add 16#64) ∧
      F.read (%89) = .value (a.add 24#64) ∧
      F.read (%91) = .value (a.add 32#64) := by
  let L := loadEnv E a (readLimbs s a)
  have hload := load_segment p g E s a ha ⟨ea, hc.c3, hc.c4, hc.c5, hc.c6⟩
  obtain ⟨G, hG, hbytes⟩ := tail54 (rename.project L) r a (readLimbs s a)
    s s rfl hwf hr (load_project_args E a r _ ea er)
  rw [load_constants E a _ hc] at hG
  change List.foldlM Instr.run (rename.project L) (ToBytes.program.entry.body.drop 54) s = _ at hG
  obtain ⟨F, hF, hproject⟩ := Renaming.list_success rename
    (ToBytes.program.entry.body.drop 54) source_supported L s _ G hG
  have htail : Cutpoint.segment (program p g) 0 130 175 L s =
      .value (F, resultState s r (readLimbs s a)) := by
    change List.foldlM Instr.run L (((program.entry p g).body.drop 130).take 175) s = _
    rw [exact_tail]
    exact hF
  have hfull : Cutpoint.segment (program p g) 0 117 189 E s =
      .value (F, resultState s r (readLimbs s a)) := by
    rw [show 189 = 13 + (175 + 1) from rfl, Inline.segment_append,
      EffectM.bind_eq, hload, PoisonOr.value_bind]
    change Cutpoint.segment (program p g) 0 130 (175 + 1) L s = _
    rw [Inline.segment_append, EffectM.bind_eq, htail, PoisonOr.value_bind]
    rfl
  have hframe : SerializerFrame.Frame 84 E F :=
    SerializerFrame.list_frame _ (writes_above p g) E s F _ hfull
  have htailframe : SerializerFrame.Frame 93 L F :=
    SerializerFrame.list_frame _ (tail_writes_above p g) L s F _ htail
  refine ⟨F, hfull, hframe, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hb := hbytes i
    rw [← hproject, rename.read, byte_names] at hb
    exact hb
  · exact htailframe.2 85 (by decide)
  · exact htailframe.2 87 (by decide)
  · exact htailframe.2 89 (by decide)
  · exact htailframe.2 91 (by decide)

theorem resume (p : Primitives) (g : Globals) (E F : Env program.Γ)
    (s : GlobalState) (r a : Pointer)
    (h : Cutpoint.segment (program p g) 0 117 189 E s =
      .value (F, resultState s r (readLimbs s a))) :
    Cutpoint.resume (program p g) 0 117 E s =
      Cutpoint.resume (program p g) 0 306 F (resultState s r (readLimbs s a)) :=
  Cutpoint.after_segment (program p g) 0 117 189 E F s
    (resultState s r (readLimbs s a)) h

theorem result_alloc (s : GlobalState) (r : Pointer) (x : Words) :
    (resultState s r x).alloc = s.alloc := by
  simp only [resultState]

theorem result_wf (s : GlobalState) (r : Pointer) (x : Words) (h : s.WF) :
    (resultState s r x).WF := ToBytes.wf_storeBytes h r _

theorem result_live (s : GlobalState) (r q : Pointer) (x : Words)
    (h : SmallRange s.mem q n) : SmallRange (resultState s r x).mem q n :=
  ToBytes.smallRange_storeBytes h r _

theorem result_read (s : GlobalState) (r q : Pointer) (x : Words)
    (h : r.id ≠ q.id) (w : Nat) :
    (resultState s r x).mem.readAt q w = s.mem.readAt q w :=
  ToBytes.readAt_storeBytes_of_ne s.mem r q _ w h

theorem result_readLimbs (s : GlobalState) (r q : Pointer) (x : Words)
    (h : r.id ≠ q.id) : readLimbs (resultState s r x) q = readLimbs s q := by
  funext i
  exact result_read s r (q.add (BitVec.ofNat 64 (8 * i.val))) x
    (by simpa only [Pointer.add_id] using h) 64

theorem result_erase (s : GlobalState) (r : Pointer) (x : Words) (mark : Nat)
    (h : mark ≤ r.id.id) :
    (resultState s r x).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  simp (disch := simpa only [Pointer.add_id] using h) only
    [resultState, ToBytes.storeBytes, MemoryState.eraseFrom_storeAt,
      MemoryState.storeAt_eraseFrom_of_le]

theorem result_byte (s : GlobalState) (r : Pointer) (x : Words)
    (hr : SmallRange s.mem r 32) (i : Fin 32) :
    (resultState s r x).mem.readAt (r.add (BitVec.ofNat 64 i.val)) 8 =
      (canonicalWord x).extractLsb' (8 * i.val) 8 := by
  rw [resultState, ToBytes.storeBytes_readAt _ _ _ hr]
  exact ToBytes.machine_canonical x i

theorem result_word (s : GlobalState) (r : Pointer) (x : Words)
    (hr : SmallRange s.mem r 32) :
    (resultState s r x).mem.readAt r 256 = canonicalWord x :=
  ToBytes.storeBytes_read256 s.mem r x hr

theorem result_compare (s : GlobalState) (r : Pointer) (x y : Words)
    (hr : SmallRange s.mem r 32) :
    (resultState s r x).mem.readAt r 256 = canonicalWord y ↔
      wordValue x = wordValue y := by
  rw [result_word s r x hr, canonicalWord_eq_iff]

/-- With the upstream check-word readback, the bytes at pc306 encode the
field expression that the following canonical-u comparison will test. -/
theorem result_check (s : GlobalState) (r a : Pointer) (u v : Pow22501.TightWords)
    (hr : SmallRange s.mem r 32) (hcheck : readLimbs s a = (wordCheck u v).limbs) :
    ((resultState s r (readLimbs s a)).mem.readAt r 256).toNat =
      (Decompress.check (wordValue u.limbs) (wordValue v.limbs)).val := by
  rw [result_word s r _ hr, hcheck, canonicalWord_value, wordCheck_value]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117
