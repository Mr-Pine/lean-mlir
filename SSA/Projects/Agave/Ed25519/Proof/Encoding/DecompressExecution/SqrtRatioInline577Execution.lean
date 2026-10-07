import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Prepared
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Slices
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Memory

/-! Exact execution of instructions 577 through 946, comprising two canonical
serializers. Live-ins are individual constants, pointers and readable ranges;
no prefix-success, slice-result, or field-result premise is used. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
open LeanMLIR.RIR SerialFieldMul SerializerRename SerializerFrame
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes

private theorem source_supported :
    ∀ i ∈ ((ToBytes.program.entry).body.drop 54).take 175,
      Renaming.supported i := by
  dsimp only [ToBytes.program.entry,List.drop,List.take]
  simp only [List.forall_mem_cons,Renaming.supported,
    SmallOrder.Execution.Transport.Supported,true_and]
  simp

theorem first_serializer (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (a r : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 40) (hr : SmallRange s.mem r 32)
    (hc : Constants E) (he : FirstLoadRegisters E a)
    (er : E.read (%63) = .value r) :
    ∃ F, Cutpoint.segment (program p g) 0 577 183 E s =
      .value (F,serialize s r (readLimbs s a)) ∧ Frame 431 E F := by
  obtain ⟨H,hH,_⟩ := tail54 (firstRenaming.project (firstLoadEnv E (readLimbs s a)))
    r a (readLimbs s a) s s rfl hwf hr (first_source_args E (readLimbs s a) r a er he.a75)
  rw [first_prepared E (readLimbs s a) hc] at hH
  change List.foldlM Instr.run (firstRenaming.project (firstLoadEnv E (readLimbs s a)))
    (((ToBytes.program.entry).body.drop 54).take 175) s =
      .value (H,serialize s r (readLimbs s a)) at hH
  obtain ⟨F,hF,_⟩ := Renaming.list_success firstRenaming _ source_supported
    (firstLoadEnv E (readLimbs s a)) s (serialize s r (readLimbs s a)) H hH
  have htail : Cutpoint.segment (program p g) 0 585 175
      (firstLoadEnv E (readLimbs s a)) s = .value (F,serialize s r (readLimbs s a)) := by
    change List.foldlM Instr.run (firstLoadEnv E (readLimbs s a))
      (((program.entry p g).body.drop 585).take 175) s = _
    rw [first_tail_names]
    exact hF
  have hfull : Cutpoint.segment (program p g) 0 577 183 E s =
      .value (F,serialize s r (readLimbs s a)) := by
    rw [show 183 = 8 + 175 from rfl,Inline.segment_append]
    simp only [Nat.reduceAdd,EffectM.bind_eq,first_load_segment p g E s a ha he,
      PoisonOr.value_bind]
    exact htail
  exact ⟨F,hfull,list_frame _ (first_writes p g) E s F _ hfull⟩

theorem second_serializer (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (a r : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 40) (hr : SmallRange s.mem r 32)
    (hc : Constants E) (he : SecondLoadRegisters E a)
    (er : E.read (%62) = .value r) :
    ∃ F, Cutpoint.segment (program p g) 0 760 187 E s =
      .value (F,serialize s r (readLimbs s a)) ∧ Frame 579 E F := by
  obtain ⟨H,hH,_⟩ := tail54 (secondRenaming.project (secondLoadEnv E a (readLimbs s a)))
    r a (readLimbs s a) s s rfl hwf hr (second_source_args E a (readLimbs s a) r a er he.a73)
  rw [second_prepared E a (readLimbs s a) hc] at hH
  change List.foldlM Instr.run (secondRenaming.project (secondLoadEnv E a (readLimbs s a)))
    (((ToBytes.program.entry).body.drop 54).take 175) s =
      .value (H,serialize s r (readLimbs s a)) at hH
  obtain ⟨F,hF,_⟩ := Renaming.list_success secondRenaming _ source_supported
    (secondLoadEnv E a (readLimbs s a)) s (serialize s r (readLimbs s a)) H hH
  have htail : Cutpoint.segment (program p g) 0 772 175
      (secondLoadEnv E a (readLimbs s a)) s = .value (F,serialize s r (readLimbs s a)) := by
    change List.foldlM Instr.run (secondLoadEnv E a (readLimbs s a))
      (((program.entry p g).body.drop 772).take 175) s = _
    rw [second_tail_names]
    exact hF
  have hfull : Cutpoint.segment (program p g) 0 760 187 E s =
      .value (F,serialize s r (readLimbs s a)) := by
    rw [show 187 = 12 + 175 from rfl,Inline.segment_append]
    simp only [Nat.reduceAdd,EffectM.bind_eq,second_load_segment p g E s a ha he,
      PoisonOr.value_bind]
    exact htail
  exact ⟨F,hfull,list_frame _ (second_writes p g) E s F _ hfull⟩

/-- All 370 original instructions execute and preserve every argument and
all values below %431. The exact resulting memory performs 64 byte stores. -/
theorem segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (a b r q : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 40) (hb : SmallRange s.mem b 40)
    (hr : SmallRange s.mem r 32) (hq : SmallRange s.mem q 32)
    (he : Registers E a b r q) :
    ∃ F, Cutpoint.segment (program p g) 0 577 370 E s =
      .value (F,resultState s a b r q) ∧ Frame 431 E F := by
  obtain ⟨F,hfirst,hframe⟩ := first_serializer p g E s a r hwf ha hr
    he.constants he.first he.r63
  have hf := registers_frame E F a b r q he hframe
  obtain ⟨G,hsecond,hframe'⟩ := second_serializer p g F
    (serialize s r (readLimbs s a)) b q (serialize_wf s r _ hwf)
    (serialize_live s r _ hb) (serialize_live s r _ hq)
    hf.constants hf.second hf.q62
  refine ⟨G,?_,hframe.trans (hframe'.mono (by decide))⟩
  rw [show 370 = 183 + 187 from rfl,Inline.segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,hfirst,PoisonOr.value_bind]
  exact hsecond

/-- Resume the original continuation at pc947, retaining its comparison
pointer registers and all earlier comparison results. -/
theorem resume (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (a b r q : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 40) (hb : SmallRange s.mem b 40)
    (hr : SmallRange s.mem r 32) (hq : SmallRange s.mem q 32)
    (he : Registers E a b r q) :
    ∃ F, Cutpoint.resume (program p g) 0 577 E s =
      Cutpoint.resume (program p g) 0 947 F (resultState s a b r q) ∧
      Registers F a b r q ∧ Frame 431 E F := by
  obtain ⟨F,hF,hframe⟩ := segment p g E s a b r q hwf ha hb hr hq he
  exact ⟨F,Cutpoint.after_segment (program p g) 0 577 370 E F s _ hF,
    registers_frame E F a b r q he hframe,hframe⟩

/-- Public endpoint at pc947: exact execution, preserved live registers, and
canonical comparison inputs, with separation needed only for readback. -/
theorem segment_correct (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (a b r q : Pointer) (hwf : s.WF)
    (ha : SmallRange s.mem a 40) (hb : SmallRange s.mem b 40)
    (hr : SmallRange s.mem r 32) (hq : SmallRange s.mem q 32)
    (he : Registers E a b r q) (hqr : q.id ≠ r.id) (hrb : r.id ≠ b.id) :
    ∃ F, Cutpoint.segment (program p g) 0 577 370 E s =
      .value (F,resultState s a b r q) ∧
      Registers F a b r q ∧ Frame 431 E F ∧
      (resultState s a b r q).WF ∧ (resultState s a b r q).alloc = s.alloc ∧
      Verifier.Execution.Dalek.ReadBytes (resultState s a b r q) r 32
        (canonicalWord (readLimbs s a)) ∧
      Verifier.Execution.Dalek.ReadBytes (resultState s a b r q) q 32
        (canonicalWord (readLimbs s b)) := by
  obtain ⟨F,hF,hframe⟩ := segment p g E s a b r q hwf ha hb hr hq he
  exact ⟨F,hF,registers_frame E F a b r q he hframe,hframe,
    result_wf s a b r q hwf,result_alloc s a b r q,
    result_comparison_inputs s a b r q hr hq hqr hrb⟩

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
