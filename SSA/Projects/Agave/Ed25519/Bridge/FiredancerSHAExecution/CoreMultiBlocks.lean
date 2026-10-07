import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreOuterLoop
import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold

/-! Finite outer-loop induction for any positive number of complete blocks.
The input and K table are framed from chaining-state stores; ring writes are
removed exactly at the caller's allocation mark. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

private theorem splice_overwrite {n w : Nat} (b : BitVec n) (off : Nat) (x y : BitVec w) :
    Memory.spliceBits (Memory.spliceBits b off x) off y = Memory.spliceBits b off y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getLsbD_spliceBits]
  grind

theorem storeAt_overwrite (m : MemoryState) (p : Pointer) (x y : BitVec w) :
    (m.storeAt p x).storeAt p y = m.storeAt p y := by
  cases hb : m[p.id]? with
  | none => simp [MemoryState.storeAt, hb]
  | some b =>
    simp only [MemoryState.storeAt, hb, MemoryState.getElem?_eq,
      Std.ExtHashMap.getElem?_insert_self, splice_overwrite, MemoryState.mk.injEq]
    apply Std.ExtHashMap.ext_getElem?
    intro k
    by_cases hk : p.id = k <;> simp [Std.ExtHashMap.getElem?_insert, hk]

theorem input_tail_disjoint {m : MemoryState} {chain data : Pointer} {n : Nat}
    (hd : SmallRange m data (128 * (n + 1)))
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8 * (128 * (n + 1))))) :
    (Range.of chain 512).Disjoint (Range.of (data.add 128#64) (8 * (128 * n))) := by
  have hoff : (data.add 128#64).offsetInBits = data.offsetInBits + 1024 := by
    simpa using Pointer.offsetInBits_add (hd.no_wrap (k := 128) (by omega))
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hoff, Nat.mul_add, Nat.mul_one] at hdis ⊢
  rcases hdis with hid | hleft | hright
  · exact Or.inl hid
  · exact Or.inr (Or.inl (by omega))
  · apply Or.inr ∘ Or.inr
    simpa only [Nat.reduceMul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright

theorem run_readBytes_cons (m : MemoryState) (data : Pointer) (s : State) (n : Nat) :
    Spec.run (pack s) (readBytes m data (128 * (n + 1))) =
      Spec.run (pack (compressBlock s (readBytes m data 128)))
        (readBytes m (data.add 128#64) (128 * n)) := by
  have he : 128 * (n + 1) = 128 + 128 * n := by omega
  rw [he, readBytes_append, Spec.run_append]
  · rw [Spec.run_one_block (pack s) (readBytes m data 128) (by simp [readBytes]),
      compressBlockBytes, unpack_pack]
  · simp [readBytes]

/-- Every positive outer-loop iteration is executed, with exact standard
compression over the original input bytes and exact memory after cleanup. -/
theorem core_outer_blocks (n : Nat) :
    ∀ (kp chain stack data : Pointer) (E : Env program.Γ) (before : GlobalState) (initial : State)
      (mark : Nat),
    before.WF → mark ≤ stack.id.id →
    OuterStateReady E initial → OuterPointersReady E chain data (n + 1) →
    FirstLoopReady (firstNextEnv E 0 initial) stack data kp 0 initial →
    SmallRange before.mem chain 64 → SmallRange before.mem stack 128 →
    SmallRange before.mem data (128 * (n + 1)) → SmallRange before.mem kp 640 →
    stack.id ≠ kp.id → stack.id ≠ data.id → chain.id ≠ kp.id →
    (Range.of chain 512).Disjoint (Range.of data (8 * (128 * (n + 1)))) →
    (∀ j, j < 80 → before.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0) →
    ∃ after, (program kp).runFrom E 1 before = .value (.nil, after) ∧
      after.WF ∧ after.alloc = before.alloc ∧
      after.mem.eraseFrom mark = (before.mem.eraseFrom mark).storeAt chain
        (Spec.run (pack initial) (readBytes before.mem data (128 * (n + 1)))) := by
  induction n with
  | zero =>
    intro kp chain stack data E before initial mark hwf hmark ho hp hfirst hc hs hd hk hsk hsd hck hdis htable
    obtain ⟨middle, hw, hr⟩ := core_one_from_outer kp chain stack data E before initial
      ho hp hfirst hc hs hd hk hsk hsd htable
    let result := compressBlock initial (readBytes before.mem data 128)
    refine ⟨{middle with mem := feedforwardMemory middle.mem chain result}, hr, ?_, hw.alloc, ?_⟩
    · rw [feedforwardMemory_eq _ _ (hw.smallRange hc)]
      exact (hw.wf hwf).storeAt
    · rw [feedforwardMemory_eq _ _ (hw.smallRange hc), MemoryState.eraseFrom_storeAt,
        hw.eraseFrom mark hmark]
      simp only [Nat.zero_add, Nat.mul_one]
      rw [Spec.run_one_block _ _ (by simp [readBytes]), compressBlockBytes, unpack_pack]
  | succ n ih =>
    intro kp chain stack data E before initial mark hwf hmark ho hp hfirst hc hs hd hk hsk hsd hck hdis htable
    have hd0 : SmallRange before.mem data 128 := smallRange_mono hd (by omega)
    have hbound : n + 1 + 1 < 2^63 := by have := smallRange_length_lt hd; omega
    obtain ⟨F, middle, ht, hf, hw, he⟩ := eighty_from_input stack data kp
      (firstNextEnv E 0 initial) before initial hfirst hs hd0 hk hsk hsd htable
    let result := compressBlock initial (readBytes before.mem data 128)
    let nextE := outerNextEnv (feedforwardEnv F result data (n + 1 + 1))
      result (data.add 128#64) (n + 1)
    let next : GlobalState := {middle with mem := feedforwardMemory middle.mem chain result}
    have hframe := (firstNext_frame E 0 initial).trans he
    have hstep := feedforward_backedge F middle chain data (n + 1 + 1) initial
      (roundsFrom initial (schedule (readBytes before.mem data 128)) 0 80)
      (hframe.outerState ho) hf (hframe.outerPointers hp) (hw.smallRange hc)
      (hw.smallRange hd0) (by omega) hbound
    have hnext_first : FirstLoopReady (firstNextEnv nextE 0 result)
        stack (data.add 128#64) kp 0 result := by
      simpa only [nextE, show n + 1 + 1 - 1 = n + 1 by omega] using
        outer_next_firstReady (firstNextEnv E 0 initial) F stack data kp 0 (n+1+1)
          initial result he hfirst
    have hnext_ptr : OuterPointersReady nextE chain (data.add 128#64) (n+1) := by
      simpa only [nextE, show n + 1 + 1 - 1 = n + 1 by omega] using
        outer_next_pointers F chain data (n+1+1) result (hframe.outerPointers hp)
    have hnext_mem : next.mem = middle.mem.storeAt chain (pack result) :=
      feedforwardMemory_eq _ _ (hw.smallRange hc) _
    have hnext_wf : next.WF := by
      change ({middle with mem := feedforwardMemory middle.mem chain result} : GlobalState).WF
      rw [feedforwardMemory_eq _ _ (hw.smallRange hc)]
      exact (hw.wf hwf).storeAt
    have hnext_table : ∀ j, j < 80 → next.mem.readAt (kp.add (BitVec.ofNat 64 (8*j))) 64 =
        constants.toList.getD j 0 := by
      intro j hj
      have hkdis : (Range.of chain 512).Disjoint
          (Range.of (kp.add (BitVec.ofNat 64 (8*j))) 64) := Or.inl hck
      rw [hnext_mem, MemoryState.readAt_storeAt_disjoint hkdis]
      rw [hw.readAt (kp.add (BitVec.ofNat 64 (8*j))) 64 hsk]
      exact htable j hj
    have htail : SmallRange before.mem (data.add 128#64) (128*(n+1)) :=
      smallRange_add hd (by omega)
    have htaildis := input_tail_disjoint hd hdis
    have hnextbytes : readBytes next.mem (data.add 128#64) (128*(n+1)) =
        readBytes before.mem (data.add 128#64) (128*(n+1)) := by
      rw [hnext_mem, readBytes_storeAt_disjoint _ _ _ _ _ (hw.smallRange htail) htaildis]
      exact hw.readBytes _ _ htail hsd
    obtain ⟨after, hr, hawf, haalloc, hamem⟩ := ih kp chain stack (data.add 128#64)
      nextE next result mark hnext_wf hmark (outerNext_ready _ _ _ _) hnext_ptr hnext_first
      (feedforwardMemory_live _ (hw.smallRange hc)) (feedforwardMemory_live _ (hw.smallRange hs))
      (feedforwardMemory_live _ (hw.smallRange htail)) (feedforwardMemory_live _ (hw.smallRange hk))
      hsk hsd hck htaildis hnext_table
    refine ⟨after, ?_, hawf, haalloc.trans hw.alloc, ?_⟩
    · rw [Func.runFrom_eq]
      change (program.bb1.run program.blockParams E before >>= _) = _
      rw [outer_start E before initial ho hp.zero]
      change (program kp).runFrom (firstNextEnv E 0 initial) 2 before = _
      rw [ht.runFrom kp, Func.runFrom_eq]
      change (program.bb4.run program.blockParams F middle >>= _) = _
      rw [hstep]
      exact hr
    · rw [hamem, hnextbytes, hnext_mem, MemoryState.eraseFrom_storeAt, hw.eraseFrom mark hmark,
        storeAt_overwrite, run_readBytes_cons before.mem data initial (n+1)]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
