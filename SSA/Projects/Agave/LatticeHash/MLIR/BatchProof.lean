/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.BatchControl
import SSA.Projects.Agave.LatticeHash.Equivalence
import SSA.Projects.SLLVM.Dialect.Semantics.ArithSemantics
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchEntry
import SSA.Projects.Firedancer.MLIR.DenoteStep

/-!
Actual header/guard/exit block execution and arithmetic obligations for the
compiler-emitted batch CFGs. These results do not assert a full CFG refinement.
In particular the reachability invariant, memory relation and compression
block denotations must still be established before composing a batch theorem.
-/
namespace AgaveLatticeHash.MLIR

open AgaveBatchControl
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The offset held by each lane at the loop header, including stalled lanes. -/
def batchOffset (len iteration : Nat) : Nat :=
  64 * min iteration (rootIndex len)

theorem batchOffset_le_960 (len iteration : Nat) (hlen : len ≤ 1024) :
    batchOffset len iteration ≤ 960 := by
  have := rootIndex_lt16 len hlen
  have := Nat.min_le_right iteration (rootIndex len)
  unfold batchOffset
  omega

/-- Both AVX2 loads fit in the fixed 1024-byte lane slot, including the
second 32-byte load. AVX512's single 64-byte load has the same endpoint. -/
theorem batchOffset_load_bounds (len iteration : Nat) (hlen : len ≤ 1024) :
    batchOffset len iteration + 32 ≤ 1024 ∧
    batchOffset len iteration + 64 ≤ 1024 := by
  have := batchOffset_le_960 len iteration hlen
  omega

/-- The exact unsigned comparisons guarding the source's panic block are
false for any offset admitted by the header invariant. -/
theorem batchOffset_panic_guards (len iteration : Nat) (hlen : len ≤ 1024) :
    ¬1027 < batchOffset len iteration ∧ ¬995 < batchOffset len iteration := by
  have := batchOffset_le_960 len iteration hlen
  omega

/-- A live lane advances; a lane already at its root retains its offset. -/
theorem batchOffset_next (len iteration : Nat) :
    batchOffset len (iteration + 1) =
      if batchOffset len iteration + 64 < len then
        batchOffset len iteration + 64 else batchOffset len iteration := by
  have h := active_iff_before_root len iteration
  unfold batchOffset at *
  split <;> omega

/-- At iteration fifteen every legal lane is at its root block. This bounds
backedges even when lanes have different lengths. -/
theorem batchOffset_terminal (len : Nat) (hlen : len ≤ 1024) :
    len ≤ batchOffset len 15 + 64 := by
  have := rootIndex_lt16 len hlen
  have := rootIndex_bounds len
  unfold batchOffset
  omega

/-- The word-address calculation used by the emitted GEPs is exact. -/
theorem batchOffset_word_address (len iteration : Nat) :
    4 * (batchOffset len iteration / 4) = batchOffset len iteration := by
  unfold batchOffset
  omega

/-- Every schedule-row access in either seven-round loop is within its
896-byte immutable global, including the final eight-byte entry. -/
theorem batch_schedule_bounds (round word : Nat) (hr : round < 7) (hw : word < 16) :
    128 * round + 8 * word + 8 ≤ 896 := by omega

/-- The two AVX2 half-output stores, or the single AVX512 store, stay within
one 2048-byte accumulator during all thirty-two output iterations. -/
theorem batch_output_bounds (counter : Nat) (hc : counter < 32) :
    64 * counter + 32 ≤ 2048 ∧ 64 * counter + 64 ≤ 2048 := by omega

/-- Unsigned i64 comparisons as used by `llvm.icmp ugt`; the bounds also
exclude wrapping while materializing the offset. -/
theorem batchOffset_bv_panic_guards (len iteration : Nat) (hlen : len ≤ 1024) :
    BitVec.ult (1027#64) (BitVec.ofNat 64 (batchOffset len iteration)) = false ∧
    BitVec.ult (995#64) (BitVec.ofNat 64 (batchOffset len iteration)) = false := by
  have hb := batchOffset_le_960 len iteration hlen
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  constructor <;> simp <;> omega

/-- The actual poison-aware LLVM comparison returns a definite false value
at both compiler-emitted panic checks. -/
theorem batchOffset_llvm_panic_guards (len iteration : Nat) (hlen : len ≤ 1024) :
    LLVM.icmp .ugt (.value (BitVec.ofNat 64 (batchOffset len iteration)))
      (.value 1027#64) = .value 0#1 ∧
    LLVM.icmp .ugt (.value (BitVec.ofNat 64 (batchOffset len iteration)))
      (.value 995#64) = .value 0#1 := by
  obtain ⟨hfirst, hsecond⟩ := batchOffset_bv_panic_guards len iteration hlen
  simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hfirst, hsecond]

/-- The header's active-lane comparison agrees with the root-block index,
including zero-length messages and lanes stalled while other lanes advance. -/
theorem batchOffset_llvm_active (len iteration : Nat) (hlen : len ≤ 1024) :
    LLVM.icmp .ugt (.value (BitVec.ofNat 64 len))
      (.value (BitVec.ofNat 64 (batchOffset len iteration + 64))) =
      .value (BitVec.ofBool (decide (iteration < rootIndex len))) := by
  have hoff := batchOffset_le_960 len iteration hlen
  have ha := active_iff_before_root len iteration
  change (¬len ≤ batchOffset len iteration + 64 ↔ iteration < rootIndex len) at ha
  have hl : len % 18446744073709551616 = len := Nat.mod_eq_of_lt (by omega)
  have ho : (batchOffset len iteration + 64) % 18446744073709551616 =
      batchOffset len iteration + 64 := Nat.mod_eq_of_lt (by omega)
  have heq : (batchOffset len iteration + 64 < len) = (iteration < rootIndex len) :=
    propext (by omega)
  simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, BitVec.toNat_ofNat, hl, ho, heq]

/-- The actual compiler-emitted AVX2 exit block returns normally and leaves
memory unchanged. This executes its lifetime-end marker and return. -/
theorem agave_batch_8_exit (V : agave_batch_8.cfgCtx.Valuation) (s : GlobalState) :
    StateT.run (agave_batch_8.cfgBlock_25.denote V) s =
      .value ((V, .inl []ₕ), s) := by
  simp only [agave_batch_8.cfgBlock_25, BlockCom.run_denote_lifetime]
  rfl

abbrev Header8Ctx := Ctxt.ofList
  [SLLVM.Ty.arith (.vector 8 (.bitvec 64)),
   SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)),
   SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)),
   SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)),
   SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64))] ++
  agave_batch_8.cfgCtx
/-- Execute the actual AVX2 header, including all vector arithmetic and the
lifetime marker. The zero/index-limit facts come from entry initialization;
the lane-offset bound is the loop invariant. Thus its first bounds check
cannot enter the panic block, and this step preserves the memory state. -/
theorem agave_batch_8_header_normal (V : Header8Ctx.Valuation) (s : GlobalState)
    (off : BitVec 64)
    (hz : V ⟨74, rfl⟩ = (PoisonOr.value 0#64))
    (hl : V ⟨61, rfl⟩ = (PoisonOr.value 1027#64))
    (ho : (show Vector (LLVM.IntW 64) 8 from V ⟨0, rfl⟩)[0] = PoisonOr.value off)
    (hb : off.toNat ≤ 960) :
    ∃ V' t, StateT.run (agave_batch_8.cfgBlock_0.denote V) s =
      .value ((V', .inr t), s) ∧ t.idx = 10 := by
  denote_step_all v
  simp only [BlockCom.run_denote_lifetime]
  denote_step_all v
  denote_eval v 10 26
  have e10 : v10 = PoisonOr.value off := by
    change v10 = LLVM.Ty.extractelement (l := 8) (e := .bitvec 64)
      (V ⟨0, rfl⟩) (V ⟨74, rfl⟩) at hv10
    rw [hz] at hv10
    change v10 = (show Vector (LLVM.IntW 64) 8 from V ⟨0, rfl⟩)[0] at hv10
    exact hv10.trans ho
  have e26 : v26 = PoisonOr.value 0#1 := by
    rw [hv26, e10, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  simp [e26, BlockCom.denote, Terminator.denote, Target.denote]


private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs} (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Guard8Ctx := blockInput agave_batch_8.cfgBlock_16
/-- The final first-half load guard also excludes the actual panic target
when lane seven's offset satisfies the header invariant. -/
theorem agave_batch_8_last_load_guard (V : Guard8Ctx.Valuation) (s : GlobalState) (off : BitVec 64)
    (ho : V ⟨7, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨87, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960) :
    ∃ V' t, StateT.run (agave_batch_8.cfgBlock_16.denote V) s =
      .value ((V', .inr t), s) ∧ t.idx = 1 := by
  denote_step_all v
  denote_eval v 0 0
  have e : v0 = PoisonOr.value 0#1 := by
    rw [hv0, ho, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  simp [e, BlockCom.denote, Terminator.denote, Target.denote]

private abbrev blockOutput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γout

/-- The normal successor forwards every live value, including six loaded rows. -/
noncomputable def firstHalfGuardNext8 (V : Guard8Ctx.Valuation) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨1, rfl, V ⟨34, rfl⟩ ::ₕ
    V ⟨33, rfl⟩ ::ₕ
    V ⟨32, rfl⟩ ::ₕ
    V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
    V ⟨15, rfl⟩ ::ₕ
    V ⟨14, rfl⟩ ::ₕ
    V ⟨13, rfl⟩ ::ₕ
    V ⟨12, rfl⟩ ::ₕ
    V ⟨11, rfl⟩ ::ₕ
    V ⟨10, rfl⟩ ::ₕ
    V ⟨9, rfl⟩ ::ₕ
    V ⟨8, rfl⟩ ::ₕ
    V ⟨7, rfl⟩ ::ₕ
    V ⟨6, rfl⟩ ::ₕ
    V ⟨5, rfl⟩ ::ₕ
    V ⟨4, rfl⟩ ::ₕ
    V ⟨3, rfl⟩ ::ₕ
    V ⟨2, rfl⟩ ::ₕ
    V ⟨1, rfl⟩ ::ₕ
    V ⟨0, rfl⟩ ::ₕ .nil⟩

/-- Continuation form of the last guard: the complete payload is retained
for composition with the final two first-half loads. -/
theorem agave_batch_8_last_load_guard_continue {α : Type}
    (V : Guard8Ctx.Valuation) (s : GlobalState) (off : BitVec 64)
    (ho : V ⟨7, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨87, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (k : (blockOutput agave_batch_8.cfgBlock_16).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_16.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ V, .inr (firstHalfGuardNext8 V))) s := by
  denote_step_all v
  denote_eval v 0 0
  have e : v0 = PoisonOr.value 0#1 := by
    rw [hv0, ho, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

noncomputable def initialHeader8 (s : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) : Header8Ctx.Valuation :=
  Ctxt.Valuation.ofHVector BatchEntry.header8.args.reverse ++ BatchEntry.entryVal8 s src len out sched panic lengths
/-- The first loop visit produced by the checked entry takes the load path. -/
theorem agave_batch_8_initial_header_normal (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8) :
    ∃ V' t, StateT.run (agave_batch_8.cfgBlock_0.denote
      (initialHeader8 s src len out sched panic lengths)) u =
      .value ((V', .inr t), u) ∧ t.idx = 10 := by
  apply agave_batch_8_header_normal _ u 0
  · rfl
  · rfl
  · rfl
  · decide

/-- Representation of eight u32 SIMD lanes in the compiler's four u64 lanes. -/
def packCV8 (words : Fin 8 → BitVec 32) : Vector (BitVec 64) 4 :=
  Vector.ofFn fun i => words ⟨2*i.val+1, by omega⟩ ++ words ⟨2*i.val, by omega⟩

/-- Concrete phi arguments for the actual batch8 loop header. CV words are
reversed in the source phi list; each machine vector packs pairs of lanes. -/
def headerTarget8 (cv : Blake3Compression.CV (Blake3Compression.Lanes 8))
    (offsets : Vector (BitVec 64) 8) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨0, rfl, [(packCV8 (cv 7)).map PoisonOr.value,
    (packCV8 (cv 6)).map PoisonOr.value, (packCV8 (cv 5)).map PoisonOr.value,
    (packCV8 (cv 4)).map PoisonOr.value, (packCV8 (cv 3)).map PoisonOr.value,
    (packCV8 (cv 2)).map PoisonOr.value, (packCV8 (cv 1)).map PoisonOr.value,
    (packCV8 (cv 0)).map PoisonOr.value, offsets.map PoisonOr.value]ₕ⟩

theorem headerTarget8_initial :
    headerTarget8 (fun w _ => AgaveConcrete.iv w) (Vector.replicate 8 0) =
      BatchEntry.header8 := by
  unfold headerTarget8 BatchEntry.header8
  congr 10 <;> apply Vector.ext <;> intro i hi <;> interval_cases i <;> simp [packCV8, AgaveConcrete.iv, LLVM.Ty.dense] <;> decide

/-- The actual AVX512 exit block preserves memory and returns normally. -/
theorem agave_batch_16_exit (V : agave_batch_16.cfgCtx.Valuation) (s : GlobalState) :
    StateT.run (agave_batch_16.cfgBlock_12.denote V) s =
      .value ((V, .inl []ₕ), s) := by
  simp only [agave_batch_16.cfgBlock_12, BlockCom.run_denote_lifetime]
  rfl

/-- Program-point representation of the existing scalar-prefix invariant;
this introduces no new compression or loop algorithm. -/
def headerAt8 (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) :
    SuccArgs agave_batch_8.cfgSigs :=
  headerTarget8
    (fun w lane => (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
      (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv w)
    (Vector.ofFn fun lane => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))

theorem headerAt8_zero (ms : Fin 8 → AgaveConcrete.Message) :
    headerAt8 ms 0 = BatchEntry.header8 := by
  have hz : Vector.ofFn (fun (_ : Fin 8) => 0#64) = Vector.replicate 8 0#64 := by
    apply Vector.ext
    intro i hi
    simp
  simpa [hz, headerAt8, AgaveBatchControl.stateAt, AgaveBatchControl.scalarPrefix,
    batchOffset] using headerTarget8_initial

noncomputable def headerAt8Val (V : agave_batch_8.cfgCtx.Valuation)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) : Header8Ctx.Valuation :=
  Ctxt.Valuation.ofHVector (headerAt8 ms iteration).args.reverse ++ V
/-- Every represented loop iteration for legal one-chunk messages takes
the actual first load edge, with the offset bound derived from `stateAt`. -/
theorem agave_batch_8_header_at_normal (s u : GlobalState) (src len out sched panic : Pointer)
    (lengths : Vector (BitVec 64) 8)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) :
    ∃ V' t, StateT.run (agave_batch_8.cfgBlock_0.denote
      (headerAt8Val (BatchEntry.entryVal8 s src len out sched panic lengths) ms iteration)) u =
      .value ((V', .inr t), u) ∧ t.idx = 10 := by
  apply agave_batch_8_header_normal _ u (BitVec.ofNat 64 (batchOffset (ms 0).length iteration))
  · rfl
  · rfl
  · change ((Vector.ofFn fun lane : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms lane).length iteration)).map PoisonOr.value)[0] = _
    simp
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 0))

end AgaveLatticeHash.MLIR
