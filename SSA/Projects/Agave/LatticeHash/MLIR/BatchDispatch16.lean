import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchGuardsRun16
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace BatchRefinement16
noncomputable abbrev input1 := BatchGuardsRun16.input1
abbrev guards_run := BatchGuardsRun16.run1

theorem guards_from_header (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[0]'(by decide)))
    (offsets : Vector (BitVec 64) 15)
    (h0 : headerInput16 A args ⟨23, rfl⟩ = PoisonOr.value offsets[0])
    (h1 : headerInput16 A args ⟨22, rfl⟩ = PoisonOr.value offsets[1])
    (h2 : headerInput16 A args ⟨21, rfl⟩ = PoisonOr.value offsets[2])
    (h3 : headerInput16 A args ⟨20, rfl⟩ = PoisonOr.value offsets[3])
    (h4 : headerInput16 A args ⟨19, rfl⟩ = PoisonOr.value offsets[4])
    (h5 : headerInput16 A args ⟨18, rfl⟩ = PoisonOr.value offsets[5])
    (h6 : headerInput16 A args ⟨17, rfl⟩ = PoisonOr.value offsets[6])
    (h7 : headerInput16 A args ⟨16, rfl⟩ = PoisonOr.value offsets[7])
    (h8 : headerInput16 A args ⟨15, rfl⟩ = PoisonOr.value offsets[8])
    (h9 : headerInput16 A args ⟨14, rfl⟩ = PoisonOr.value offsets[9])
    (h10 : headerInput16 A args ⟨13, rfl⟩ = PoisonOr.value offsets[10])
    (h11 : headerInput16 A args ⟨12, rfl⟩ = PoisonOr.value offsets[11])
    (h12 : headerInput16 A args ⟨11, rfl⟩ = PoisonOr.value offsets[12])
    (h13 : headerInput16 A args ⟨10, rfl⟩ = PoisonOr.value offsets[13])
    (h14 : headerInput16 A args ⟨9, rfl⟩ = PoisonOr.value offsets[14])
    (hl : headerInput16 A args ⟨112, rfl⟩ = PoisonOr.value 1027#64) :
    BatchGuards16.Env1 (input1 A (BatchHeader16.next16 (headerInput16 A args)).args) offsets := by
  constructor
  · change headerInput16 A args ⟨23, rfl⟩ = _
    exact h0
  · change headerInput16 A args ⟨22, rfl⟩ = _
    exact h1
  · change headerInput16 A args ⟨21, rfl⟩ = _
    exact h2
  · change headerInput16 A args ⟨20, rfl⟩ = _
    exact h3
  · change headerInput16 A args ⟨19, rfl⟩ = _
    exact h4
  · change headerInput16 A args ⟨18, rfl⟩ = _
    exact h5
  · change headerInput16 A args ⟨17, rfl⟩ = _
    exact h6
  · change headerInput16 A args ⟨16, rfl⟩ = _
    exact h7
  · change headerInput16 A args ⟨15, rfl⟩ = _
    exact h8
  · change headerInput16 A args ⟨14, rfl⟩ = _
    exact h9
  · change headerInput16 A args ⟨13, rfl⟩ = _
    exact h10
  · change headerInput16 A args ⟨12, rfl⟩ = _
    exact h11
  · change headerInput16 A args ⟨11, rfl⟩ = _
    exact h12
  · change headerInput16 A args ⟨10, rfl⟩ = _
    exact h13
  · change headerInput16 A args ⟨9, rfl⟩ = _
    exact h14
  · change A ⟨86, rfl⟩ = _
    exact hl

private theorem guards_from_target (A : agave_batch_16.cfgCtx.Valuation)
    (cv : Blake3Compression.CV (Blake3Compression.Lanes 16))
    (offsets : Vector (BitVec 64) 16)
    (hl : A ⟨86, rfl⟩ = PoisonOr.value 1027#64) :
    BatchGuards16.Env1 (input1 A
      (BatchHeader16.next16 (headerInput16 A (headerTarget16 cv offsets).args)).args)
      (Vector.ofFn fun i : Fin 15 => offsets[15-i.val]) := by
  apply guards_from_header A (headerTarget16 cv offsets).args
    (Vector.ofFn fun i : Fin 15 => offsets[15-i.val])
  all_goals first | exact hl | (simp only [Vector.getElem_ofFn]; rfl)

/-- The remaining fifteen bounds are derived from the same scalar invariant;
no guard or successful execution hypothesis is assumed. -/
theorem header_guards_env (s : GlobalState) (src len out sched panic : Pointer)
    (lengthsLo lengthsHi : Vector (BitVec 64) 8) (ms : Fin 16 → AgaveConcrete.Message)
    (iteration : Nat) :
    BatchGuards16.Env1
      (input1 (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi)
        (BatchHeader16.next16 (headerAt16Val
          (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi) ms iteration)).args)
      (Vector.ofFn fun i : Fin 15 =>
        BitVec.ofNat 64 (batchOffset (ms ⟨15-i.val, by omega⟩).length iteration)) := by
  have h := guards_from_target
    (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi)
    (fun w lane => (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
      (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv w)
    (Vector.ofFn fun lane => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))
    (by rfl)
  simp only [Vector.getElem_ofFn] at h
  convert h using 1
  all_goals rfl

/-- Execute both actual bounds blocks to the sixteen source loads. The
message length restriction alone excludes every panic edge on this path. -/
theorem header_to_loads (s u : GlobalState) (src len out sched panic : Pointer)
    (lengthsLo lengthsHi : Vector (BitVec 64) 8) (ms : Fin 16 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024) :
    StateT.run (agave_batch_16.blocks.run
      (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi) (headerAt16 ms iteration)) u =
    StateT.run (agave_batch_16.blocks.run
      (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi)
      (BatchGuards16.next1
        (input1 (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi)
          (BatchHeader16.next16 (headerAt16Val
            (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi) ms iteration)).args))) u := by
  let A := BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi
  let offsets := Vector.ofFn fun i : Fin 15 =>
    BitVec.ofNat 64 (batchOffset (ms ⟨15-i.val, by omega⟩).length iteration)
  have hb : ∀ i : Fin 15, offsets[i].toNat ≤ 960 := by
    intro i
    simp only [offsets, Fin.getElem_fin, Vector.getElem_ofFn, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms _))
  have h := guards_run A (BatchHeader16.next16 (headerAt16Val A ms iteration)).args u offsets
    (header_guards_env s src len out sched panic lengthsLo lengthsHi ms iteration) hb
  have heta (V : BatchHeader16.Input16.Valuation) :
      (⟨1, rfl, (BatchHeader16.next16 V).args⟩ : SuccArgs agave_batch_16.cfgSigs) =
        BatchHeader16.next16 V := rfl
  rw [heta] at h
  rw [headerAt16_run s u src len out sched panic lengthsLo lengthsHi ms iteration hms]
  exact h

end BatchRefinement16
end AgaveLatticeHash.MLIR
