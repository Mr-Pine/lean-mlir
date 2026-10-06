/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof
import SSA.Projects.Agave.LatticeHash.MLIR.BatchEntry16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeader16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchGuards16

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

/-- Actual AVX512 header phi payload: two offset halves, sixteen scalar
aliases and eight word-major chaining vectors. -/
def headerTarget16 (cv : Blake3Compression.CV (Blake3Compression.Lanes 16))
    (offsets : Vector (BitVec 64) 16) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨0, rfl, [ (Vector.ofFn fun i : Fin 8 => PoisonOr.value offsets[i.val + 8]),
    (Vector.ofFn fun i : Fin 8 => PoisonOr.value offsets[i.val]),
    PoisonOr.value offsets[15],
    PoisonOr.value offsets[14],
    PoisonOr.value offsets[13],
    PoisonOr.value offsets[12],
    PoisonOr.value offsets[11],
    PoisonOr.value offsets[10],
    PoisonOr.value offsets[9],
    PoisonOr.value offsets[8],
    PoisonOr.value offsets[7],
    PoisonOr.value offsets[6],
    PoisonOr.value offsets[5],
    PoisonOr.value offsets[4],
    PoisonOr.value offsets[3],
    PoisonOr.value offsets[2],
    PoisonOr.value offsets[1],
    PoisonOr.value offsets[0],
    Vector.ofFn (fun lane => PoisonOr.value (cv 7 lane)),
    Vector.ofFn (fun lane => PoisonOr.value (cv 6 lane)),
    Vector.ofFn (fun lane => PoisonOr.value (cv 5 lane)),
    Vector.ofFn (fun lane => PoisonOr.value (cv 4 lane)),
    Vector.ofFn (fun lane => PoisonOr.value (cv 3 lane)),
    Vector.ofFn (fun lane => PoisonOr.value (cv 2 lane)),
    Vector.ofFn (fun lane => PoisonOr.value (cv 1 lane)),
    Vector.ofFn (fun lane => PoisonOr.value (cv 0 lane))]ₕ⟩

theorem headerTarget16_initial :
    headerTarget16 (fun w _ => AgaveConcrete.iv w) (Vector.replicate 16 0) =
      BatchEntry16.header16 := by
  unfold headerTarget16 BatchEntry16.header16
  congr 28 <;> funext i <;> simp [AgaveConcrete.iv, LLVM.Ty.dense]

/-- Compiler program-point encoding of the scalar prefix state. -/
def headerAt16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) :
    SuccArgs agave_batch_16.cfgSigs :=
  headerTarget16
    (fun w lane => (AgaveBatchControl.stateAt AgaveConcrete.compress AgaveConcrete.iv
      (AgaveConcrete.bytes (ms lane)) (ms lane).length iteration).cv w)
    (Vector.ofFn fun lane => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))

theorem headerAt16_zero (ms : Fin 16 → AgaveConcrete.Message) :
    headerAt16 ms 0 = BatchEntry16.header16 := by
  have hz : Vector.ofFn (fun (_ : Fin 16) => 0#64) = Vector.replicate 16 0#64 := by
    apply Vector.ext
    intro i hi
    simp
  simpa [hz, headerAt16, AgaveBatchControl.stateAt, AgaveBatchControl.scalarPrefix,
    batchOffset] using headerTarget16_initial

noncomputable def headerAt16Val (A : agave_batch_16.cfgCtx.Valuation)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : BatchHeader16.Input16.Valuation :=
  Ctxt.Valuation.ofHVector (headerAt16 ms iteration).args.reverse ++ A

noncomputable def headerInput16 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[0]'(by decide))) :
    BatchHeader16.Input16.Valuation := Ctxt.Valuation.ofHVector args.reverse ++ A

theorem header_run16 (A : agave_batch_16.cfgCtx.Valuation)
    (args : HVector TyDenote.toType (agave_batch_16.cfgSigs[0]'(by decide)))
    (s : GlobalState) (off : BitVec 64)
    (ho : headerInput16 A args ⟨8, rfl⟩ = PoisonOr.value off)
    (hl : headerInput16 A args ⟨112, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960) :
    StateT.run (agave_batch_16.blocks.run A ⟨0, rfl, args⟩) s =
    StateT.run (agave_batch_16.blocks.run A (BatchHeader16.next16 (headerInput16 A args))) s := by
  denote_enter_block
  apply BatchHeader16.continue16 (headerInput16 A args) s off ho hl hb

/-- Every legal scalar-prefix state passes the first actual bounds check. -/
theorem headerAt16_run (s u : GlobalState) (src len out sched panic : Pointer)
    (lengthsLo lengthsHi : Vector (BitVec 64) 8) (ms : Fin 16 → AgaveConcrete.Message)
    (iteration : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024) :
    StateT.run (agave_batch_16.blocks.run
      (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi) (headerAt16 ms iteration)) u =
    StateT.run (agave_batch_16.blocks.run
      (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi)
      (BatchHeader16.next16 (headerAt16Val
        (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi) ms iteration))) u := by
  apply header_run16 _ _ u (BitVec.ofNat 64 (batchOffset (ms 0).length iteration))
  · rfl
  · rfl
  · simp only [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le ..) (batchOffset_le_960 _ _ (hms 0))

/-- The full compiled function enters the represented scalar-prefix invariant
at iteration zero after its checked allocations and input-length loads. -/
theorem entry_to_header16 (s : GlobalState) (hs : s.WF)
    (src len out sched panic : Pointer) (lengthsLo lengthsHi : Vector (BitVec 64) 8)
    (ms : Fin 16 → AgaveConcrete.Message)
    (hsrc : Fits s.mem src 131072) (hlen : Fits s.mem len 1024)
    (rlenLo : readWord? len 512 s.mem = some (packBits lengthsLo))
    (rlenHi : readWord? (len.withOffset 64) 512 s.mem = some (packBits lengthsHi))
    (hg : GlobalPtr s "alloc_61fb4a9344bbdaf2573accd6331d7e32" sched)
    (hgpanic : GlobalPtr s "alloc_83bddfce772813ac48c9037cf7b0770f" panic) :
    StateT.run (agave_batch_16.denote
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ)) s =
    StateT.run (agave_batch_16.blocks.run
      (BatchEntry16.entryVal16 s src len out sched panic lengthsLo lengthsHi)
      (headerAt16 ms 0)) (BatchEntry16.entryState s) := by
  rw [headerAt16_zero]
  unfold Cfg.denote
  apply BatchEntry16.entry16_continue s hs src len out sched panic lengthsLo lengthsHi
    hsrc hlen rlenLo rlenHi hg hgpanic

end AgaveLatticeHash.MLIR
