import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Startup
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Frame

/-! Actual final local-zeroization suffix, instructions 576–606. Memory reads
remain explicit; frame erasure does not require replacing them by assumed zeroes. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
set_option maxRecDepth 100000

def finalCleanupMemory (mem : MemoryState) (tmp slots : Fin 5 → Pointer) : MemoryState :=
  let m0 := mem
  let m1 := m0.storeAt (tmp 0) (0#64)
  let m2 := m1.storeAt (tmp 1) (0#64)
  let m3 := m2.storeAt (tmp 2) (0#64)
  let m4 := m3.storeAt (tmp 3) (0#64)
  let m5 := m4.storeAt (tmp 4) (0#64)
  let v456 := m5.readAt (tmp 0) 64
  let m6 := m5.storeAt (slots 0) v456
  let v457 := m6.readAt (tmp 1) 64
  let m7 := m6.storeAt (slots 1) v457
  let v458 := m7.readAt (tmp 2) 64
  let m8 := m7.storeAt (slots 2) v458
  let v459 := m8.readAt (tmp 3) 64
  let m9 := m8.storeAt (slots 3) v459
  let v460 := m9.readAt (tmp 4) 64
  let m10 := m9.storeAt (slots 4) v460
  m10

def finalCleanupEnv (E : Env program.Γ) (mem : MemoryState)
    (tmp slots : Fin 5 → Pointer) : Env program.Γ :=
  let m0 := mem
  let m1 := m0.storeAt (tmp 0) (0#64)
  let m2 := m1.storeAt (tmp 1) (0#64)
  let m3 := m2.storeAt (tmp 2) (0#64)
  let m4 := m3.storeAt (tmp 3) (0#64)
  let m5 := m4.storeAt (tmp 4) (0#64)
  let v456 := m5.readAt (tmp 0) 64
  let m6 := m5.storeAt (slots 0) v456
  let v457 := m6.readAt (tmp 1) 64
  let m7 := m6.storeAt (slots 1) v457
  let v458 := m7.readAt (tmp 2) 64
  let m8 := m7.storeAt (slots 2) v458
  let v459 := m8.readAt (tmp 3) 64
  let m9 := m8.storeAt (slots 3) v459
  let v460 := m9.readAt (tmp 4) 64
  let m10 := m9.storeAt (slots 4) v460
  E[%456 := .value v456, %457 := .value v457, %458 := .value v458, %459 := .value v459, %460 := .value v460]

theorem finalCleanup_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (tmp slots : Fin 5 → Pointer)
    (htlive : ∀ i, Fits state.mem (tmp i) 64)
    (hslive : ∀ i, Fits state.mem (slots i) 64)
    (hz : E.read (%46) = .value 0#64)
    (ht0 : E.read (%65) = .value (tmp 0))
    (hs0 : E.read (%84) = .value (slots 0))
    (ht1 : E.read (%66) = .value (tmp 1))
    (hs1 : E.read (%85) = .value (slots 1))
    (ht2 : E.read (%67) = .value (tmp 2))
    (hs2 : E.read (%86) = .value (slots 2))
    (ht3 : E.read (%68) = .value (tmp 3))
    (hs3 : E.read (%87) = .value (slots 3))
    (ht4 : E.read (%69) = .value (tmp 4))
    (hs4 : E.read (%88) = .value (slots 4))
    : List.foldlM Instr.run E ((program.entry p g).body.drop 576) state =
      .value (finalCleanupEnv E state.mem tmp slots,
        {state with mem := finalCleanupMemory state.mem tmp slots}) := by
  have htf0 := htlive 0
  have hsf0 := hslive 0
  have htf1 := htlive 1
  have hsf1 := hslive 1
  have htf2 := htlive 2
  have hsf2 := hslive 2
  have htf3 := htlive 3
  have hsf3 := hslive 3
  have htf4 := htlive 4
  have hsf4 := hslive 4
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    finalCleanupMemory, finalCleanupEnv, Operation.load, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf, hz,
    ht0, ht1, ht2, ht3, ht4, hs0, hs1, hs2, hs3, hs4, htf0, htf1, htf2, htf3, htf4, hsf0, hsf1, hsf2, hsf3, hsf4]

theorem finalCleanup_erase (mem : MemoryState) (tmp slots : Fin 5 → Pointer)
    (mark : Nat) (ht : ∀ i, mark ≤ (tmp i).id.id) (hs : ∀ i, mark ≤ (slots i).id.id) :
    (finalCleanupMemory mem tmp slots).eraseFrom mark = mem.eraseFrom mark := by
  simp only [finalCleanupMemory, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (ht _), MemoryState.storeAt_eraseFrom_of_le (hs _)]

end Agave.Ed25519.Verifier.Execution.ScalarWide
