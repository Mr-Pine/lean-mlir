import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Startup
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Frame

/-! The actual zeroization/copy phase before serialization, instructions 405–442. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
set_option maxRecDepth 100000

def inputCleanupMemory (mem : MemoryState) (scratch : Fin 8 → Pointer)
    (zeroLow zeroHigh low high : Pointer) : MemoryState :=
  let m0 := mem
  let m1 := m0.storeAt (scratch 0) (0#64)
  let m2 := m1.storeAt (scratch 1) (0#64)
  let m3 := m2.storeAt (scratch 2) (0#64)
  let m4 := m3.storeAt (scratch 3) (0#64)
  let m5 := m4.storeAt (scratch 4) (0#64)
  let m6 := m5.storeAt (scratch 5) (0#64)
  let m7 := m6.storeAt (scratch 6) (0#64)
  let m8 := m7.storeAt (scratch 7) (0#64)
  let m9 := m8.storeAt zeroLow (0#320)
  let m10 := m9.storeAt low (m9.readAt zeroLow 320)
  let m11 := m10.storeAt zeroHigh (0#320)
  let m12 := m11.storeAt high (m11.readAt zeroHigh 320)
  m12

theorem inputCleanup_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (scratch : Fin 8 → Pointer) (zeroLow zeroHigh low high : Pointer)
    (hslive : ∀ i, Fits state.mem (scratch i) 64)
    (hzllive : Fits state.mem zeroLow 320) (hzhlive : Fits state.mem zeroHigh 320)
    (hllive : Fits state.mem low 320) (hhlive : Fits state.mem high 320)
    (hdl : low.id ≠ zeroLow.id) (hdh : high.id ≠ zeroHigh.id)
    (hz : E.read (%46) = .value 0#64) (hb : E.read (%51) = .value 0#8)
    (h40 : E.read (%4) = .value 40#64)
    (hzl : E.read (%71) = .value zeroLow) (hzh : E.read (%70) = .value zeroHigh)
    (hl : E.read (%75) = .value low) (hh : E.read (%74) = .value high)
    (hs0 : E.read (%76) = .value (scratch 0))
    (hs1 : E.read (%77) = .value (scratch 1))
    (hs2 : E.read (%78) = .value (scratch 2))
    (hs3 : E.read (%79) = .value (scratch 3))
    (hs4 : E.read (%80) = .value (scratch 4))
    (hs5 : E.read (%81) = .value (scratch 5))
    (hs6 : E.read (%82) = .value (scratch 6))
    (hs7 : E.read (%83) = .value (scratch 7))
    : List.foldlM Instr.run E (((program.entry p g).body.drop 405).take 38) state =
      .value (E, {state with mem := inputCleanupMemory state.mem scratch zeroLow zeroHigh low high}) := by
  have hdl' : (Range.of low 320).Disjoint (Range.of zeroLow 320) := Range.disjoint_of_id_ne hdl
  have hdh' : (Range.of high 320).Disjoint (Range.of zeroHigh 320) := Range.disjoint_of_id_ne hdh
  have hzrep : (0#8).replicate 40 = 0#320 := by decide
  have hf0 := hslive 0
  have hf1 := hslive 1
  have hf2 := hslive 2
  have hf3 := hslive 3
  have hf4 := hslive 4
  have hf5 := hslive 5
  have hf6 := hslive 6
  have hf7 := hslive 7
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputCleanupMemory, Operation.store, Operation.memset, Operation.memcpy,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf, hz, hb, h40,
    hzl, hzh, hl, hh, hzllive, hzhlive, hllive, hhlive, hdl', hdh', hzrep,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7]

theorem inputCleanup_erase (mem : MemoryState) (scratch : Fin 8 → Pointer)
    (zeroLow zeroHigh low high : Pointer) (mark : Nat)
    (hs : ∀ i, mark ≤ (scratch i).id.id)
    (hzl : mark ≤ zeroLow.id.id) (hzh : mark ≤ zeroHigh.id.id)
    (hl : mark ≤ low.id.id) (hh : mark ≤ high.id.id) :
    (inputCleanupMemory mem scratch zeroLow zeroHigh low high).eraseFrom mark =
      mem.eraseFrom mark := by
  simp only [inputCleanupMemory, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (hs _), MemoryState.storeAt_eraseFrom_of_le hzl,
    MemoryState.storeAt_eraseFrom_of_le hzh, MemoryState.storeAt_eraseFrom_of_le hl,
    MemoryState.storeAt_eraseFrom_of_le hh]

end Agave.Ed25519.Verifier.Execution.ScalarWide
