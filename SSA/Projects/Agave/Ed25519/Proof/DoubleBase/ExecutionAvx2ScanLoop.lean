import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Scan
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame

/-!
# Complete descending scan of the imported AVX2 CFG

The two live byte arrays justify every load. The induction executes the real
blocks 16 and 17, including their zero fallback, and terminates at block 15
with the source `startIndex`. It assumes no property of point helpers, table
contents, digit bounds, or a successful run. The continuation remains the
original imported function, rather than a substitute interpreter.
-/

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

/-- Registers initialized before the scan and never changed by it. -/
structure ScanReady (E : ⟪avx2Kernel.Γ⟫) (a b : Pointer) : Prop where
  zeroByte : E.read (%1) = .value 0#8
  zeroWord : E.read (%4) = .value 0#64
  decrement : E.read (%19) = .value (-1 : BitVec 64)
  digitsA : E.read (%266) = .value a
  digitsB : E.read (%265) = .value b

def memoryDigits (s : GlobalState) (p : Pointer) : Digits :=
  fun i => (s.mem.readAt (p.add (BitVec.ofNat 64 i)) 8).toInt

theorem byte_toInt_zero : ∀ x : BitVec 8, x.toInt = 0 ↔ x = 0#8 := by
  decide +kernel

theorem scanAInput_of_ready (E : ⟪avx2Kernel.Γ⟫) (a b : Pointer)
    (pos : Fin 256) (h : ScanReady E a b)
    (hcursor : E.read (%411) = .value (BitVec.ofNat 64 (pos.val + 1))) :
    scanAInput E a pos = E := by
  unfold scanAInput
  rw [Env.write_of_read E (%1) h.zeroByte, Env.write_of_read E (%19) h.decrement,
    Env.write_of_read E (%266) h.digitsA, Env.write_of_read E (%411) hcursor]

theorem scanBInput_of_ready (E : ⟪avx2Kernel.Γ⟫) (a b : Pointer)
    (pos : Fin 256) (h : ScanReady E a b)
    (hcursor : E.read (%412) = .value (BitVec.ofNat 64 pos.val)) :
    scanBInput E b pos = E := by
  unfold scanBInput
  rw [Env.write_of_read E (%1) h.zeroByte, Env.write_of_read E (%4) h.zeroWord,
    Env.write_of_read E (%265) h.digitsB, Env.write_of_read E (%412) hcursor]

theorem ScanReady.afterA (h : ScanReady E a b) (pos : Fin 256) (digit : BitVec 8) :
    ScanReady (scanAResult E a pos digit) a b := by
  rcases h with ⟨h1, h4, h19, ha, hb⟩
  constructor <;> simp_all [scanAResult, scanAInput, mlir_env]

theorem ScanReady.afterB (h : ScanReady E a b) (pos : Fin 256) (digit : BitVec 8) :
    ScanReady (scanBResult E b pos digit) a b := by
  rcases h with ⟨h1, h4, h19, ha, hb⟩
  constructor <;> simp_all [scanBResult, scanBInput, mlir_env]

theorem ScanReady.back (h : ScanReady E a b) (n : Nat) :
    ScanReady (E[%411 := .value (BitVec.ofNat 64 n)]) a b := by
  rcases h with ⟨h1, h4, h19, ha, hb⟩
  constructor <;> simp_all [mlir_env]

theorem scanAResult_frame (E : ⟪avx2Kernel.Γ⟫) (a b : Pointer)
    (pos : Fin 256) (digit : BitVec 8) (h : ScanReady E a b)
    (hcursor : E.read (%411) = .value (BitVec.ofNat 64 (pos.val + 1))) :
    RegisterFrame 411 421 E (scanAResult E a pos digit) := by
  unfold scanAResult
  rw [scanAInput_of_ready E a b pos h hcursor]
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem scanBResult_frame (E : ⟪avx2Kernel.Γ⟫) (a b : Pointer)
    (pos : Fin 256) (digit : BitVec 8) (h : ScanReady E a b)
    (hcursor : E.read (%412) = .value (BitVec.ofNat 64 pos.val)) :
    RegisterFrame 411 421 E (scanBResult E b pos digit) := by
  unfold scanBResult
  rw [scanBInput_of_ready E a b pos h hcursor]
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

/-- Total scan, parameterized by its initial highest index. The state and
function arguments are preserved exactly, including the all-zero case. -/
theorem scan_loop_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (a b : Pointer) (s : GlobalState)
    (ha : Buffer s.mem a 256) (hb : Buffer s.mem b 256)
    (n : Nat) (hn : n < 256) (E : ⟪avx2Kernel.Γ⟫)
    (hready : ScanReady E a b)
    (hcursor : E.read (%411) = .value (BitVec.ofNat 64 (n + 1))) :
    ∃ E' : ⟪avx2Kernel.Γ⟫,
      (avx2Kernel p g).runFrom E 16 s = (avx2Kernel p g).runFrom E' 15 s ∧
      ScanReady E' a b ∧ RegisterFrame 411 421 E E' ∧
      E'.read (%412) = .value (BitVec.ofNat 64
        (startIndex (memoryDigits s a) (memoryDigits s b) n)) := by
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    let pos : Fin 256 := ⟨n, hn⟩
    let da := s.mem.readAt (a.add (BitVec.ofNat 64 n)) 8
    let db := s.mem.readAt (b.add (BitVec.ofNat 64 n)) 8
    let EA := scanAResult E a pos da
    have hEA : ScanReady EA a b := hready.afterA pos da
    have hframeA : RegisterFrame 411 421 E EA :=
      scanAResult_frame E a b pos da hready hcursor
    have hEAindex : EA.read (%412) = .value (BitVec.ofNat 64 n) := by
      simp [EA, scanAResult, mlir_env, pos]
    have hrunA := scanA_run p g E a pos da s ha rfl
    rw [scanAInput_of_ready E a b pos hready hcursor] at hrunA
    by_cases hda : da = 0#8
    · rw [if_pos hda] at hrunA
      let EB := scanBResult EA b pos db
      have hEB : ScanReady EB a b := hEA.afterB pos db
      have hframeB : RegisterFrame 411 421 EA EB :=
        scanBResult_frame EA a b pos db hEA hEAindex
      have hEBindex : EB.read (%412) = .value (BitVec.ofNat 64 n) := by
        simp [EB, scanBResult, scanBInput, mlir_env, pos]
      have hrunB := scanB_run p g EA b pos db s hb rfl
      rw [scanBInput_of_ready EA a b pos hEA hEAindex] at hrunB
      by_cases hstop : db ≠ 0#8 ∨ n = 0
      · have hstop' : db ≠ 0#8 ∨ pos.val = 0 := hstop
        rw [if_pos hstop'] at hrunB
        refine ⟨EB, hrunA.trans hrunB, hEB, hframeA.trans hframeB, ?_⟩
        have hindex : startIndex (memoryDigits s a) (memoryDigits s b) n = n := by
          rcases hstop with hdb | rfl
          · cases n with
            | zero => rfl
            | succ k =>
              have hnonzero : memoryDigits s b (k + 1) ≠ 0 := by
                simpa [memoryDigits, db, byte_toInt_zero] using hdb
              exact startIndex_top _ _ k (Or.inr hnonzero)
          · rfl
        rw [hindex]
        exact hEBindex
      · have hstop' : ¬(db ≠ 0#8 ∨ pos.val = 0) := hstop
        rw [if_neg hstop'] at hrunB
        let EN := EB[%411 := .value (BitVec.ofNat 64 n)]
        have hpositive : 0 < n := by omega
        have hpred : n - 1 < n := by omega
        have hnext : EN.read (%411) = .value (BitVec.ofNat 64 ((n - 1) + 1)) := by
          have hn' : (n - 1) + 1 = n := by omega
          simp [EN, hn', mlir_env]
        obtain ⟨E', hrun, hready', hframe, hindex⟩ :=
          ih (n - 1) hpred (by omega) EN (hEB.back n) hnext
        have hframeN : RegisterFrame 411 421 EB EN :=
          (RegisterFrame.refl 411 421 EB).write _ _ (by decide)
        refine ⟨E', hrunA.trans (hrunB.trans hrun), hready',
          hframeA.trans (hframeB.trans (hframeN.trans hframe)), ?_⟩
        have hscan : startIndex (memoryDigits s a) (memoryDigits s b) n =
            startIndex (memoryDigits s a) (memoryDigits s b) (n - 1) := by
          have hdb : db = 0#8 := by tauto
          cases n with
          | zero => omega
          | succ k =>
            have hzA : memoryDigits s a (k + 1) = 0 := by
              simpa [memoryDigits, da, byte_toInt_zero] using hda
            have hzB : memoryDigits s b (k + 1) = 0 := by
              simpa [memoryDigits, db, byte_toInt_zero] using hdb
            simp [startIndex, hzA, hzB]
        rw [hscan]
        exact hindex
    · rw [if_neg hda] at hrunA
      refine ⟨EA, hrunA, hEA, hframeA, ?_⟩
      have hindex : startIndex (memoryDigits s a) (memoryDigits s b) n = n := by
        cases n with
        | zero => rfl
        | succ k =>
          have hnonzero : memoryDigits s a (k + 1) ≠ 0 := by
            simpa [memoryDigits, da, byte_toInt_zero] using hda
          exact startIndex_top _ _ k (Or.inl hnonzero)
      rw [hindex]
      exact hEAindex

/-- The two NAF arrays produced by the emitter determine the exact source
start index. No premise says that any scanned digit is nonzero. -/
theorem scan_naf_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (a b : Pointer) (x y : Nat) (s : GlobalState)
    (ha : Buffer s.mem a 256) (hb : Buffer s.mem b 256)
    (hreadA : ∀ i : Fin 256, s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8 =
      Execution.nafByte 5 x i.val)
    (hreadB : ∀ i : Fin 256, s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8 =
      Execution.nafByte 8 y i.val)
    (E : ⟪avx2Kernel.Γ⟫) (hready : ScanReady E a b)
    (hcursor : E.read (%411) = .value 256#64) :
    ∃ E' : ⟪avx2Kernel.Γ⟫,
      (avx2Kernel p g).runFrom E 16 s = (avx2Kernel p g).runFrom E' 15 s ∧
      ScanReady E' a b ∧ RegisterFrame 411 421 E E' ∧
      E'.read (%412) = .value (BitVec.ofNat 64
        (startIndex (nafDigits 5 x) (nafDigits 8 y) 255)) := by
  obtain ⟨E', hrun, hr, hframe, hi⟩ :=
    scan_loop_run p g a b s ha hb 255 (by decide) E hready hcursor
  refine ⟨E', hrun, hr, hframe, ?_⟩
  have hindex := startIndex_congr (memoryDigits s a) (memoryDigits s b)
    (nafDigits 5 x) (nafDigits 8 y) 255
    (fun i hi => by
      unfold memoryDigits
      rw [hreadA ⟨i, by omega⟩, Execution.nafByte_toInt 5 (Or.inl rfl)])
    (fun i hi => by
      unfold memoryDigits
      rw [hreadB ⟨i, by omega⟩, Execution.nafByte_toInt 8 (Or.inr rfl)])
  rwa [hindex] at hi

end Agave.Ed25519.DoubleBase.ExecutionAvx2
