import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Program
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Arithmetic
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.EntryTail

/-! Exact finalizer entry: read counters, append the mandatory 0x80 byte, and
select one or two blocks using the source comparison. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem byte_index (n : Nat) (hn : n < 2 ^ 63) :
    Operation.gepInboundsIndex 1 (.value (BitVec.ofNat 64 n)) = .value (n : Int) := by
  have hn64 : n < 2 ^ 64 := by omega
  have hnat : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have hint : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    simpa only [hnat] using (BitVec.toInt_eq_toNat_of_lt (x := BitVec.ofNat 64 n) (by rw [hnat]; omega))
  have h := Operation.gepInboundsIndex_eq 1 (BitVec.ofNat 64 n)
    (by simp only [Operation.GepSignedRange, hint]; omega)
    (by simp only [Operation.GepSignedRange, hint, mul_one]; omega)
    (by rw [hnat]; exact hn64)
    (by simp only [BitVec.ofInt_toInt, hnat, mul_one]; exact hn64)
  simpa only [hint, Nat.cast_one, mul_one] using h

def markerMemory (m : MemoryState) (context : Pointer) (used : Nat) : MemoryState :=
  m.storeAt (context.add (BitVec.ofNat 64 used)) 128#8

def entryEnv (E : Env program.Γ) (context : Pointer) (used : Nat) (lo hi : Word) :
    Env program.Γ :=
  E[%0 := .value ((128 : BitVec 64)),
    %1 := .value ((200 : BitVec 64)),
    %2 := .value ((208 : BitVec 64)),
    %3 := .value ((216 : BitVec 64)),
    %4 := .value ((-128 : BitVec 8)),
    %5 := .value ((1 : BitVec 64)),
    %6 := .value ((112 : BitVec 64)),
    %7 := .value ((127 : BitVec 64)),
    %8 := .value ((0 : BitVec 8)),
    %9 := .value ((0 : BitVec 64)),
    %10 := .value ((120 : BitVec 64)),
    %11 := .value ((136 : BitVec 64)),
    %12 := .value ((8 : BitVec 64)),
    %13 := .value ((144 : BitVec 64)),
    %14 := .value ((16 : BitVec 64)),
    %15 := .value ((152 : BitVec 64)),
    %16 := .value ((24 : BitVec 64)),
    %17 := .value ((160 : BitVec 64)),
    %18 := .value ((32 : BitVec 64)),
    %19 := .value ((168 : BitVec 64)),
    %20 := .value ((40 : BitVec 64)),
    %21 := .value ((176 : BitVec 64)),
    %22 := .value ((48 : BitVec 64)),
    %23 := .value ((184 : BitVec 64)),
    %24 := .value ((56 : BitVec 64)),
    %25 := .value (context.add 128#64),
    %26 := .value (context.add 200#64),
    %27 := .value (BitVec.ofNat 64 used),
    %28 := .value (context.add 208#64),
    %29 := .value (lo),
    %30 := .value (context.add 216#64),
    %31 := .value (hi),
    %32 := .value (context.add (BitVec.ofNat 64 used)),
    %33 := .value (BitVec.ofNat 64 used + 1),
    %34 := .value (BitVec.ofBool ((112#64).ult (BitVec.ofNat 64 used + 1)))]

theorem entry_body (E : Env program.Γ) (state : GlobalState) (context : Pointer)
    (used : Nat) (lo hi : Word) (hcontext : E.read (%arg0) = .value context)
    (hn : used < 128) (hr : SmallRange state.mem context 224)
    (hu : state.mem.readAt (context.add 200#64) 64 = BitVec.ofNat 64 used)
    (hlo : state.mem.readAt (context.add 208#64) 64 = lo)
    (hhi : state.mem.readAt (context.add 216#64) 64 = hi) :
    List.foldlM Instr.run E program.bb0.body state =
      .value (entryEnv E context used lo hi,
        {state with mem := markerMemory state.mem context used}) := by
  have harg : E.args 0 = .value context := hcontext
  have hg128 := hr.gep (k := 128) (by decide)
  have hg200 := hr.gep (k := 200) (by decide)
  have hg208 := hr.gep (k := 208) (by decide)
  have hg216 := hr.gep (k := 216) (by decide)
  have hgused := hr.gep (k := used) (by omega)
  have hiused := byte_index used (by omega)
  have hi128 : Operation.gepInboundsIndex 1 (.value 128#64) = .value (128 : Int) := by decide
  have hi200 : Operation.gepInboundsIndex 1 (.value 200#64) = .value (200 : Int) := by decide
  have hi208 : Operation.gepInboundsIndex 1 (.value 208#64) = .value (208 : Int) := by decide
  have hi216 : Operation.gepInboundsIndex 1 (.value 216#64) = .value (216 : Int) := by decide
  have hf200 := hr.fits_add (k := 200) (count := 8) (by decide)
  have hf208 := hr.fits_add (k := 208) (count := 8) (by decide)
  have hf216 := hr.fits_add (k := 216) (count := 8) (by decide)
  have hfused := hr.fits_add (k := used) (count := 1) (by omega)
  norm_num only [Nat.cast_ofNat] at hg128 hg200 hg208 hg216
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb0, List.foldlM_cons, List.foldlM_nil, Instr.run,
    entryEnv, markerMemory, harg, hg128, hg200, hg208, hg216, hgused, hiused, hi128, hi200, hi208, hi216,
    hf200, hf208, hf216, hfused, hu, hlo, hhi,
    Operation.load, Operation.store, Operation.icmp, hadd,
    GepIndex.inboundsOffset,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem entry_choice (E : Env program.Γ) (context : Pointer) (used : Nat) (lo hi : Word)
    (hn : used < 128) :
    (entryEnv E context used lo hi).read (%34) = .value (BitVec.ofBool (decide (112 ≤ used))) := by
  have hnat : (BitVec.ofNat 64 used).toNat = used := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : used < 2 ^ 64)]
  have hcut := finish_two_blocks (BitVec.ofNat 64 used) (by rw [hnat]; exact hn)
  rw [hnat] at hcut
  have hb : (112#64).ult (BitVec.ofNat 64 used + 1) = decide (112 ≤ used) := by
    exact Bool.eq_iff_iff.mpr (by simpa using hcut)
  simpa only [entryEnv, mlir_env] using congrArg (fun b => PoisonOr.value (BitVec.ofBool b)) hb

open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes)

def longMemory (m : MemoryState) (context : Pointer) (used : Nat) : MemoryState :=
  m.storeAt (context.add (BitVec.ofNat 64 (used + 1))) ((0#8).replicate (127 - used))

def longEnv (E : Env program.Γ) (context : Pointer) (used : Nat) : Env program.Γ :=
  E[%35 := .value (context.add (BitVec.ofNat 64 (used + 1))),
    %36 := .value (BitVec.ofNat 64 (127 - used))]

/-- The first padding block is zero-filled up to byte 127 before its core call. -/
theorem long_prefix (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (E : Env program.Γ) (state : GlobalState) (context : Pointer) (used : Nat)
    (hn : used < 128) (hr : SmallRange state.mem context 224)
    (hc : E.read (%arg0) = .value context)
    (hu : E.read (%27) = .value (BitVec.ofNat 64 used))
    (hu1 : E.read (%33) = .value (BitVec.ofNat 64 (used + 1)))
    (h127 : E.read (%7) = .value 127#64) (hz : E.read (%8) = .value 0#8) :
    List.foldlM Instr.run E ((program.bb1 core).body.take 3) state =
      .value (longEnv E context used, {state with mem := longMemory state.mem context used}) := by
  have harg : E.args 0 = .value context := hc
  have hidx := byte_index (used + 1) (by omega)
  have hgep := hr.gep (k := used + 1) (by omega)
  norm_num only [Nat.cast_add, Nat.cast_one] at hgep
  have hf := hr.fits_add (k := used + 1) (count := 127 - used) (by omega)
  have hsub : 127#64 - BitVec.ofNat 64 used = BitVec.ofNat 64 (127 - used) :=
    BitVec.ofNat_sub_ofNat_of_le 127 used (by omega) (by omega)
  have hsubop : Operation.sub {} (.value 127#64) (.value (BitVec.ofNat 64 used)) =
      .value (BitVec.ofNat 64 (127 - used)) := by simp [Operation.sub, hsub]
  have hlen : (BitVec.ofNat 64 (127 - used)).toNat = 127 - used := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 127 - used < 2 ^ 64)]
  simp [program.bb1, List.foldlM_cons, List.foldlM_nil, Instr.run,
    longEnv, longMemory, harg, hc, hu, hu1, h127, hz, hidx, hgep, hf, hsubop, hlen,
    Operation.memset, GepIndex.inboundsOffset,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem last_sub (n : Nat) (hn : n ≤ 112) :
    Operation.sub {nsw := true, nuw := true} (.value 112#64)
      (.value (BitVec.ofNat 64 n)) = .value (BitVec.ofNat 64 (112 - n)) := by
  interval_cases n <;> decide

def lastMemory (m : MemoryState) (context : Pointer) (n : Nat) (lo hi : Word) : MemoryState :=
  let cleared := m.storeAt (context.add (BitVec.ofNat 64 n)) ((0#8).replicate (112 - n))
  let high := cleared.storeAt (context.add 112#64) (swapBytes hi)
  high.storeAt (context.add 120#64) (swapBytes lo)

def lastEnv (E : Env program.Γ) (context : Pointer) (n : Nat) (lo hi : Word) : Env program.Γ :=
  E[%38 := .value (context.add (BitVec.ofNat 64 n)),
    %39 := .value (BitVec.ofNat 64 (112 - n)), %40 := .value (swapBytes hi),
    %41 := .value (context.add 112#64), %42 := .value (swapBytes lo),
    %43 := .value (context.add 120#64)]

/-- The final block prefix is zero-filled and receives the high then low
byte-swapped length words, exactly as in the imported source. -/
theorem last_prefix (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (E : Env program.Γ) (state : GlobalState) (context : Pointer) (n : Nat) (lo hi : Word)
    (hn : n ≤ 112) (hr : SmallRange state.mem context 224)
    (hc : E.read (%arg0) = .value context)
    (h112 : E.read (%6) = .value 112#64) (hz : E.read (%8) = .value 0#8)
    (h120 : E.read (%10) = .value 120#64) (hlo : E.read (%29) = .value lo)
    (hhi : E.read (%31) = .value hi) (hnreg : E.read (%37) = .value (BitVec.ofNat 64 n)) :
    List.foldlM Instr.run E ((program.bb2 core).body.take 9) state =
      .value (lastEnv E context n lo hi, {state with mem := lastMemory state.mem context n lo hi}) := by
  have harg : E.args 0 = .value context := hc
  have hidx := byte_index n (by omega)
  have hidx112 : Operation.gepInboundsIndex 1 (.value 112#64) = .value (112 : Int) := by decide
  have hidx120 : Operation.gepInboundsIndex 1 (.value 120#64) = .value (120 : Int) := by decide
  have hgep := hr.gep (k := n) (by omega)
  have hf := hr.fits_add (k := n) (count := 112 - n) (by omega)
  have hr1 := hr.storeAt (context.add (BitVec.ofNat 64 n)) ((0#8).replicate (112 - n))
  have hg112 := hr1.gep (k := 112) (by decide)
  have hf112 := hr1.fits_add (k := 112) (count := 8) (by decide)
  have hr2 := hr1.storeAt (context.add 112#64) (swapBytes hi)
  have hg120 := hr2.gep (k := 120) (by decide)
  have hf120 := hr2.fits_add (k := 120) (count := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hg112 hg120
  have hsub := last_sub n hn
  have hlen : (BitVec.ofNat 64 (112 - n)).toNat = 112 - n := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 112 - n < 2 ^ 64)]
  have hswap (word : Word) : Operation.bswap (.value word) = .value (swapBytes word) := rfl
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    lastEnv, lastMemory, harg, hc, h112, hz, h120, hlo, hhi, hnreg,
    hidx, hidx112, hidx120, hgep, hf, hsub, hlen, hg112, hf112, hg120, hf120,
    Operation.memset, Operation.store, hswap, GepIndex.inboundsOffset,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
