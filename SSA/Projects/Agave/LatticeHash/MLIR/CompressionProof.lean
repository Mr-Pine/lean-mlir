/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionEntry
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionEntry16
import SSA.Projects.Agave.LatticeHash.MLIR.RoundProof
import SSA.Projects.Agave.LatticeHash.MLIR.RoundProof16
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionExit
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionSpec
import SSA.Projects.Agave.LatticeHash.MLIR.GlobalsProof
import SSA.Projects.Agave.LatticeHash.MLIR.OutputRead

/-! Refinement of the actual compiler-emitted `compress_pre` CFGs. -/
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression
open CompressionEntry CompressionRound CompressionExit

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Seven applications of the actual compiled round-block execution theorem.
The scalar round schedule is fixed by the source loop's counter and exit test. -/
theorem seven_rounds8_run (V : agave_compress_pre_8.cfgCtx.Valuation)
    (msg sched : Pointer) (hV : RoundEnv8 V msg sched) (s : GlobalState)
    (initial m : State (Vector Word 8))
    (hsi : ∀ r i, Fits s.mem (CompressionRound.schedulePtr sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (agave_compress_pre_8.blocks.run V (headerAt8 0 initial)) s =
    StateT.run (agave_compress_pre_8.blocks.run V
      (exitAt8 (sevenRounds gVectors initial m))) s := by
  let s1 := roundFn gVectors initial m 0
  let s2 := roundFn gVectors s1 m 1
  let s3 := roundFn gVectors s2 m 2
  let s4 := roundFn gVectors s3 m 3
  let s5 := roundFn gVectors s4 m 4
  let s6 := roundFn gVectors s5 m 5
  let s7 := roundFn gVectors s6 m 6
  calc
    StateT.run (agave_compress_pre_8.blocks.run V (headerAt8 0 initial)) s =
        StateT.run (agave_compress_pre_8.blocks.run V (headerAt8 1 s1)) s :=
      round8_run V msg sched hV s 0 initial m (hsi 0) (hsv 0) hmi hmv
    _ =
        StateT.run (agave_compress_pre_8.blocks.run V (headerAt8 2 s2)) s :=
      round8_run V msg sched hV s 1 s1 m (hsi 1) (hsv 1) hmi hmv
    _ =
        StateT.run (agave_compress_pre_8.blocks.run V (headerAt8 3 s3)) s :=
      round8_run V msg sched hV s 2 s2 m (hsi 2) (hsv 2) hmi hmv
    _ =
        StateT.run (agave_compress_pre_8.blocks.run V (headerAt8 4 s4)) s :=
      round8_run V msg sched hV s 3 s3 m (hsi 3) (hsv 3) hmi hmv
    _ =
        StateT.run (agave_compress_pre_8.blocks.run V (headerAt8 5 s5)) s :=
      round8_run V msg sched hV s 4 s4 m (hsi 4) (hsv 4) hmi hmv
    _ =
        StateT.run (agave_compress_pre_8.blocks.run V (headerAt8 6 s6)) s :=
      round8_run V msg sched hV s 5 s5 m (hsi 5) (hsv 5) hmi hmv
    _ =
        StateT.run (agave_compress_pre_8.blocks.run V (exitAt8 s7)) s :=
      round8_run V msg sched hV s 6 s6 m (hsi 6) (hsv 6) hmi hmv
    _ = StateT.run (agave_compress_pre_8.blocks.run V
          (exitAt8 (sevenRounds gVectors initial m))) s := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Full execution of the compiled eight-lane wrapper, including entry loads,
all seven rounds, every output store, and normal return. -/
theorem agave_compress_pre_8_run (s : GlobalState)
    (out cv iv msg lo hi len flags sched : Pointer) (initial m : State (Vector Word 8))
    (hinput : CompressionInputs s.mem cv iv lo hi len flags initial)
    (hmessage : CompressionMessage s.mem msg m)
    (hglobal : ScheduleGlobal s sched) (hout : Fits s.mem out 4096) :
    StateT.run (agave_compress_pre_8.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value len, .value hi, .value lo,
       .value msg, .value iv, .value cv, .value out]ₕ)) s =
      .value ([]ₕ, {s with mem := outputMem out (sevenRounds gVectors initial m) 16 s.mem}) := by
  rw [entry8_run s out cv iv msg lo hi len flags sched initial
    hinput.cvFits hinput.ivFits hinput.loFits hinput.hiFits hinput.lenFits hinput.flagsFits
    hinput.cvRead hinput.ivRead hinput.loRead hinput.hiRead hinput.lenRead hinput.flagsRead
    hglobal.1.ptr]
  have hV : RoundEnv8 (entryVal8 out cv iv msg lo hi len flags sched initial) msg sched := by
    constructor <;> rfl
  have hsi (r : Fin 7) (i : Fin 16) :
      Fits s.mem (CompressionRound.schedulePtr sched r i) 64 := by
    simpa only [CompressionRound.schedulePtr, rowPtr, schedulePtr_two_geps] using
      scheduleGlobal_fits hglobal r i
  have hsv (r : Fin 7) (i : Fin 16) :
      readWord? (CompressionRound.schedulePtr sched r i) 64 s.mem =
        some (BitVec.ofNat 64 (schedule r i).val) := by
    simpa only [CompressionRound.schedulePtr, rowPtr, schedulePtr_two_geps] using
      scheduleGlobal_read hglobal r i
  have hptr (i : Fin 16) : messagePtr8 msg i =
      msg.withOffset (BitVec.ofNat 64 (32*i.val)) := by
    unfold messagePtr8
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_mul]
    rw [Nat.mul_comm i.val 32]
  have hmi (i : Fin 16) : Fits s.mem (messagePtr8 msg i) 256 := by
    rw [hptr]
    exact compressionSlotFits8 hmessage.fits i.val i.isLt
  have hmv (i : Fin 16) : readWord? (messagePtr8 msg i) 256 s.mem = some (packBits (m i)) := by
    rw [hptr]
    exact hmessage.read i
  rw [seven_rounds8_run _ msg sched hV s initial m hsi hsv hmi hmv]
  have hExit : ExitEnv8 (entryVal8 out cv iv msg lo hi len flags sched initial) out := by
    constructor <;> rfl
  exact exit8_run _ out _ hExit s (compressionSlotFits8 hout)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Actual compiled execution with the BLAKE3 IV and counter initialization:
every stored vector contains the independently specified scalar compression
result for each lane. No relation between SIMD lanes is assumed. -/
theorem agave_compress_pre_8_conforms (s : GlobalState)
    (out cvPtr ivPtr msgPtr lo hi lenPtr flagsPtr sched : Pointer)
    (cv : CV (Lanes 8)) (m : State (Lanes 8)) (counter : Counters 8)
    (blockLen flags : Lanes 8)
    (hinput : CompressionInputs s.mem cvPtr ivPtr lo hi lenPtr flagsPtr
      (fun i => Vector.ofFn (laneInit cv counter blockLen flags i)))
    (hmessage : CompressionMessage s.mem msgPtr (fun i => Vector.ofFn (m i)))
    (hglobal : ScheduleGlobal s sched) (hout : Fits s.mem out 4096) :
    StateT.run (agave_compress_pre_8.denote (Ctxt.Valuation.ofHVector
      [.value flagsPtr, .value lenPtr, .value hi, .value lo,
       .value msgPtr, .value ivPtr, .value cvPtr, .value out]ₕ)) s =
      .value ([]ₕ, {s with mem := outputMem out (scalarPreVectors cv m counter blockLen flags) 16 s.mem}) := by
  rw [agave_compress_pre_8_run s out cvPtr ivPtr msgPtr lo hi lenPtr flagsPtr sched _ _
      hinput hmessage hglobal hout, sevenRounds_vectors_eq_scalarPreVectors]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Seven applications of the actual compiled round-block execution theorem.
The scalar round schedule is fixed by the source loop's counter and exit test. -/
theorem seven_rounds16_run (V : agave_compress_pre_16.cfgCtx.Valuation)
    (msg sched : Pointer) (hV : RoundEnv16 V msg sched) (s : GlobalState)
    (initial m : State (Vector Word 16))
    (hsi : ∀ r i, Fits s.mem (CompressionRound.schedulePtr16 sched r i) 64)
    (hsv : ∀ r i, readWord? (CompressionRound.schedulePtr16 sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr16 msg i) 512)
    (hmv : ∀ i, readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i))) :
    StateT.run (agave_compress_pre_16.blocks.run V (headerAt16 0 initial)) s =
    StateT.run (agave_compress_pre_16.blocks.run V
      (exitAt16 (sevenRounds gVectors initial m))) s := by
  let s1 := roundFn gVectors initial m 0
  let s2 := roundFn gVectors s1 m 1
  let s3 := roundFn gVectors s2 m 2
  let s4 := roundFn gVectors s3 m 3
  let s5 := roundFn gVectors s4 m 4
  let s6 := roundFn gVectors s5 m 5
  let s7 := roundFn gVectors s6 m 6
  calc
    StateT.run (agave_compress_pre_16.blocks.run V (headerAt16 0 initial)) s =
        StateT.run (agave_compress_pre_16.blocks.run V (headerAt16 1 s1)) s :=
      round16_run V msg sched hV s 0 initial m (hsi 0) (hsv 0) hmi hmv
    _ =
        StateT.run (agave_compress_pre_16.blocks.run V (headerAt16 2 s2)) s :=
      round16_run V msg sched hV s 1 s1 m (hsi 1) (hsv 1) hmi hmv
    _ =
        StateT.run (agave_compress_pre_16.blocks.run V (headerAt16 3 s3)) s :=
      round16_run V msg sched hV s 2 s2 m (hsi 2) (hsv 2) hmi hmv
    _ =
        StateT.run (agave_compress_pre_16.blocks.run V (headerAt16 4 s4)) s :=
      round16_run V msg sched hV s 3 s3 m (hsi 3) (hsv 3) hmi hmv
    _ =
        StateT.run (agave_compress_pre_16.blocks.run V (headerAt16 5 s5)) s :=
      round16_run V msg sched hV s 4 s4 m (hsi 4) (hsv 4) hmi hmv
    _ =
        StateT.run (agave_compress_pre_16.blocks.run V (headerAt16 6 s6)) s :=
      round16_run V msg sched hV s 5 s5 m (hsi 5) (hsv 5) hmi hmv
    _ =
        StateT.run (agave_compress_pre_16.blocks.run V (exitAt16 s7)) s :=
      round16_run V msg sched hV s 6 s6 m (hsi 6) (hsv 6) hmi hmv
    _ = StateT.run (agave_compress_pre_16.blocks.run V
          (exitAt16 (sevenRounds gVectors initial m))) s := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Full execution of the compiled sixteen-lane wrapper, including entry loads,
all seven rounds, every output store, and normal return. -/
theorem agave_compress_pre_16_run (s : GlobalState)
    (out cv iv msg lo hi len flags sched : Pointer) (initial m : State (Vector Word 16))
    (hinput : CompressionInputs s.mem cv iv lo hi len flags initial)
    (hmessage : CompressionMessage s.mem msg m)
    (hglobal : ScheduleGlobal s sched) (hout : Fits s.mem out 8192) :
    StateT.run (agave_compress_pre_16.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value len, .value hi, .value lo,
       .value msg, .value iv, .value cv, .value out]ₕ)) s =
      .value ([]ₕ, {s with mem := outputMem out (sevenRounds gVectors initial m) 16 s.mem}) := by
  rw [entry16_run s out cv iv msg lo hi len flags sched initial
    hinput.cvFits hinput.ivFits hinput.loFits hinput.hiFits hinput.lenFits hinput.flagsFits
    hinput.cvRead hinput.ivRead hinput.loRead hinput.hiRead hinput.lenRead hinput.flagsRead
    hglobal.1.ptr]
  have hV : RoundEnv16 (entryVal16 out cv iv msg lo hi len flags sched initial) msg sched := by
    constructor <;> rfl
  have hsi (r : Fin 7) (i : Fin 16) :
      Fits s.mem (CompressionRound.schedulePtr16 sched r i) 64 := by
    simpa only [CompressionRound.schedulePtr16, rowPtr16, schedulePtr_two_geps] using
      scheduleGlobal_fits hglobal r i
  have hsv (r : Fin 7) (i : Fin 16) :
      readWord? (CompressionRound.schedulePtr16 sched r i) 64 s.mem =
        some (BitVec.ofNat 64 (schedule r i).val) := by
    simpa only [CompressionRound.schedulePtr16, rowPtr16, schedulePtr_two_geps] using
      scheduleGlobal_read hglobal r i
  have hptr (i : Fin 16) : messagePtr16 msg i =
      msg.withOffset (BitVec.ofNat 64 (64*i.val)) := by
    unfold messagePtr16
    rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_mul]
    rw [Nat.mul_comm i.val 64]
  have hmi (i : Fin 16) : Fits s.mem (messagePtr16 msg i) 512 := by
    rw [hptr]
    exact compressionSlotFits16 hmessage.fits i.val i.isLt
  have hmv (i : Fin 16) : readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i)) := by
    rw [hptr]
    exact hmessage.read i
  rw [seven_rounds16_run _ msg sched hV s initial m hsi hsv hmi hmv]
  have hExit : ExitEnv16 (entryVal16 out cv iv msg lo hi len flags sched initial) out := by
    constructor <;> rfl
  exact exit16_run _ out _ hExit s (compressionSlotFits16 hout)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Actual compiled execution with the BLAKE3 IV and counter initialization:
every stored vector contains the independently specified scalar compression
result for each lane. No relation between SIMD lanes is assumed. -/
theorem agave_compress_pre_16_conforms (s : GlobalState)
    (out cvPtr ivPtr msgPtr lo hi lenPtr flagsPtr sched : Pointer)
    (cv : CV (Lanes 16)) (m : State (Lanes 16)) (counter : Counters 16)
    (blockLen flags : Lanes 16)
    (hinput : CompressionInputs s.mem cvPtr ivPtr lo hi lenPtr flagsPtr
      (fun i => Vector.ofFn (laneInit cv counter blockLen flags i)))
    (hmessage : CompressionMessage s.mem msgPtr (fun i => Vector.ofFn (m i)))
    (hglobal : ScheduleGlobal s sched) (hout : Fits s.mem out 8192) :
    StateT.run (agave_compress_pre_16.denote (Ctxt.Valuation.ofHVector
      [.value flagsPtr, .value lenPtr, .value hi, .value lo,
       .value msgPtr, .value ivPtr, .value cvPtr, .value out]ₕ)) s =
      .value ([]ₕ, {s with mem := outputMem out (scalarPreVectors cv m counter blockLen flags) 16 s.mem}) := by
  rw [agave_compress_pre_16_run s out cvPtr ivPtr msgPtr lo hi lenPtr flagsPtr sched _ _
      hinput hmessage hglobal hout, sevenRounds_vectors_eq_scalarPreVectors]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The actual compiled function returns normally, and each output word read
from memory equals the scalar BLAKE3 compression result for that SIMD lane. -/
theorem agave_compress_pre_8_readback (s : GlobalState)
    (out cvPtr ivPtr msgPtr lo hi lenPtr flagsPtr sched : Pointer)
    (cv : CV (Lanes 8)) (m : State (Lanes 8)) (counter : Counters 8)
    (blockLen flags : Lanes 8)
    (hinput : CompressionInputs s.mem cvPtr ivPtr lo hi lenPtr flagsPtr
      (fun i => Vector.ofFn (laneInit cv counter blockLen flags i)))
    (hmessage : CompressionMessage s.mem msgPtr (fun i => Vector.ofFn (m i)))
    (hglobal : ScheduleGlobal s sched) (hout : Fits s.mem out 4096)
    (hwrap : out.offset.toNat + 512 ≤ 2^64) :
    ∃ s' : GlobalState,
      StateT.run (agave_compress_pre_8.denote (Ctxt.Valuation.ofHVector
        [.value flagsPtr, .value lenPtr, .value hi, .value lo,
         .value msgPtr, .value ivPtr, .value cvPtr, .value out]ₕ)) s = .value ([]ₕ, s') ∧
      ∀ (i : Fin 16) (lane : Fin 8),
        readWord? (out.withOffset (BitVec.ofNat 64 (32*i.val+4*lane.val))) 32 s'.mem =
          some (scalarCompressPre (project cv lane) (project m lane)
            (counter lane) (blockLen lane) (flags lane) i) := by
  refine ⟨{s with mem := outputMem out (scalarPreVectors cv m counter blockLen flags) 16 s.mem},
    agave_compress_pre_8_conforms s out cvPtr ivPtr msgPtr lo hi lenPtr flagsPtr sched
      cv m counter blockLen flags hinput hmessage hglobal hout, ?_⟩
  intro i lane
  simpa only [scalarPreVectors, Fin.getElem_fin, Vector.getElem_ofFn] using
    outputMem_read_lane out (scalarPreVectors cv m counter blockLen flags) s.mem hout hwrap i lane

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The actual compiled function returns normally, and each output word read
from memory equals the scalar BLAKE3 compression result for that SIMD lane. -/
theorem agave_compress_pre_16_readback (s : GlobalState)
    (out cvPtr ivPtr msgPtr lo hi lenPtr flagsPtr sched : Pointer)
    (cv : CV (Lanes 16)) (m : State (Lanes 16)) (counter : Counters 16)
    (blockLen flags : Lanes 16)
    (hinput : CompressionInputs s.mem cvPtr ivPtr lo hi lenPtr flagsPtr
      (fun i => Vector.ofFn (laneInit cv counter blockLen flags i)))
    (hmessage : CompressionMessage s.mem msgPtr (fun i => Vector.ofFn (m i)))
    (hglobal : ScheduleGlobal s sched) (hout : Fits s.mem out 8192)
    (hwrap : out.offset.toNat + 1024 ≤ 2^64) :
    ∃ s' : GlobalState,
      StateT.run (agave_compress_pre_16.denote (Ctxt.Valuation.ofHVector
        [.value flagsPtr, .value lenPtr, .value hi, .value lo,
         .value msgPtr, .value ivPtr, .value cvPtr, .value out]ₕ)) s = .value ([]ₕ, s') ∧
      ∀ (i : Fin 16) (lane : Fin 16),
        readWord? (out.withOffset (BitVec.ofNat 64 (64*i.val+4*lane.val))) 32 s'.mem =
          some (scalarCompressPre (project cv lane) (project m lane)
            (counter lane) (blockLen lane) (flags lane) i) := by
  refine ⟨{s with mem := outputMem out (scalarPreVectors cv m counter blockLen flags) 16 s.mem},
    agave_compress_pre_16_conforms s out cvPtr ivPtr msgPtr lo hi lenPtr flagsPtr sched
      cv m counter blockLen flags hinput hmessage hglobal hout, ?_⟩
  intro i lane
  simpa only [scalarPreVectors, Fin.getElem_fin, Vector.getElem_ofFn] using
    outputMem_read_lane out (scalarPreVectors cv m counter blockLen flags) s.mem hout hwrap i lane

end AgaveLatticeHash.MLIR
