/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionProof
import SSA.Projects.Agave.LatticeHash.MLIR.PortableReference
import SSA.Projects.Agave.LatticeHash.MLIR.PortableOutputRead

/-!
Observable refinement of the three independently compiled compression helpers.
These theorems concern actual CFG execution and byte-backed output reads.
They do not assert execution of the Rust public lifecycle or the full batch CFG.
-/
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression

attribute [local irreducible] agave_portable_compress_pre portableCompressionMemory
  AgaveBlake3Reference.compressPre

/-- The actual portable helper returns, and every stored word agrees with the
independent portable reference. All premises describe input memory and bounds. -/
theorem portable_reference_readback (s : GlobalState) (out cvp msg : Pointer)
    (cv : AgaveBlake3Reference.CV) (b : AgaveBlake3Reference.Block)
    (counter : BitVec 64) (len flags : BitVec 8)
    (hout : Fits s.mem out 512) (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (hwrap : out.offset.toNat + 64 ≤ 2^64)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem =
      some (AgaveBlake3Reference.load32 b i)) :
    ∃ s' : GlobalState,
      StateT.run (agave_portable_compress_pre.denote (Ctxt.Valuation.ofHVector
        [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ)) s =
        .value ([]ₕ, s') ∧
      ∀ i : Fin 16, readWord? (out.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s'.mem =
        some (AgaveBlake3Reference.compressPre cv b (len.zeroExtend 32) counter
          (flags.zeroExtend 32) i) := by
  let words := AgaveBlake3Reference.compressPre cv b (len.zeroExtend 32) counter (flags.zeroExtend 32)
  let after : GlobalState := {s with mem := portableCompressionMemory s.mem out words}
  refine ⟨after, portable_reference_run s out cvp msg cv b counter len flags
    hout hcvp hmsg rcv rmsg, ?_⟩
  intro i
  exact portableCompressionMemory_read_word s.mem out words hout hwrap i

/-- Actual 8-lane compression returns the independent reference result in every
lane. Different lanes may carry unrelated chaining values, blocks and counters. -/
theorem vector8_reference_readback (s : GlobalState)
    (out cvp ivp msg lo hi lenp flagsp sched : Pointer)
    (cv : CV (Lanes 8)) (b : Fin 8 → AgaveBlake3Reference.Block)
    (counter : Counters 8) (len flags : Lanes 8)
    (hinput : CompressionInputs s.mem cvp ivp lo hi lenp flagsp
      (fun i => Vector.ofFn (laneInit cv counter len flags i)))
    (hmessage : CompressionMessage s.mem msg
      (fun i => Vector.ofFn (fun lane => AgaveBlake3Reference.load32 (b lane) i)))
    (hglobal : ScheduleGlobal s sched) (hout : Fits s.mem out 4096)
    (hwrap : out.offset.toNat + 512 ≤ 2^64) :
    ∃ s' : GlobalState,
      StateT.run (agave_compress_pre_8.denote (Ctxt.Valuation.ofHVector
        [.value flagsp, .value lenp, .value hi, .value lo,
         .value msg, .value ivp, .value cvp, .value out]ₕ)) s = .value ([]ₕ, s') ∧
      ∀ (i : Fin 16) (lane : Fin 8),
        readWord? (out.withOffset (BitVec.ofNat 64 (32*i.val+4*lane.val))) 32 s'.mem =
          some (AgaveBlake3Reference.compressPre (project cv lane) (b lane)
            (len lane) (counter lane) (flags lane) i) := by
  obtain ⟨s', hrun, hread⟩ := agave_compress_pre_8_readback s out cvp ivp msg lo hi lenp flagsp sched cv
    (fun i lane => AgaveBlake3Reference.load32 (b lane) i) counter len flags
    hinput hmessage hglobal hout hwrap
  refine ⟨s', hrun, ?_⟩
  intro i lane
  rw [AgaveBlake3Reference.compressPre_eq]
  exact hread i lane

/-- Actual 16-lane compression returns the independent reference result in every
lane. Different lanes may carry unrelated chaining values, blocks and counters. -/
theorem vector16_reference_readback (s : GlobalState)
    (out cvp ivp msg lo hi lenp flagsp sched : Pointer)
    (cv : CV (Lanes 16)) (b : Fin 16 → AgaveBlake3Reference.Block)
    (counter : Counters 16) (len flags : Lanes 16)
    (hinput : CompressionInputs s.mem cvp ivp lo hi lenp flagsp
      (fun i => Vector.ofFn (laneInit cv counter len flags i)))
    (hmessage : CompressionMessage s.mem msg
      (fun i => Vector.ofFn (fun lane => AgaveBlake3Reference.load32 (b lane) i)))
    (hglobal : ScheduleGlobal s sched) (hout : Fits s.mem out 8192)
    (hwrap : out.offset.toNat + 1024 ≤ 2^64) :
    ∃ s' : GlobalState,
      StateT.run (agave_compress_pre_16.denote (Ctxt.Valuation.ofHVector
        [.value flagsp, .value lenp, .value hi, .value lo,
         .value msg, .value ivp, .value cvp, .value out]ₕ)) s = .value ([]ₕ, s') ∧
      ∀ (i : Fin 16) (lane : Fin 16),
        readWord? (out.withOffset (BitVec.ofNat 64 (64*i.val+4*lane.val))) 32 s'.mem =
          some (AgaveBlake3Reference.compressPre (project cv lane) (b lane)
            (len lane) (counter lane) (flags lane) i) := by
  obtain ⟨s', hrun, hread⟩ := agave_compress_pre_16_readback s out cvp ivp msg lo hi lenp flagsp sched cv
    (fun i lane => AgaveBlake3Reference.load32 (b lane) i) counter len flags
    hinput hmessage hglobal hout hwrap
  refine ⟨s', hrun, ?_⟩
  intro i lane
  rw [AgaveBlake3Reference.compressPre_eq]
  exact hread i lane

/-- Concrete caller data, kept separate from the memory validity predicate. -/
structure PortableCompressionCall where
  state : GlobalState
  out : Pointer
  cvp : Pointer
  msg : Pointer
  cv : AgaveBlake3Reference.CV
  block : AgaveBlake3Reference.Block
  counter : BitVec 64
  len : BitVec 8
  flags : BitVec 8

def PortableCompressionCall.Valid (p : PortableCompressionCall) : Prop :=
  Fits p.state.mem p.out 512 ∧ Fits p.state.mem p.cvp 256 ∧
  Fits p.state.mem p.msg 512 ∧ p.out.offset.toNat + 64 ≤ 2^64 ∧
  (∀ i : Fin 8, readWord? (p.cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 p.state.mem = some (p.cv i)) ∧
  (∀ i : Fin 16, readWord? (p.msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 p.state.mem =
    some (AgaveBlake3Reference.load32 p.block i))

def PortableCompressionCall.Returns (p : PortableCompressionCall) (s : GlobalState) : Prop :=
  StateT.run (agave_portable_compress_pre.denote (Ctxt.Valuation.ofHVector
    [.value p.flags, .value p.counter, .value p.len, .value p.msg, .value p.cvp, .value p.out]ₕ))
    p.state = .value ([]ₕ, s)

structure VectorCompressionCall (n : Nat) where
  state : GlobalState
  out : Pointer
  cvp : Pointer
  ivp : Pointer
  msg : Pointer
  lo : Pointer
  hi : Pointer
  lenp : Pointer
  flagsp : Pointer
  sched : Pointer
  cv : CV (Lanes n)
  block : Fin n → AgaveBlake3Reference.Block
  counter : Counters n
  len : Lanes n
  flags : Lanes n

def VectorCompressionCall.Valid {n : Nat} (p : VectorCompressionCall n) : Prop :=
  CompressionInputs p.state.mem p.cvp p.ivp p.lo p.hi p.lenp p.flagsp
    (fun i => Vector.ofFn (laneInit p.cv p.counter p.len p.flags i)) ∧
  CompressionMessage p.state.mem p.msg
    (fun i => Vector.ofFn (fun lane => AgaveBlake3Reference.load32 (p.block lane) i)) ∧
  ScheduleGlobal p.state p.sched ∧ Fits p.state.mem p.out (512*n) ∧
  p.out.offset.toNat + 64*n ≤ 2^64

/-- Equality of the selected logical input, independent of its memory layout. -/
def VectorCompressionCall.Matches {n : Nat} (v : VectorCompressionCall n)
    (lane : Fin n) (p : PortableCompressionCall) : Prop :=
  project v.cv lane = p.cv ∧ v.block lane = p.block ∧
  v.counter lane = p.counter ∧ v.len lane = p.len.zeroExtend 32 ∧
  v.flags lane = p.flags.zeroExtend 32

def VectorCompressionCall.Returns8 (p : VectorCompressionCall 8) (s : GlobalState) : Prop :=
  StateT.run (agave_compress_pre_8.denote (Ctxt.Valuation.ofHVector
    [.value p.flagsp, .value p.lenp, .value p.hi, .value p.lo,
     .value p.msg, .value p.ivp, .value p.cvp, .value p.out]ₕ)) p.state = .value ([]ₕ, s)

def VectorCompressionCall.Returns16 (p : VectorCompressionCall 16) (s : GlobalState) : Prop :=
  StateT.run (agave_compress_pre_16.denote (Ctxt.Valuation.ofHVector
    [.value p.flagsp, .value p.lenp, .value p.hi, .value p.lo,
     .value p.msg, .value p.ivp, .value p.cvp, .value p.out]ₕ)) p.state = .value ([]ₕ, s)

/-- The independently compiled portable, AVX2 and AVX512 helpers all return;
reading any word from matching lanes yields exactly the same value. Other SIMD
lanes are unrestricted. The hypotheses are input memory validity and matching
logical inputs; neither execution nor output correctness is assumed. -/
theorem compression_three_way_readback
    (p : PortableCompressionCall) (v8 : VectorCompressionCall 8)
    (v16 : VectorCompressionCall 16) (lane8 : Fin 8) (lane16 : Fin 16)
    (hp : p.Valid) (hv8 : v8.Valid) (hv16 : v16.Valid)
    (hm8 : v8.Matches lane8 p) (hm16 : v16.Matches lane16 p) :
    ∃ sp s8 s16 : GlobalState,
      p.Returns sp ∧ v8.Returns8 s8 ∧ v16.Returns16 s16 ∧
      ∀ i : Fin 16,
        readWord? (p.out.withOffset (BitVec.ofNat 64 (4*i.val))) 32 sp.mem =
          some (AgaveBlake3Reference.compressPre p.cv p.block (p.len.zeroExtend 32)
            p.counter (p.flags.zeroExtend 32) i) ∧
        readWord? (p.out.withOffset (BitVec.ofNat 64 (4*i.val))) 32 sp.mem =
          readWord? (v8.out.withOffset (BitVec.ofNat 64 (32*i.val+4*lane8.val))) 32 s8.mem ∧
        readWord? (v8.out.withOffset (BitVec.ofNat 64 (32*i.val+4*lane8.val))) 32 s8.mem =
          readWord? (v16.out.withOffset (BitVec.ofNat 64 (64*i.val+4*lane16.val))) 32 s16.mem := by
  rcases hp with ⟨hpout, hpcv, hpmsg, hpwrap, hpcvr, hpmsgr⟩
  rcases hv8 with ⟨hi8, hm8mem, hg8, ho8, hw8⟩
  rcases hv16 with ⟨hi16, hm16mem, hg16, ho16, hw16⟩
  obtain ⟨sp, hrp, hreadp⟩ := portable_reference_readback p.state p.out p.cvp p.msg
    p.cv p.block p.counter p.len p.flags hpout hpcv hpmsg hpwrap hpcvr hpmsgr
  obtain ⟨s8, hr8, hread8⟩ := vector8_reference_readback v8.state v8.out v8.cvp v8.ivp
    v8.msg v8.lo v8.hi v8.lenp v8.flagsp v8.sched v8.cv v8.block v8.counter v8.len v8.flags
    hi8 hm8mem hg8 ho8 hw8
  obtain ⟨s16, hr16, hread16⟩ := vector16_reference_readback v16.state v16.out v16.cvp v16.ivp
    v16.msg v16.lo v16.hi v16.lenp v16.flagsp v16.sched v16.cv v16.block v16.counter v16.len v16.flags
    hi16 hm16mem hg16 ho16 hw16
  refine ⟨sp, s8, s16, hrp, hr8, hr16, ?_⟩
  intro i
  rcases hm8 with ⟨hc8, hb8, hk8, hl8, hf8⟩
  rcases hm16 with ⟨hc16, hb16, hk16, hl16, hf16⟩
  rw [hreadp i, hread8 i lane8, hread16 i lane16,
    hc8, hb8, hk8, hl8, hf8, hc16, hb16, hk16, hl16, hf16]
  exact ⟨rfl, rfl, rfl⟩

end AgaveLatticeHash.MLIR
