import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionControl
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory

/-! Exact accepted-scalar copying and the first CPUID-cache load. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- The byte-preserving 31+1 copy emitted by LLVM for a parsed scalar. -/
def scalarCopyState (state : GlobalState) (signature scalar : Pointer)
    (first : BitVec 8) : GlobalState :=
  { state with mem :=
    (state.mem.storeAt (scalar.add 1#64) (state.mem.readAt (signature.add 33#64) 248)).storeAt scalar first }

def scalarCopyEnv (E : Env program.Γ) (signature scalar : Pointer) (cache : BitVec 8) :
    Env program.Γ :=
  E[%60 := .value (signature.add 33#64), %61 := .value (scalar.add 1#64),
    %62 := .value cache, %63 := .value (BitVec.ofBool (cache == 255#8))]

/-- This equation executes block 5 itself. The final cache value is read after
the scalar copy; it is not replaced by an assumed CPU-selection result. -/
theorem scalar_copy_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (signature scalar cache : Pointer) (first cached : BitVec 8)
    (hsig : E.read (%arg1) = .value signature)
    (hscalar : E.read (%27) = .value scalar) (hcache : E.read (%18) = .value cache)
    (hfirst : E.read (%50) = .value first)
    (h33 : E.read (%15) = .value 33#64)
    (h1 : E.read (%16) = .value 1#64)
    (h31 : E.read (%17) = .value 31#64)
    (h255 : E.read (%13) = .value 255#8)
    (hfsig : SmallRange state.mem signature 64)
    (hfscalar : SmallRange state.mem scalar 32)
    (hdisjoint : (Range.of (scalar.add 1#64) 248).Disjoint
      (Range.of (signature.add 33#64) 248))
    (hfcache : Fits state.mem cache 8)
    (hcached : (scalarCopyState state signature scalar first).mem.readAt cache 8 = cached) :
    (program p g).runFrom E 5 state =
      (program p g).runFrom (scalarCopyEnv E signature scalar cached)
        (if cached = 255#8 then 6 else 7) (scalarCopyState state signature scalar first) := by
  change E.args 1 = .value signature at hsig
  have hg33 := hfsig.gep (k := 33) (by decide)
  have hg1 := hfscalar.gep (k := 1) (by decide)
  change Operation.gepInboundsLive state.mem (.value signature) [.value (33 : Int)] =
    .value (signature.add 33#64) at hg33
  change Operation.gepInboundsLive state.mem (.value scalar) [.value (1 : Int)] =
    .value (scalar.add 1#64) at hg1
  have hf33 : Fits state.mem (signature.add 33#64) 248 :=
    hfsig.fits_add (k := 33) (count := 31) (by decide)
  have hf1 : Fits state.mem (scalar.add 1#64) 248 :=
    hfscalar.fits_add (k := 1) (count := 31) (by decide)
  have hf0 : Fits
      (state.mem.storeAt (scalar.add 1#64) (state.mem.readAt (signature.add 33#64) 248)) scalar 8 :=
    Fits.storeAt (Fits.mono (by decide) hfscalar.fits)
  have hfc : Fits (scalarCopyState state signature scalar first).mem cache 8 :=
    Fits.storeAt (Fits.storeAt hfcache)
  dsimp only [scalarCopyState] at hfc hcached
  have hb : program.bb5.run program.blockParams E state =
      .value (((scalarCopyEnv E signature scalar cached), .inr (if cached = 255#8 then 6 else 7)),
        scalarCopyState state signature scalar first) := by
    by_cases heq : cached = 255#8 <;>
      simp [BasicBlock.run, program.bb5, scalarCopyEnv, scalarCopyState,
        List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy, Operation.store,
        Operation.load, BinOp.compute, Operation.icmp,
        EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
        Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
        Env.writeMany_cons, Env.writeMany_nil,
        GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
        hsig, hscalar, hcache, hfirst, h33, h1, h31, h255,
        hg33, hg1, hf33, hf1, hf0, hdisjoint, hfc, hcached, heq, throwUBIf,
        ofBool_eq_one_iff]
  rw [Func.runFrom_eq, block_5, hb]
  rfl

/-- Two disjoint writes cover all 256 bits; no fact about the previous stack
contents is needed. -/
theorem scalar_splice_parts (old value : Bytes32) :
    Memory.spliceBits (Memory.spliceBits old 8 (value.extractLsb' 8 248))
      0 (value.extractLsb' 0 8) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getLsbD_spliceBits, BitVec.getLsbD_extractLsb']
  grind

/-- Full readback of the parsed scalar's emitted 31+1 copy. -/
theorem scalar_copy_readback (state : GlobalState) (signature scalar : Pointer)
    (first : BitVec 8) (value : Bytes32) (hscalar : SmallRange state.mem scalar 32)
    (hhigh : state.mem.readAt (signature.add 33#64) 248 = value.extractLsb' 8 248)
    (hlow : first = value.extractLsb' 0 8) :
    ReadBytes (scalarCopyState state signature scalar first) scalar 32 value := by
  constructor
  · exact (hscalar.storeAt _ _).storeAt _ _
  · have houter := MemoryState.readAt_add_storeAt (p := scalar) (off := 0#64)
      (v := 256) (w := 8)
      (m := state.mem.storeAt (scalar.add 1#64) (state.mem.readAt (signature.add 33#64) 248))
      hscalar.fits.storeAt (hscalar.no_wrap (k := 0) (by decide)) (by decide) first
    have hinner := MemoryState.readAt_add_storeAt (p := scalar) (off := 1#64)
      (v := 256) (w := 248) hscalar.fits (hscalar.no_wrap (k := 1) (by decide))
      (by decide) (state.mem.readAt (signature.add 33#64) 248)
    simp only [Pointer.add_zero, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.zero_mul, Nat.one_mul] at houter hinner
    change ((state.mem.storeAt (scalar.add 1#64)
      (state.mem.readAt (signature.add 33#64) 248)).storeAt scalar first).readAt scalar 256 = value
    rw [houter, hinner, hhigh, hlow, scalar_splice_parts]

/-- The accepted-scalar copy changes only the 32-byte scalar destination. -/
theorem scalar_copy_frame (state : GlobalState) (signature scalar : Pointer)
    (first : BitVec 8) (hwf : state.WF) (hscalar : SmallRange state.mem scalar 32) :
    OutputFrame state (scalarCopyState state signature scalar first) scalar 32 := by
  constructor
  · simpa only [scalarCopyState, GlobalState.WF_storeAt] using hwf
  · intro q n hn
    exact (hn.storeAt _ _).storeAt _ _
  · intro q w hd
    have hhigh := disjoint_add_subrange hscalar hd (k := 1) (count := 31) (by decide)
    have hlow := disjoint_add_subrange hscalar hd (k := 0) (count := 1) (by decide)
    simp only [Pointer.add_zero] at hlow
    simp only [scalarCopyState, MemoryState.readAt_storeAt_disjoint hlow.symm,
      MemoryState.readAt_storeAt_disjoint hhigh.symm]

end Agave.Ed25519.Verifier.Execution.Dalek
