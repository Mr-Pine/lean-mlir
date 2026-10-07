import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionControl
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory

/-! The exact scalar-parse basic block, including both black-box calls, flagged
pointer arithmetic, the signed high-byte test, reduction, and byte equality. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

def scalarBlockEnv (E : Env program.Γ) (signature : Pointer)
    (first last : BitVec 8) (equal : Bool) : Env program.Γ :=
  let high := (255#8).slt last
  E[%49 := .value (signature.add 32#64), %50 := .value first,
    %51 := .value (signature.add 63#64), %52 := .value last,
    %53 := .value (BitVec.ofBool high), %54 := .value (choiceByte high),
    %55 := .value (choiceByte high), %56 := .value (choiceByte equal),
    %57 := .value (choiceByte (equal && high)),
    %58 := .value (choiceByte (equal && high)),
    %59 := .value (BitVec.ofBool (equal && high))]

/-- A direct execution equation for the imported scalar-check block. The
reducer and equality premises concern only their individual calls. `first`
and `last` are loaded from the signature before either call runs. -/
theorem scalar_check_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s t u v w : GlobalState) (signature scratch : Pointer)
    (first last : BitVec 8) (equal : Bool)
    (hsig : E.read (%arg1) = .value signature)
    (hscratch : E.read (%20) = .value scratch)
    (h32 : E.read (%1) = .value 32#64)
    (h63 : E.read (%12) = .value 63#64)
    (hminus : E.read (%13) = .value 255#8)
    (hone : E.read (%14) = .value 1#8)
    (hfit : SmallRange s.mem signature 64)
    (hfirst : s.mem.readAt (signature.add 32#64) 8 = first)
    (hlast : s.mem.readAt (signature.add 63#64) 8 = last)
    (hblackFirst : p.blackBoxByte (.cons (.value (choiceByte ((255#8).slt last))) .nil) s =
      .value (.cons (.value (choiceByte ((255#8).slt last))) .nil, t))
    (hblackLast : p.blackBoxByte
      (.cons (.value (choiceByte (equal && (255#8).slt last))) .nil) v =
      .value (.cons (.value (choiceByte (equal && (255#8).slt last))) .nil, w))
    (hreduce : p.scalarReduce (args2 scratch (signature.add 32#64)) t = .value (.nil, u))
    (hequal : p.bytesConstantTimeEq (args2 (signature.add 32#64) scratch) u =
      .value (.cons (.value (choiceByte equal)) .nil, v)) :
    (program p g).runFrom E 4 s =
      (program p g).runFrom (scalarBlockEnv E signature first last equal)
        (if equal && (255#8).slt last then 5 else 11) w := by
  dsimp only [args2] at hreduce hequal
  change E.args 1 = .value signature at hsig
  have hg32 := hfit.gep (k := 32) (by decide)
  have hg63 := hfit.gep (k := 63) (by decide)
  change Operation.gepInboundsLive s.mem (.value signature) [.value (32 : Int)] =
    .value (signature.add 32#64) at hg32
  change Operation.gepInboundsLive s.mem (.value signature) [.value (63 : Int)] =
    .value (signature.add 63#64) at hg63
  have hf32 : Fits s.mem (signature.add 32#64) 8 :=
    hfit.fits_add (k := 32) (count := 1) (by decide)
  have hf63 : Fits s.mem (signature.add 63#64) 8 :=
    hfit.fits_add (k := 63) (count := 1) (by decide)
  have hblock : (program.bb4 p).run program.blockParams E s =
      .value (((scalarBlockEnv E signature first last equal),
        .inr (if equal && (255#8).slt last then 5 else 11)), w) := by
    cases hh : (255#8).slt last <;> cases equal <;>
      simp [hh, choiceByte] at hblackFirst hblackLast hequal <;>
      simp [BasicBlock.run, program.bb4, scalarBlockEnv,
        List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
        UnOp.compute, BinOp.compute, Operation.zext, Operation.and, Operation.icmp,
        EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
        Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
        Env.writeMany_cons, Env.writeMany_nil, args2, choiceByte,
        GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
        hsig, hscratch, h32, h63, hminus, hone, hg32, hg63, hf32, hf63,
        hfirst, hlast, hblackFirst, hblackLast, hreduce, hequal, hh, throwUBIf]
  rw [Func.runFrom_eq, block_4, hblock]
  rfl

/-- All scalar encodings that fail the source parser gate follow the imported
error path. This statement retains the first-byte/last-byte memory obligations
rather than assuming a well-formed scalar. -/
theorem scalar_check_rejection (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s t u v w : GlobalState) (signature scratch : Pointer)
    (first last : BitVec 8) (equal : Bool)
    (hsig : E.read (%arg1) = .value signature)
    (hscratch : E.read (%20) = .value scratch)
    (h32 : E.read (%1) = .value 32#64)
    (h63 : E.read (%12) = .value 63#64)
    (hminus : E.read (%13) = .value 255#8)
    (hone : E.read (%14) = .value 1#8)
    (herr : E.read (%8) = .value 2#8)
    (hfit : SmallRange s.mem signature 64)
    (hfirst : s.mem.readAt (signature.add 32#64) 8 = first)
    (hlast : s.mem.readAt (signature.add 63#64) 8 = last)
    (hblackFirst : p.blackBoxByte (.cons (.value (choiceByte ((255#8).slt last))) .nil) s =
      .value (.cons (.value (choiceByte ((255#8).slt last))) .nil, t))
    (hblackLast : p.blackBoxByte
      (.cons (.value (choiceByte (equal && (255#8).slt last))) .nil) v =
      .value (.cons (.value (choiceByte (equal && (255#8).slt last))) .nil, w))
    (hreduce : p.scalarReduce (args2 scratch (signature.add 32#64)) t = .value (.nil, u))
    (hequal : p.bytesConstantTimeEq (args2 (signature.add 32#64) scratch) u =
      .value (.cons (.value (choiceByte equal)) .nil, v))
    (hreject : (equal && (255#8).slt last) = false) :
    (program p g).runFrom E 4 s = .value (.cons (.value 2#8) .nil, w) := by
  rw [scalar_check_block p g E s t u v w signature scratch first last equal hsig hscratch
    h32 h63 hminus hone hfit hfirst hlast hblackFirst hblackLast hreduce hequal, hreject]
  apply scalar_rejection
  simp [scalarBlockEnv, mlir_env, herr]

/-- A reduction call followed by read-only byte equality has only the reducer's
caller-visible output effect. -/
theorem OutputFrame.thenReadOnly (frame : OutputFrame before middle out bytes)
    (readOnly : ReadOnlyFrame middle after) : OutputFrame before after out bytes := by
  refine ⟨readOnly.wellFormed, ?_, ?_⟩
  · intro q n hq
    exact readOnly.live q n (frame.live q n hq)
  · intro q w hd
    exact (readOnly.read q w).trans (frame.read q w hd)

/-- A read-only prefix preserves the caller-visible output frame. -/
theorem ReadOnlyFrame.thenOutput (readOnly : ReadOnlyFrame before middle)
    (frame : OutputFrame middle after out bytes) : OutputFrame before after out bytes := by
  refine ⟨frame.wellFormed, ?_, ?_⟩
  · intro q n hq
    exact frame.live q n (readOnly.live q n hq)
  · intro q width hd
    exact (frame.read q width hd).trans (readOnly.read q width)

/-- A subread of the scalar half of a signature, including the exact generated
pointer arithmetic. The full scalar remains arbitrary. -/
theorem scalar_signature_subread (state : GlobalState) (signature : Pointer)
    (bytes : Bytes32) (hbytes : ReadBytes state (signature.add 32#64) 32 bytes)
    (k count : Nat) (hk : k + count ≤ 32) :
    state.mem.readAt (signature.add (32#64 + BitVec.ofNat 64 k)) (8 * count) =
      bytes.extractLsb' (8 * k) (8 * count) := by
  have hk64 : k < 2^64 := by omega
  have he := MemoryState.readAt_add_of_readAt (off := BitVec.ofNat 64 k) (w := 8 * count)
    hbytes.1.fits (hbytes.1.no_wrap (by omega)) (by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
      omega) hbytes.2
  simpa only [Pointer.add_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64,
    Nat.mul_comm] using he

/-- The exact scalar block follows the parser gate for every byte string.
The only effect contracts used here are reduction, equality, and black-box
identity; the resulting frame can be used to continue the generated CFG. -/
theorem scalar_check_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (hreduce : ScalarReduceContract p.scalarReduce layout)
    (hequal : BytesEqContract p.bytesConstantTimeEq)
    (hblack : BlackBoxContract p.blackBoxByte)
    (E : Env program.Γ) (state : GlobalState) (signature scratch : Pointer)
    (bytes : Bytes32)
    (hsig : E.read (%arg1) = .value signature)
    (hscratch : E.read (%20) = .value scratch)
    (h32 : E.read (%1) = .value 32#64)
    (h63 : E.read (%12) = .value 63#64)
    (hminus : E.read (%13) = .value 255#8)
    (hone : E.read (%14) = .value 1#8)
    (hwf : state.WF) (hsigfit : SmallRange state.mem signature 64)
    (hfit : SmallRange state.mem scratch 32)
    (hbytes : ReadBytes state (signature.add 32#64) 32 bytes)
    (hd : (Range.of scratch 256).Disjoint (Range.of (signature.add 32#64) 256)) :
    ∃ after, OutputFrame state after scratch 32 ∧
      (program p g).runFrom E 4 state =
        (program p g).runFrom
          (scalarBlockEnv E signature (bytes.extractLsb' 0 8) (bytes.extractLsb' 248 8)
            (decide (bytes = layout.reduce bytes)))
          (if scalarGate layout bytes then 5 else 11) after := by
  obtain ⟨blackFirst, hbf, hbfFrame⟩ := hblack
    (choiceByte ((255#8).slt (bytes.extractLsb' 248 8))) state hwf
  have hbytesFirst := ReadOnlyFrame.readBytes state blackFirst
    (signature.add 32#64) 32 bytes hbfFrame hbytes
  obtain ⟨middle, hrcall, hframe, hred⟩ := hreduce scratch (signature.add 32#64)
    blackFirst bytes hbfFrame.wellFormed (hbfFrame.live _ _ hfit) hbytesFirst hd
  have hb := OutputFrame.readBytes blackFirst middle scratch
    (signature.add 32#64) 32 32 bytes hframe hbytesFirst hd.symm
  obtain ⟨equalAfter, hecall, hro⟩ := hequal (signature.add 32#64) scratch middle bytes
    (layout.reduce bytes) hframe.wellFormed hb hred
  have hfirst := scalar_signature_subread state signature bytes hbytes 0 1 (by decide)
  have hlast := scalar_signature_subread state signature bytes hbytes 31 1 (by decide)
  change state.mem.readAt (signature.add 32#64) 8 = bytes.extractLsb' 0 8 at hfirst
  change state.mem.readAt (signature.add 63#64) 8 = bytes.extractLsb' 248 8 at hlast
  have hecall' : p.bytesConstantTimeEq (args2 (signature.add 32#64) scratch) middle =
    .value (.cons (.value (choiceByte (decide (bytes = layout.reduce bytes)))) .nil, equalAfter) := by
    simpa only [choiceByte, decide_eq_true_eq] using hecall
  have hsame : decide (bytes = layout.reduce bytes) = decide (layout.reduce bytes = bytes) := by
    simp only [eq_comm]
  have hgate : (decide (bytes = layout.reduce bytes) && (255#8).slt (bytes.extractLsb' 248 8)) =
      scalarGate layout bytes := by
    unfold scalarGate scalarHighBitClear
    have hnegative : (-1 : BitVec 8) = 255#8 := by decide
    rw [hsame, Bool.and_comm, hnegative]
  obtain ⟨after, hbl, hblFrame⟩ := hblack
    (choiceByte (decide (bytes = layout.reduce bytes) &&
      (255#8).slt (bytes.extractLsb' 248 8))) equalAfter hro.wellFormed
  refine ⟨after, hbfFrame.thenOutput ((hframe.thenReadOnly hro).thenReadOnly hblFrame), ?_⟩
  rw [scalar_check_block p g E state blackFirst middle equalAfter after signature scratch
    (bytes.extractLsb' 0 8) (bytes.extractLsb' 248 8) (decide (bytes = layout.reduce bytes))
    hsig hscratch h32 h63 hminus hone hsigfit hfirst hlast hbf hbl hrcall hecall', hgate]

end Agave.Ed25519.Verifier.Execution.Dalek
