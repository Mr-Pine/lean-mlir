import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionControl
import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionArithmetic

namespace Agave.Ed25519.Verifier.Execution.Key
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

abbrev Words := Fin 5 → BitVec 64

def negWord (x : Words) (i : Fin 5) : BitVec 64 :=
  (if i = 0 then 36028797018963664 else 36028797018963952) - x i

def negResult (x : Words) : Words :=
  ![(negWord x 4 >>> 51) * 19 + (negWord x 0 &&& 2251799813685247),
    (negWord x 1 &&& 2251799813685247) + (negWord x 0 >>> 51),
    (negWord x 2 &&& 2251799813685247) + (negWord x 1 >>> 51),
    (negWord x 3 &&& 2251799813685247) + (negWord x 2 >>> 51),
    (negWord x 4 &&& 2251799813685247) + (negWord x 3 >>> 51)]

def copyYZ (s : GlobalState) (out opt : Pointer) : GlobalState :=
  { s with mem := ((s.mem.storeAt (out.add 80#64) (s.mem.readAt (opt.add 48#64) 320)).storeAt (out.add 120#64) (s.mem.readAt (opt.add 88#64) 320)) }

def payloadState (s : GlobalState) (out opt bytes : Pointer) (x t : Words) : GlobalState :=
  let m := (copyYZ s out opt).mem.storeAt (out.add 8#64) (s.mem.readAt bytes 256)
  let m := m.storeAt (out.add 40#64) (negResult x 0)
  let m := m.storeAt (out.add 48#64) (BitVec.packLanes #v[negResult x 1, negResult x 2])
  let m := m.storeAt (out.add 64#64) (BitVec.packLanes #v[negResult x 3, negResult x 4])
  let m := m.storeAt (out.add 160#64) (negResult t 0)
  let m := m.storeAt (out.add 168#64) (BitVec.packLanes #v[negResult t 1, negResult t 2])
  let m := m.storeAt (out.add 184#64) (BitVec.packLanes #v[negResult t 3, negResult t 4])
  { s with mem := m }

/-- Exact byte slices loaded by the two inline negations. Y and Z are copied
without inspection. Overlapping x0/x1 and x1/x2 loads are explicit. -/
structure NegationReads (s : GlobalState) (opt : Pointer) (x t : Words) : Prop where
  x01 : s.mem.readAt (opt.add 8#64) 128 = BitVec.packLanes #v[x 0, x 1]
  x12 : s.mem.readAt (opt.add 16#64) 128 = BitVec.packLanes #v[x 1, x 2]
  x34 : s.mem.readAt (opt.add 32#64) 128 = BitVec.packLanes #v[x 3, x 4]
  t01 : s.mem.readAt (opt.add 128#64) 128 = BitVec.packLanes #v[t 0, t 1]
  t12 : s.mem.readAt (opt.add 136#64) 128 = BitVec.packLanes #v[t 1, t 2]
  t34 : s.mem.readAt (opt.add 152#64) 128 = BitVec.packLanes #v[t 3, t 4]

def successEnv (E : Env program.Γ) (out opt : Pointer) (x t : Words) : Env program.Γ :=
  E[%30 := .value (opt.add 8#64),
    %31 := .value (opt.add 16#64),
    %32 := .value (opt.add 32#64),
    %33 := .value (opt.add 48#64),
    %34 := .value (out.add 80#64),
    %35 := .value (opt.add 88#64),
    %36 := .value (out.add 120#64),
    %37 := .value (opt.add 128#64),
    %38 := .value (opt.add 136#64),
    %39 := .value (opt.add 152#64),
    %40 := .value (out.add 8#64),
    %41 := .value (out.add 40#64),
    %42 := .value (out.add 48#64),
    %43 := Ty.wrap #v[x 0, x 1],
    %44 := Ty.wrap #v[x 1, x 2],
    %45 := Ty.wrap #v[negWord x 0, negWord x 1],
    %46 := Ty.wrap #v[negWord x 1, negWord x 2],
    %47 := Ty.wrap #v[negWord x 0 >>> 51, negWord x 1 >>> 51],
    %48 := .value (negWord x 0),
    %49 := .value (negWord x 0 &&& 2251799813685247),
    %50 := Ty.wrap #v[negWord x 1 &&& 2251799813685247, negWord x 2 &&& 2251799813685247],
    %51 := Ty.wrap #v[negResult x 1, negResult x 2],
    %52 := .value (out.add 64#64),
    %53 := Ty.wrap #v[x 3, x 4],
    %54 := Ty.wrap #v[negWord x 3, negWord x 4],
    %55 := .value (negWord x 4),
    %56 := .value (negWord x 4 >>> 51),
    %57 := Ty.wrap #v[negWord x 3 &&& 2251799813685247, negWord x 4 &&& 2251799813685247],
    %58 := .value ((negWord x 4 >>> 51) * 19),
    %59 := Ty.wrap #v[negWord x 2, negWord x 3],
    %60 := Ty.wrap #v[negWord x 2 >>> 51, negWord x 3 >>> 51],
    %61 := .value (negResult x 0),
    %62 := Ty.wrap #v[negResult x 3, negResult x 4],
    %63 := .value (out.add 160#64),
    %64 := .value (out.add 168#64),
    %65 := Ty.wrap #v[t 0, t 1],
    %66 := Ty.wrap #v[t 1, t 2],
    %67 := Ty.wrap #v[negWord t 0, negWord t 1],
    %68 := Ty.wrap #v[negWord t 1, negWord t 2],
    %69 := Ty.wrap #v[negWord t 0 >>> 51, negWord t 1 >>> 51],
    %70 := .value (negWord t 0),
    %71 := .value (negWord t 0 &&& 2251799813685247),
    %72 := Ty.wrap #v[negWord t 1 &&& 2251799813685247, negWord t 2 &&& 2251799813685247],
    %73 := Ty.wrap #v[negResult t 1, negResult t 2],
    %74 := .value (out.add 184#64),
    %75 := Ty.wrap #v[t 3, t 4],
    %76 := Ty.wrap #v[negWord t 3, negWord t 4],
    %77 := .value (negWord t 4),
    %78 := .value (negWord t 4 >>> 51),
    %79 := Ty.wrap #v[negWord t 3 &&& 2251799813685247, negWord t 4 &&& 2251799813685247],
    %80 := .value ((negWord t 4 >>> 51) * 19),
    %81 := Ty.wrap #v[negWord t 2, negWord t 3],
    %82 := Ty.wrap #v[negWord t 2 >>> 51, negWord t 3 >>> 51],
    %83 := .value (negResult t 0),
    %84 := Ty.wrap #v[negResult t 3, negResult t 4],
    %86 := .value (0#8)]



theorem unflatten_pack2 (a b : BitVec 64) :
    (Ty.vec 2 64).unflatten (BitVec.packLanes #v[a,b]) = Ty.wrap #v[a,b] :=
  Ty.unflatten_flatten (Ty.flatten_wrap_vec _)

theorem read_other (m : MemoryState) (dst src : Pointer) (x : BitVec w)
    (hne : dst.id ≠ src.id) : (m.storeAt dst x).readAt src n = m.readAt src n :=
  MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hne) _

theorem success_block (E : Env program.Γ) (initial s : GlobalState)
    (out bytes : Pointer) (x t : Words)
    (hout : E.read (%arg0) = .value out) (hbytes : E.read (%arg1) = .value bytes)
    (hor : SmallRange s.mem out 200)
    (hpr : SmallRange s.mem (optionSlot initial) 168)
    (hbr : SmallRange s.mem bytes 32)
    (hop : out.id ≠ (optionSlot initial).id) (hob : out.id ≠ bytes.id)
    (hreads : NegationReads s (optionSlot initial) x t) :
    program.bb1.run program.blockParams (entryEnv E initial true) s =
      .value ((successEnv (entryEnv E initial true) out (optionSlot initial) x t, .inr 3),
        payloadState s out (optionSlot initial) bytes x t) := by
  change E.args 0 = .value out at hout
  change E.args 1 = .value bytes at hbytes
  let opt := optionSlot initial
  let y := s.mem.readAt (opt.add 48#64) 320
  let z := s.mem.readAt (opt.add 88#64) 320
  let m1 := s.mem.storeAt (out.add 80#64) y
  let m2 := m1.storeAt (out.add 120#64) z
  have ho1 := hor.storeAt (out.add 80#64) y
  have hp1 := hpr.storeAt (out.add 80#64) y
  have ho2 := ho1.storeAt (out.add 120#64) z
  have hp2 := hp1.storeAt (out.add 120#64) z
  have hb2 := (hbr.storeAt (out.add 80#64) y).storeAt (out.add 120#64) z
  have hgp8 := hpr.gep (k := 8) (by decide)
  have hgp16 := hpr.gep (k := 16) (by decide)
  have hgp32 := hpr.gep (k := 32) (by decide)
  have hgp48 := hpr.gep (k := 48) (by decide)
  have hgo80 := hor.gep (k := 80) (by decide)
  have hgp88 := hp1.gep (k := 88) (by decide)
  have hgo120 := ho1.gep (k := 120) (by decide)
  have hgp128 := hp2.gep (k := 128) (by decide)
  have hgp136 := hp2.gep (k := 136) (by decide)
  have hgp152 := hp2.gep (k := 152) (by decide)
  have hgo8 := ho2.gep (k := 8) (by decide)
  have hgo40 := ho2.gep (k := 40) (by decide)
  have hgo48 := ho2.gep (k := 48) (by decide)
  have hgo64 := ho2.gep (k := 64) (by decide)
  have hgo160 := ho2.gep (k := 160) (by decide)
  have hgo168 := ho2.gep (k := 168) (by decide)
  have hgo184 := ho2.gep (k := 184) (by decide)
  have hfyout := hor.fits_add (k := 80) (count := 40) (by decide)
  have hfyin := hpr.fits_add (k := 48) (count := 40) (by decide)
  have hfzout := ho1.fits_add (k := 120) (count := 40) (by decide)
  have hfzin := hp1.fits_add (k := 88) (count := 40) (by decide)
  have hfr8 := hp2.fits_add (k := 8) (count := 16) (by decide)
  have hfr16 := hp2.fits_add (k := 16) (count := 16) (by decide)
  have hfr32 := hp2.fits_add (k := 32) (count := 16) (by decide)
  have hfr128 := hp2.fits_add (k := 128) (count := 16) (by decide)
  have hfr136 := hp2.fits_add (k := 136) (count := 16) (by decide)
  have hfr152 := hp2.fits_add (k := 152) (count := 16) (by decide)
  have hdY : (Range.of (out.add 80#64) 320).Disjoint (Range.of (opt.add 48#64) 320) :=
    Range.disjoint_of_id_ne hop
  have hdZ : (Range.of (out.add 120#64) 320).Disjoint (Range.of (opt.add 88#64) 320) :=
    Range.disjoint_of_id_ne hop
  have hdB : (Range.of (out.add 8#64) 256).Disjoint (Range.of bytes 256) :=
    Range.disjoint_of_id_ne hob
  have hof := ho2.fits_add (k := 8) (count := 32) (by decide)
  have hoS0 := ho2.storeAt (out.add 8#64) (s.mem.readAt bytes 256)
  have hfS0 := hoS0.fits_add (k := 40) (count := 8) (by decide)
  have hoS1 := hoS0.storeAt (out.add 40#64) (negResult x 0)
  have hfS1 := hoS1.fits_add (k := 48) (count := 16) (by decide)
  have hoS2 := hoS1.storeAt (out.add 48#64) (BitVec.packLanes #v[negResult x 1, negResult x 2])
  have hfS2 := hoS2.fits_add (k := 64) (count := 16) (by decide)
  have hoS3 := hoS2.storeAt (out.add 64#64) (BitVec.packLanes #v[negResult x 3, negResult x 4])
  have hfS3 := hoS3.fits_add (k := 160) (count := 8) (by decide)
  have hoS4 := hoS3.storeAt (out.add 160#64) (negResult t 0)
  have hfS4 := hoS4.fits_add (k := 168) (count := 16) (by decide)
  have hoS5 := hoS4.storeAt (out.add 168#64) (BitVec.packLanes #v[negResult t 1, negResult t 2])
  have hfS5 := hoS5.fits_add (k := 184) (count := 16) (by decide)
  have hzread : m1.readAt (opt.add 88#64) 320 = z := by
    exact read_other _ _ _ _ hop
  have hpread (k : BitVec 64) (w : Nat) : m2.readAt (opt.add k) w =
      s.mem.readAt (opt.add k) w := by
    dsimp only [m2, m1]
    rw [read_other _ (out.add 120#64) (opt.add k) z hop,
      read_other _ (out.add 80#64) (opt.add k) y hop]
  have hbread : m2.readAt bytes 256 = s.mem.readAt bytes 256 := by
    dsimp only [m2, m1]
    rw [read_other _ (out.add 120#64) bytes z hob,
      read_other _ (out.add 80#64) bytes y hob]
  rcases hreads with ⟨hx01,hx12,hx34,ht01,ht12,ht34⟩
  norm_num only [Nat.cast_ofNat, Nat.reduceMul] at *
  simp only [opt, m1, m2, y, z, Fits.storeAt_iff] at *
  simp [BasicBlock.run, program.bb1, entryEnv, successEnv, payloadState, copyYZ,
    List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    Operation.memcpy, Operation.load, Operation.store, throwUBIf,
    hout, hbytes, GepIndex.inboundsOffset,
    hgp8, hgp16, hgp32, hgp48, hgo80, hgp88, hgo120, hgp128, hgp136, hgp152, hgo8, hgo40, hgo48, hgo64, hgo160, hgo168, hgo184,
    hfyout, hfyin, hfzout, hfzin, hfr8, hfr16, hfr32, hfr128, hfr136, hfr152, hdY, hdZ, hdB, hof, hb2.fits, hfS0, hfS1, hfS2, hfS3, hfS4, hfS5,
    hzread, hpread, hbread, hop, hob, Pointer.add_id,
    hx01,hx12,hx34,ht01,ht12,ht34,
    unflatten_pack2, Ty.flatten_wrap_vec,
    BinOp.compute, mlir_operation,
    negWord, negResult, carry_mask51_flags, fold_mask51_flags, Reduce64.high_mul19_flags,
    Exit.run, Jump.run, program.blockParams, Regs.read_cons, Regs.read_nil,
    Env.writeMany_cons, Env.writeMany_nil,
    opt, m1, m2, y, z]
  rfl

end Agave.Ed25519.Verifier.Execution.Key
