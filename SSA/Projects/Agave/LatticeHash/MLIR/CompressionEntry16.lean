/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.agave_compress_pre_16
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Agave.LatticeHash.Compression
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Globals

namespace AgaveLatticeHash.MLIR.CompressionEntry
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression
abbrev V16 := SLLVM.Ty.arith (.vector 16 (.bitvec 32))

abbrev header16 (initial : State (Vector Word 16)) : SuccArgs agave_compress_pre_16.cfgSigs :=
  ⟨0, rfl, ([PoisonOr.value (0 : BitVec 64),
    (initial 0).map PoisonOr.value,
    (initial 1).map PoisonOr.value,
    (initial 2).map PoisonOr.value,
    (initial 3).map PoisonOr.value,
    (initial 4).map PoisonOr.value,
    (initial 5).map PoisonOr.value,
    (initial 6).map PoisonOr.value,
    (initial 7).map PoisonOr.value,
    (initial 8).map PoisonOr.value,
    (initial 9).map PoisonOr.value,
    (initial 10).map PoisonOr.value,
    (initial 11).map PoisonOr.value,
    (initial 12).map PoisonOr.value,
    (initial 13).map PoisonOr.value,
    (initial 14).map PoisonOr.value,
    (initial 15).map PoisonOr.value ]ₕ : HVector TyDenote.toType [SLLVM.Ty.bitvec 64, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16, V16])⟩

/-- Exact entry valuation of the compiled sixteen-lane kernel. -/
noncomputable def entryVal16 (out cv iv msg lo hi len flags sched : Pointer)
    (initial : State (Vector Word 16)) : agave_compress_pre_16.cfgCtx.Valuation :=
  Ctxt.Valuation.ofHVector (
    ((initial 11).map PoisonOr.value) ::ₕ
    PoisonOr.value (iv.withOffset 192) ::ₕ
    ((initial 10).map PoisonOr.value) ::ₕ
    PoisonOr.value (iv.withOffset 128) ::ₕ
    ((initial 9).map PoisonOr.value) ::ₕ
    PoisonOr.value (iv.withOffset 64) ::ₕ
    ((initial 8).map PoisonOr.value) ::ₕ
    ((initial 7).map PoisonOr.value) ::ₕ
    PoisonOr.value (cv.withOffset 448) ::ₕ
    ((initial 6).map PoisonOr.value) ::ₕ
    PoisonOr.value (cv.withOffset 384) ::ₕ
    ((initial 5).map PoisonOr.value) ::ₕ
    PoisonOr.value (cv.withOffset 320) ::ₕ
    ((initial 4).map PoisonOr.value) ::ₕ
    PoisonOr.value (cv.withOffset 256) ::ₕ
    ((initial 3).map PoisonOr.value) ::ₕ
    PoisonOr.value (cv.withOffset 192) ::ₕ
    ((initial 2).map PoisonOr.value) ::ₕ
    PoisonOr.value (cv.withOffset 128) ::ₕ
    ((initial 1).map PoisonOr.value) ::ₕ
    PoisonOr.value (cv.withOffset 64) ::ₕ
    ((initial 0).map PoisonOr.value) ::ₕ
    ((initial 15).map PoisonOr.value) ::ₕ
    ((initial 14).map PoisonOr.value) ::ₕ
    ((initial 13).map PoisonOr.value) ::ₕ
    ((initial 12).map PoisonOr.value) ::ₕ
    PoisonOr.value (960 : BitVec 64) ::ₕ
    PoisonOr.value (896 : BitVec 64) ::ₕ
    PoisonOr.value (832 : BitVec 64) ::ₕ
    PoisonOr.value (768 : BitVec 64) ::ₕ
    PoisonOr.value (704 : BitVec 64) ::ₕ
    PoisonOr.value (640 : BitVec 64) ::ₕ
    PoisonOr.value (576 : BitVec 64) ::ₕ
    PoisonOr.value (512 : BitVec 64) ::ₕ
    PoisonOr.value (7 : BitVec 64) ::ₕ
    PoisonOr.value (112 : BitVec 64) ::ₕ
    PoisonOr.value (120 : BitVec 64) ::ₕ
    PoisonOr.value (96 : BitVec 64) ::ₕ
    PoisonOr.value (104 : BitVec 64) ::ₕ
    PoisonOr.value (80 : BitVec 64) ::ₕ
    PoisonOr.value (88 : BitVec 64) ::ₕ
    PoisonOr.value (72 : BitVec 64) ::ₕ
    PoisonOr.value (48 : BitVec 64) ::ₕ
    PoisonOr.value (56 : BitVec 64) ::ₕ
    PoisonOr.value (32 : BitVec 64) ::ₕ
    PoisonOr.value (40 : BitVec 64) ::ₕ
    PoisonOr.value (16 : BitVec 64) ::ₕ
    PoisonOr.value (24 : BitVec 64) ::ₕ
    (Vector.replicate 16 (PoisonOr.value (25 : Word))) ::ₕ
    (Vector.replicate 16 (PoisonOr.value (24 : Word))) ::ₕ
    (Vector.replicate 16 (PoisonOr.value (20 : Word))) ::ₕ
    (Vector.replicate 16 (PoisonOr.value (16 : Word))) ::ₕ
    PoisonOr.value (8 : BitVec 64) ::ₕ
    PoisonOr.value sched ::ₕ
    PoisonOr.value (1 : BitVec 64) ::ₕ
    PoisonOr.value (0 : BitVec 64) ::ₕ
    PoisonOr.value (448 : BitVec 64) ::ₕ
    PoisonOr.value (384 : BitVec 64) ::ₕ
    PoisonOr.value (320 : BitVec 64) ::ₕ
    PoisonOr.value (256 : BitVec 64) ::ₕ
    PoisonOr.value (192 : BitVec 64) ::ₕ
    PoisonOr.value (128 : BitVec 64) ::ₕ
    PoisonOr.value (64 : BitVec 64) ::ₕ
    PoisonOr.value flags ::ₕ
    PoisonOr.value len ::ₕ
    PoisonOr.value hi ::ₕ
    PoisonOr.value lo ::ₕ
    PoisonOr.value msg ::ₕ
    PoisonOr.value iv ::ₕ
    PoisonOr.value cv ::ₕ
    PoisonOr.value out ::ₕ
    HVector.nil : HVector TyDenote.toType [V16, SLLVM.Ty.ptr, V16, SLLVM.Ty.ptr, V16, SLLVM.Ty.ptr, V16, V16, SLLVM.Ty.ptr, V16, SLLVM.Ty.ptr, V16, SLLVM.Ty.ptr, V16, SLLVM.Ty.ptr, V16, SLLVM.Ty.ptr, V16, SLLVM.Ty.ptr, V16, SLLVM.Ty.ptr, V16, V16, V16, V16, V16, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, V16, V16, V16, V16, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr])

/-- Execute the compiler-emitted entry block up to its actual loop header.
This theorem does not assume a compression result: its preconditions only
specify the input memory and the global schedule's address. -/
theorem entry16_run (s : GlobalState) (out cv iv msg lo hi len flags sched : Pointer)
    (initial : State (Vector Word 16))
    (hcv : Fits s.mem cv 4096) (hiv : Fits s.mem iv 2048)
    (hlo : Fits s.mem lo 512) (hhi : Fits s.mem hi 512)
    (hlen : Fits s.mem len 512) (hflags : Fits s.mem flags 512)
    (rcv : ∀ i : Fin 8, readWord? (cv.withOffset (BitVec.ofNat 64 (64*i.val))) 512 s.mem =
      some (packBits (initial (i.castAdd 8))))
    (riv : ∀ i : Fin 4, readWord? (iv.withOffset (BitVec.ofNat 64 (64*i.val))) 512 s.mem =
      some (packBits (initial ⟨8+i.val, by omega⟩)))
    (rlo : readWord? lo 512 s.mem = some (packBits (initial 12)))
    (rhi : readWord? hi 512 s.mem = some (packBits (initial 13)))
    (rlen : readWord? len 512 s.mem = some (packBits (initial 14)))
    (rflags : readWord? flags 512 s.mem = some (packBits (initial 15)))
    (hg : GlobalPtr s "alloc_61fb4a9344bbdaf2573accd6331d7e32" sched) :
    StateT.run (agave_compress_pre_16.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value len, .value hi, .value lo,
       .value msg, .value iv, .value cv, .value out]ₕ)) s =
    StateT.run (agave_compress_pre_16.blocks.run
      (entryVal16 out cv iv msg lo hi len flags sched initial) (header16 initial)) s := by
  simp only [Cfg.denote]
  dsimp only [agave_compress_pre_16]
  denote_step_reduce v 8 [LLVM.const?]
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8
  peel_addressof hg
  denote_step_reduce v 36 [LLVM.const?]
  subst hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28 hv29 hv30 hv31 hv32 hv33 hv34 hv35 hv36
  peel_load_vector (initial 12), lo, hlo, rlo, s
  peel_load_vector (initial 13), hi, hhi, rhi, s
  peel_load_vector (initial 14), len, hlen, rlen, s
  peel_load_vector (initial 15), flags, hflags, rflags, s
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s)
    (by simp [Expr.denoteOp, simp_denote, simp_sllvm])]
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s)
    (by simp [Expr.denoteOp, simp_denote, simp_sllvm])]
  have rcv0 : readWord? cv 512 s.mem = some (packBits (initial 0)) := by
    simpa [Pointer.withOffset] using rcv (0 : Fin 8)
  peel_load_vector (initial 0), cv, (Fits.mono hcv (by omega)), rcv0, s
  peel_gep 64 with cv, hcv, s as cv1
  have rcv1 : readWord? cv1 512 s.mem = some (packBits (initial 1)) := by
    simpa [cv1, Pointer.withOffset] using rcv (1 : Fin 8)
  peel_load_vector (initial 1), cv1, (Fits.mono hcv1 (by omega)), rcv1, s
  peel_gep 128 with cv, hcv, s as cv2
  have rcv2 : readWord? cv2 512 s.mem = some (packBits (initial 2)) := by
    simpa [cv2, Pointer.withOffset] using rcv (2 : Fin 8)
  peel_load_vector (initial 2), cv2, (Fits.mono hcv2 (by omega)), rcv2, s
  peel_gep 192 with cv, hcv, s as cv3
  have rcv3 : readWord? cv3 512 s.mem = some (packBits (initial 3)) := by
    simpa [cv3, Pointer.withOffset] using rcv (3 : Fin 8)
  peel_load_vector (initial 3), cv3, (Fits.mono hcv3 (by omega)), rcv3, s
  peel_gep 256 with cv, hcv, s as cv4
  have rcv4 : readWord? cv4 512 s.mem = some (packBits (initial 4)) := by
    simpa [cv4, Pointer.withOffset] using rcv (4 : Fin 8)
  peel_load_vector (initial 4), cv4, (Fits.mono hcv4 (by omega)), rcv4, s
  peel_gep 320 with cv, hcv, s as cv5
  have rcv5 : readWord? cv5 512 s.mem = some (packBits (initial 5)) := by
    simpa [cv5, Pointer.withOffset] using rcv (5 : Fin 8)
  peel_load_vector (initial 5), cv5, (Fits.mono hcv5 (by omega)), rcv5, s
  peel_gep 384 with cv, hcv, s as cv6
  have rcv6 : readWord? cv6 512 s.mem = some (packBits (initial 6)) := by
    simpa [cv6, Pointer.withOffset] using rcv (6 : Fin 8)
  peel_load_vector (initial 6), cv6, (Fits.mono hcv6 (by omega)), rcv6, s
  peel_gep 448 with cv, hcv, s as cv7
  have rcv7 : readWord? cv7 512 s.mem = some (packBits (initial 7)) := by
    simpa [cv7, Pointer.withOffset] using rcv (7 : Fin 8)
  peel_load_vector (initial 7), cv7, (Fits.mono hcv7 (by omega)), rcv7, s
  have riv0 : readWord? iv 512 s.mem = some (packBits (initial 8)) := by
    simpa [Pointer.withOffset] using riv (0 : Fin 4)
  peel_load_vector (initial 8), iv, (Fits.mono hiv (by omega)), riv0, s
  peel_gep 64 with iv, hiv, s as iv1
  have riv1 : readWord? iv1 512 s.mem = some (packBits (initial 9)) := by
    simpa [iv1, Pointer.withOffset] using riv (1 : Fin 4)
  peel_load_vector (initial 9), iv1, (Fits.mono hiv1 (by omega)), riv1, s
  peel_gep 128 with iv, hiv, s as iv2
  have riv2 : readWord? iv2 512 s.mem = some (packBits (initial 10)) := by
    simpa [iv2, Pointer.withOffset] using riv (2 : Fin 4)
  peel_load_vector (initial 10), iv2, (Fits.mono hiv2 (by omega)), riv2, s
  peel_gep 192 with iv, hiv, s as iv3
  have riv3 : readWord? iv3 512 s.mem = some (packBits (initial 11)) := by
    simpa [iv3, Pointer.withOffset] using riv (3 : Fin 4)
  peel_load_vector (initial 11), iv3, (Fits.mono hiv3 (by omega)), riv3, s
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  rfl

end AgaveLatticeHash.MLIR.CompressionEntry
