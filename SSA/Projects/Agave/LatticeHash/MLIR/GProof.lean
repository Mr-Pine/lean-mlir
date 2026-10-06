import SSA.Projects.Agave.LatticeHash.MLIR.agave_g_8
import SSA.Projects.Agave.LatticeHash.MLIR.agave_g_16
import SSA.Projects.Agave.LatticeHash.MLIR.agave_portable_g
import SSA.Projects.Agave.LatticeHash.MLIR.GArithmetic
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Firedancer.Proof.Tactics

/-!
Refinement of the compiler-emitted AVX2, AVX-512 and portable G helpers. The imported
regions come from the pinned Rust source extraction; the proofs execute those
CFGs, including loads, three pointer offsets and four stores. The portable
helper is independently extracted from the locked BLAKE3 reference source.

Bounds and byte-read hypotheses describe arbitrary initial memory. No input
values are fixed. The resulting memory is the exact store chain, and
`gVectors_lane` identifies every output lane with the existing `scalarG`.
`gMemory_frame` preserves unrelated blocks; `gMemory_popFrame` handles return
from the call in any well-formed caller state.
-/

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression

/-- The four stores emitted by the actual Rust helper, in their emitted order. -/
def gMemory {n : Nat} (m : MemoryState) (p : Pointer) (q : Quad (Vector Word n)) : MemoryState :=
  let m := m.splice p (packBits q.a)
  let m := m.splice (p.withOffset (BitVec.ofNat 64 (48*n))) (packBits q.d)
  let m := m.splice (p.withOffset (BitVec.ofNat 64 (32*n))) (packBits q.c)
  m.splice (p.withOffset (BitVec.ofNat 64 (16*n))) (packBits q.b)

/-- No block outside the mutated state buffer changes. -/
theorem gMemory_frame {n : Nat} (m : MemoryState) (p : Pointer) (q : Quad (Vector Word n))
    (b : BlockId) (hb : p.id ≠ b) : (gMemory m p q).live? b = m.live? b := by
  unfold gMemory
  simp only [live?_splice_ne (p := p.withOffset _) hb, live?_splice_ne hb]

/-- Execute the compiler-emitted eight-lane helper on arbitrary defined input words. -/
theorem agave_g_8_run (s : GlobalState) (p mx my : Pointer)
    (a b c d x y : Vector Word 8)
    (hp : Fits s.mem p 4096) (hx : Fits s.mem mx 256) (hy : Fits s.mem my 256)
    (ha : readWord? p 256 s.mem = some (packBits a))
    (hb : readWord? (p.withOffset 128) 256 s.mem = some (packBits b))
    (hc : readWord? (p.withOffset 256) 256 s.mem = some (packBits c))
    (hd : readWord? (p.withOffset 384) 256 s.mem = some (packBits d))
    (hxr : readWord? mx 256 s.mem = some (packBits x))
    (hyr : readWord? my 256 s.mem = some (packBits y)) :
    StateT.run (agave_g_8.denote (Ctxt.Valuation.ofHVector
      [.value my, .value mx, .value p]ₕ)) s =
      .value ([]ₕ, { s with mem := gMemory s.mem p (gVectors a b c d x y) }) := by
  simp only [Cfg.denote]
  dsimp only [agave_g_8]
  denote_step_all v 6
  denote_eval v 0 6
  simp only [LLVM.const?] at hv0 hv1 hv3
  subst hv0; subst hv1; subst hv3
  peel_load_vector x, mx, hx, hxr, s
  peel_load_vector y, my, hy, hyr, s
  peel_load_vector a, p, (Fits.mono hp (by omega)), ha, s
  peel_gep 128 with p, hp, s as pb
  peel_load_vector b, pb, (Fits.mono hpb (by omega)), hb, s
  denote_step_all v 13
  denote_eval v 12 13
  peel_gep 384 with p, hp, s as pd
  peel_load_vector d, pd, (Fits.mono hpd (by omega)), hd, s
  denote_step_all v 17
  denote_eval v 16 17
  peel_gep 256 with p, hp, s as pc
  peel_load_vector c, pc, (Fits.mono hpc (by omega)), hc, s
  denote_step_all v 24
  denote_eval v 20 24
  have ea : v24 = (gVectors a b c d x y).a.map PoisonOr.value := by
    simp only [hv24, hv23, hv22, hv21, hv20, hv17, hv16, hv13, hv12, hv2, hv4]
    apply Vector.ext
    intro i hi
    simp [gVectors, compiledG, InstCombine.binaryDenote, simp_llvm, simp_llvm_option,
      vfshl, fshl, LLVM.Ty.dense]
  rw [ea]
  let q := gVectors a b c d x y
  let s1 : GlobalState := { s with mem := s.mem.splice p (packBits q.a) }
  have hs1 : s1 = { s with mem := s.mem.splice p (packBits q.a) } := rfl
  peel_store_vector q.a, p, hp, s as s1 := hs1
  denote_step_all v 26
  denote_eval v 25 26
  have ed : v26 = q.d.map PoisonOr.value := by
    simp only [hv26, hv25, hv17, hv16, hv13, hv12, hv2, hv5]
    apply Vector.ext
    intro i hi
    simp [q, gVectors, compiledG, InstCombine.binaryDenote, simp_llvm, simp_llvm_option,
      vfshl, fshl, LLVM.Ty.dense]
  rw [ed]
  let s2 : GlobalState := { s1 with mem := s1.mem.splice pd (packBits q.d) }
  have hs2 : s2 = { s1 with mem := s1.mem.splice pd (packBits q.d) } := rfl
  have hpd1 : Fits s1.mem pd 1024 := fits_splice hpd
  peel_store_vector q.d, pd, hpd1, s1 as s2 := hs2
  denote_step_all v 27
  denote_eval v 27 27
  have ec : v27 = q.c.map PoisonOr.value := by
    simp only [hv27, hv20, hv17, hv16, hv13, hv12, hv2]
    apply Vector.ext
    intro i hi
    simp [q, gVectors, compiledG, InstCombine.binaryDenote, simp_llvm, simp_llvm_option,
      vfshl, fshl, LLVM.Ty.dense]
  rw [ec]
  let s3 : GlobalState := { s2 with mem := s2.mem.splice pc (packBits q.c) }
  have hs3 : s3 = { s2 with mem := s2.mem.splice pc (packBits q.c) } := rfl
  have hpc2 : Fits s2.mem pc 2048 := fits_splice (fits_splice hpc)
  peel_store_vector q.c, pc, hpc2, s2 as s3 := hs3
  denote_step_all v 29
  denote_eval v 28 29
  have eb : v29 = q.b.map PoisonOr.value := by
    simp only [hv29, hv28, hv22, hv21, hv20, hv17, hv16, hv13, hv12, hv2, hv4, hv6]
    apply Vector.ext
    intro i hi
    simp [q, gVectors, compiledG, InstCombine.binaryDenote, simp_llvm, simp_llvm_option,
      vfshl, fshl, LLVM.Ty.dense]
  rw [eb]
  have hpb3 : Fits s3.mem pb 3072 := fits_splice (fits_splice (fits_splice hpb))
  peel_store_vector q.b, pb, hpb3, s3
  simp_return
  exact ⟨rfl, rfl, rfl⟩

/-- Execute the compiler-emitted sixteen-lane helper on arbitrary defined input words. -/
theorem agave_g_16_run (s : GlobalState) (p mx my : Pointer)
    (a b c d x y : Vector Word 16)
    (hp : Fits s.mem p 8192) (hx : Fits s.mem mx 512) (hy : Fits s.mem my 512)
    (ha : readWord? p 512 s.mem = some (packBits a))
    (hb : readWord? (p.withOffset 256) 512 s.mem = some (packBits b))
    (hc : readWord? (p.withOffset 512) 512 s.mem = some (packBits c))
    (hd : readWord? (p.withOffset 768) 512 s.mem = some (packBits d))
    (hxr : readWord? mx 512 s.mem = some (packBits x))
    (hyr : readWord? my 512 s.mem = some (packBits y)) :
    StateT.run (agave_g_16.denote (Ctxt.Valuation.ofHVector
      [.value my, .value mx, .value p]ₕ)) s =
      .value ([]ₕ, { s with mem := gMemory s.mem p (gVectors a b c d x y) }) := by
  simp only [Cfg.denote]
  dsimp only [agave_g_16]
  denote_step_all v 6
  denote_eval v 0 6
  simp only [LLVM.const?] at hv0 hv1 hv3
  subst hv0; subst hv1; subst hv3
  peel_load_vector x, mx, hx, hxr, s
  peel_load_vector y, my, hy, hyr, s
  peel_load_vector a, p, (Fits.mono hp (by omega)), ha, s
  peel_gep 256 with p, hp, s as pb
  peel_load_vector b, pb, (Fits.mono hpb (by omega)), hb, s
  denote_step_all v 13
  denote_eval v 12 13
  peel_gep 768 with p, hp, s as pd
  peel_load_vector d, pd, (Fits.mono hpd (by omega)), hd, s
  denote_step_all v 17
  denote_eval v 16 17
  peel_gep 512 with p, hp, s as pc
  peel_load_vector c, pc, (Fits.mono hpc (by omega)), hc, s
  denote_step_all v 24
  denote_eval v 20 24
  have ea : v24 = (gVectors a b c d x y).a.map PoisonOr.value := by
    simp only [hv24, hv23, hv22, hv21, hv20, hv17, hv16, hv13, hv12, hv2, hv4]
    apply Vector.ext
    intro i hi
    simp [gVectors, compiledG, InstCombine.binaryDenote, simp_llvm, simp_llvm_option,
      vfshl, fshl, LLVM.Ty.dense]
  rw [ea]
  let q := gVectors a b c d x y
  let s1 : GlobalState := { s with mem := s.mem.splice p (packBits q.a) }
  have hs1 : s1 = { s with mem := s.mem.splice p (packBits q.a) } := rfl
  peel_store_vector q.a, p, hp, s as s1 := hs1
  denote_step_all v 26
  denote_eval v 25 26
  have ed : v26 = q.d.map PoisonOr.value := by
    simp only [hv26, hv25, hv17, hv16, hv13, hv12, hv2, hv5]
    apply Vector.ext
    intro i hi
    simp [q, gVectors, compiledG, InstCombine.binaryDenote, simp_llvm, simp_llvm_option,
      vfshl, fshl, LLVM.Ty.dense]
  rw [ed]
  let s2 : GlobalState := { s1 with mem := s1.mem.splice pd (packBits q.d) }
  have hs2 : s2 = { s1 with mem := s1.mem.splice pd (packBits q.d) } := rfl
  have hpd1 : Fits s1.mem pd 2048 := fits_splice hpd
  peel_store_vector q.d, pd, hpd1, s1 as s2 := hs2
  denote_step_all v 27
  denote_eval v 27 27
  have ec : v27 = q.c.map PoisonOr.value := by
    simp only [hv27, hv20, hv17, hv16, hv13, hv12, hv2]
    apply Vector.ext
    intro i hi
    simp [q, gVectors, compiledG, InstCombine.binaryDenote, simp_llvm, simp_llvm_option,
      vfshl, fshl, LLVM.Ty.dense]
  rw [ec]
  let s3 : GlobalState := { s2 with mem := s2.mem.splice pc (packBits q.c) }
  have hs3 : s3 = { s2 with mem := s2.mem.splice pc (packBits q.c) } := rfl
  have hpc2 : Fits s2.mem pc 4096 := fits_splice (fits_splice hpc)
  peel_store_vector q.c, pc, hpc2, s2 as s3 := hs3
  denote_step_all v 29
  denote_eval v 28 29
  have eb : v29 = q.b.map PoisonOr.value := by
    simp only [hv29, hv28, hv22, hv21, hv20, hv17, hv16, hv13, hv12, hv2, hv4, hv6]
    apply Vector.ext
    intro i hi
    simp [q, gVectors, compiledG, InstCombine.binaryDenote, simp_llvm, simp_llvm_option,
      vfshl, fshl, LLVM.Ty.dense]
  rw [eb]
  have hpb3 : Fits s3.mem pb 6144 := fits_splice (fits_splice (fits_splice hpb))
  peel_store_vector q.b, pb, hpb3, s3
  simp_return
  exact ⟨rfl, rfl, rfl⟩


private theorem run_load_word {m : MemoryState} {p : Pointer} (x : Word)
    (hp : Fits m p 32) (hr : readWord? p 32 m = some x) :
    (load (.value p) (.bitvec (.concrete 32))).run m = .value (.value x, m) := by
  obtain ⟨block, hblk, hlen⟩ := hp
  have hread : block.bytes.extractLsb' p.offsetInBits 32 = x := by
    simpa [readWord?, MemoryState.live?, hblk] using hr
  rw [run_load (t := .bitvec (.concrete 32)) hblk hlen]
  simp only [LLVM.Ty.width]
  rw [hread]
  rfl

macro "peel_g_word " x:term ", " p:term ", " hp:term ", " hr:term ", " st:term : tactic =>
  `(tactic|
    (try simp only [bind_assoc]
     reduce_cfg_indices
     rw [BlockCom.run_bind_denote_var_of_value (x := PoisonOr.value $x) (s' := $st)
       (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
           rw [run_liftM (run_load_word (p := $p) $x $hp $hr)]
           rfl)]))

/-- The scalar compiler output mutates the same four state positions. -/
def scalarGMemory (m : MemoryState) (p : Pointer) (q : Quad Word) : MemoryState :=
  (((m.splice p q.a).splice (p.withOffset 48) q.d).splice (p.withOffset 32) q.c).splice
    (p.withOffset 16) q.b

set_option maxHeartbeats 1200000 in
/-- Execution of the independently compiled portable Rust G implementation. -/
theorem agave_portable_g_run (s : GlobalState) (p : Pointer) (a b c d x y : Word)
    (hp : Fits s.mem p 512)
    (ha : readWord? p 32 s.mem = some a)
    (hb : readWord? (p.withOffset 16) 32 s.mem = some b)
    (hc : readWord? (p.withOffset 32) 32 s.mem = some c)
    (hd : readWord? (p.withOffset 48) 32 s.mem = some d) :
    StateT.run (agave_portable_g.denote (Ctxt.Valuation.ofHVector
      [.value y, .value x, .value p]ₕ)) s =
      .value ([]ₕ, { s with mem := scalarGMemory s.mem p (scalarG a b c d x y) }) := by
  simp only [Cfg.denote]
  dsimp only [agave_portable_g]
  denote_step_all v 6
  denote_eval v 0 6
  simp only [LLVM.const?] at hv0 hv1 hv2 hv3 hv4 hv5 hv6
  subst hv0; subst hv1; subst hv2; subst hv3; subst hv4; subst hv5; subst hv6
  peel_g_word a, p, (Fits.mono hp (by omega)), ha, s
  peel_gep 16 with p, hp, s as pb
  peel_g_word b, pb, (Fits.mono hpb (by omega)), hb, s
  denote_step_all v 11
  denote_eval v 10 11
  peel_gep 48 with p, hp, s as pd
  peel_g_word d, pd, (Fits.mono hpd (by omega)), hd, s
  denote_step_all v 15
  denote_eval v 14 15
  peel_gep 32 with p, hp, s as pc
  peel_g_word c, pc, (Fits.mono hpc (by omega)), hc, s
  denote_step_all v 22
  denote_eval v 18 22
  have ea : v22 = .value (scalarG a b c d x y).a := by
    simp only [hv22, hv21, hv20, hv19, hv18, hv15, hv14, hv11, hv10]
    simp [scalarG, simp_llvm, simp_llvm_option, fshl, funnel16_bits, funnel20_bits,
      BitVec.add_comm, BitVec.add_assoc, word_add_left_comm, BitVec.xor_comm]
  rw [ea]
  let q := scalarG a b c d x y
  let s1 : GlobalState := { s with mem := s.mem.splice p q.a }
  have hs1 : s1 = { s with mem := s.mem.splice p q.a } := rfl
  peel_store q.a, p, hp, s as s1 := hs1
  denote_step_all v 24
  denote_eval v 23 24
  have ed : v24 = .value q.d := by
    simp only [hv24, hv23, hv15, hv14, hv11, hv10]
    simp [q, scalarG, simp_llvm, simp_llvm_option, fshl, funnel16_bits, funnel24_bits,
      BitVec.add_comm, BitVec.add_assoc, word_add_left_comm, BitVec.xor_comm]
  rw [ed]
  let s2 : GlobalState := { s1 with mem := s1.mem.splice pd q.d }
  have hs2 : s2 = { s1 with mem := s1.mem.splice pd q.d } := rfl
  have hpd1 : Fits s1.mem pd 128 := fits_splice hpd
  peel_store q.d, pd, hpd1, s1 as s2 := hs2
  denote_step_all v 25
  denote_eval v 25 25
  have ec : v25 = .value q.c := by
    simp only [hv25, hv18, hv15, hv14, hv11, hv10]
    simp [q, scalarG, simp_llvm, simp_llvm_option, fshl, funnel16_bits,
      BitVec.add_comm, BitVec.add_assoc, word_add_left_comm]
  rw [ec]
  let s3 : GlobalState := { s2 with mem := s2.mem.splice pc q.c }
  have hs3 : s3 = { s2 with mem := s2.mem.splice pc q.c } := rfl
  have hpc2 : Fits s2.mem pc 256 := fits_splice (fits_splice hpc)
  peel_store q.c, pc, hpc2, s2 as s3 := hs3
  denote_step_all v 27
  denote_eval v 26 27
  have eb : v27 = .value q.b := by
    simp only [hv27, hv26, hv20, hv19, hv18, hv15, hv14, hv11, hv10]
    simp [q, scalarG, simp_llvm, simp_llvm_option, fshl, funnel16_bits, funnel20_bits, funnel25_bits,
      BitVec.add_comm, BitVec.add_assoc, word_add_left_comm, BitVec.xor_comm]
  rw [eb]
  have hpb3 : Fits s3.mem pb 384 := fits_splice (fits_splice (fits_splice hpb))
  peel_store q.b, pb, hpb3, s3
  simp_return
  exact ⟨rfl, rfl, rfl⟩

/-- The G stores cannot create a live allocation. -/
theorem gMemory_dead {n : Nat} {m : MemoryState} {p : Pointer}
    (q : Quad (Vector Word n)) {b : BlockId} (hb : m.live? b = none) :
    (gMemory m p q).live? b = none :=
  live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none hb)))

/-- Returning from G keeps the caller's allocations and all four output stores. -/
theorem gMemory_popFrame {n : Nat} (s : GlobalState) (hs : s.WF) (p : Pointer)
    (q : Quad (Vector Word n)) :
    s.popFrame (gMemory s.mem p q) ≈ ({ s with mem := gMemory s.mem p q } : GlobalState) :=
  killFrom_equiv_of_none (fun b hb => gMemory_dead q (hs b hb))

/-- Whole-function execution and caller-memory refinement of the emitted 8-lane G. -/
theorem agave_g_8_conforms (s : GlobalState) (hs : s.WF) (p mx my : Pointer)
    (a b c d x y : Vector Word 8)
    (hp : Fits s.mem p 4096) (hx : Fits s.mem mx 256) (hy : Fits s.mem my 256)
    (ha : readWord? p 256 s.mem = some (packBits a))
    (hb : readWord? (p.withOffset 128) 256 s.mem = some (packBits b))
    (hc : readWord? (p.withOffset 256) 256 s.mem = some (packBits c))
    (hd : readWord? (p.withOffset 384) 256 s.mem = some (packBits d))
    (hxr : readWord? mx 256 s.mem = some (packBits x))
    (hyr : readWord? my 256 s.mem = some (packBits y)) :
    ∃ s' : GlobalState,
      StateT.run (runFunction (agave_g_8.denote (Ctxt.Valuation.ofHVector
        [.value my, .value mx, .value p]ₕ))) s = .value ([]ₕ, s') ∧
      s' ≈ ({ s with mem := gMemory s.mem p (gVectors a b c d x y) } : GlobalState) := by
  exact ⟨s.popFrame (gMemory s.mem p (gVectors a b c d x y)),
    run_runFunction (s' := { s with mem := gMemory s.mem p (gVectors a b c d x y) }) (agave_g_8_run s p mx my a b c d x y hp hx hy ha hb hc hd hxr hyr),
    gMemory_popFrame s hs p (gVectors a b c d x y)⟩

/-- Whole-function execution and caller-memory refinement of the emitted 16-lane G. -/
theorem agave_g_16_conforms (s : GlobalState) (hs : s.WF) (p mx my : Pointer)
    (a b c d x y : Vector Word 16)
    (hp : Fits s.mem p 8192) (hx : Fits s.mem mx 512) (hy : Fits s.mem my 512)
    (ha : readWord? p 512 s.mem = some (packBits a))
    (hb : readWord? (p.withOffset 256) 512 s.mem = some (packBits b))
    (hc : readWord? (p.withOffset 512) 512 s.mem = some (packBits c))
    (hd : readWord? (p.withOffset 768) 512 s.mem = some (packBits d))
    (hxr : readWord? mx 512 s.mem = some (packBits x))
    (hyr : readWord? my 512 s.mem = some (packBits y)) :
    ∃ s' : GlobalState,
      StateT.run (runFunction (agave_g_16.denote (Ctxt.Valuation.ofHVector
        [.value my, .value mx, .value p]ₕ))) s = .value ([]ₕ, s') ∧
      s' ≈ ({ s with mem := gMemory s.mem p (gVectors a b c d x y) } : GlobalState) := by
  exact ⟨s.popFrame (gMemory s.mem p (gVectors a b c d x y)),
    run_runFunction (s' := { s with mem := gMemory s.mem p (gVectors a b c d x y) }) (agave_g_16_run s p mx my a b c d x y hp hx hy ha hb hc hd hxr hyr),
    gMemory_popFrame s hs p (gVectors a b c d x y)⟩

/-- The portable helper also preserves every unrelated live block. -/
theorem scalarGMemory_frame (m : MemoryState) (p : Pointer) (q : Quad Word)
    (b : BlockId) (hb : p.id ≠ b) : (scalarGMemory m p q).live? b = m.live? b := by
  unfold scalarGMemory
  simp only [live?_splice_ne (p := p.withOffset _) hb, live?_splice_ne hb]

/-- Whole-function refinement of the independently compiled portable helper. -/
theorem agave_portable_g_conforms (s : GlobalState) (hs : s.WF) (p : Pointer)
    (a b c d x y : Word) (hp : Fits s.mem p 512)
    (ha : readWord? p 32 s.mem = some a)
    (hb : readWord? (p.withOffset 16) 32 s.mem = some b)
    (hc : readWord? (p.withOffset 32) 32 s.mem = some c)
    (hd : readWord? (p.withOffset 48) 32 s.mem = some d) :
    ∃ s' : GlobalState,
      StateT.run (runFunction (agave_portable_g.denote (Ctxt.Valuation.ofHVector
        [.value y, .value x, .value p]ₕ))) s = .value ([]ₕ, s') ∧
      s' ≈ ({ s with mem := scalarGMemory s.mem p (scalarG a b c d x y) } : GlobalState) := by
  refine ⟨s.popFrame (scalarGMemory s.mem p (scalarG a b c d x y)),
    run_runFunction (s' := { s with mem := scalarGMemory s.mem p (scalarG a b c d x y) })
      (agave_portable_g_run s p a b c d x y hp ha hb hc hd), ?_⟩
  apply killFrom_equiv_of_none
  intro b hb
  exact live?_splice_eq_none
    (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (hs b hb))))

/-- The results stored by the three execution theorems agree when their selected
input lanes agree. Other SIMD lanes are unrestricted. -/
theorem g_threeway_lane (a8 b8 c8 d8 x8 y8 : Vector Word 8)
    (a16 b16 c16 d16 x16 y16 : Vector Word 16) (i : Fin 8) (j : Fin 16)
    (ha : a16[j] = a8[i]) (hb : b16[j] = b8[i]) (hc : c16[j] = c8[i])
    (hd : d16[j] = d8[i]) (hx : x16[j] = x8[i]) (hy : y16[j] = y8[i]) :
    let q8 := gVectors a8 b8 c8 d8 x8 y8
    let q16 := gVectors a16 b16 c16 d16 x16 y16
    let reference := scalarG a8[i] b8[i] c8[i] d8[i] x8[i] y8[i]
    (⟨q8.a[i], q8.b[i], q8.c[i], q8.d[i]⟩ : Quad Word) = reference ∧
    (⟨q16.a[j], q16.b[j], q16.c[j], q16.d[j]⟩ : Quad Word) = reference := by
  constructor
  · exact gVectors_lane a8 b8 c8 d8 x8 y8 i
  · simpa only [ha, hb, hc, hd, hx, hy] using gVectors_lane a16 b16 c16 d16 x16 y16 j

end AgaveLatticeHash.MLIR
