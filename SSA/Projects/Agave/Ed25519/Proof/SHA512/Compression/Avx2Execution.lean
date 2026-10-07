import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2Program
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Exact execution of the imported AVX2 backend's final sixteen scalar rounds.
The scratch invariant states the contents of the schedule produced by the preceding
vector loop; it does not assume any compression result. The loop itself only reads
scratch, so its memory and allocation counter are preserved exactly. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic

/-- Register interpretation at the actual bb6 header. -/
structure TailReady (E : Env program.Γ) (scratch : Pointer) (r : Nat) (s : Spec.State) : Prop where
  scratch : E.read (%81) = .value scratch
  counter : E.read (%272) = .value (BitVec.ofNat 64 r)
  a : E.read (%277) = .value s.a
  b : E.read (%278) = .value s.b
  c : E.read (%279) = .value s.c
  d : E.read (%280) = .value s.d
  e : E.read (%274) = .value s.e
  f : E.read (%276) = .value s.f
  g : E.read (%275) = .value s.g
  h : E.read (%273) = .value s.h
  one : E.read (%1) = .value 1#64
  limit : E.read (%17) = .value 80#64
  rot14 : E.read (%36) = .value 50#64
  rot18 : E.read (%37) = .value 46#64
  rot41 : E.read (%38) = .value 23#64
  rot28 : E.read (%39) = .value 36#64
  rot34 : E.read (%40) = .value 30#64
  rot39 : E.read (%41) = .value 25#64
  mask : E.read (%44) = .value 15#64

/-- The last sixteen K+W words occupy the sixteen scratch slots. This is
intended to be discharged by the preceding vector schedule loop. -/
structure TailSchedule (mem : MemoryState) (scratch : Pointer) (words : List Word) : Prop where
  live : SmallRange mem scratch 128
  words : ∀ r, 64 ≤ r → r < 80 →
    mem.readAt (scratch.add (BitVec.ofNat 64 (8 * (r - 64)))) 64 =
      constants.toList.getD r 0 + words.getD r 0

/-- Every instruction's destination, in the exact source order. -/
def tailBodyEnv (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) : Env program.Γ :=
  let v285 := s.e.rotateRight 14
  let v286 := s.e.rotateRight 18
  let v287 := v285 ^^^ v286
  let v288 := s.e.rotateRight 41
  let v289 := s.f ^^^ s.g
  let v290 := s.a.rotateRight 28
  let v291 := s.a.rotateRight 34
  let v292 := v290 ^^^ v291
  let v293 := s.a.rotateRight 39
  let v294 := v292 ^^^ v293
  let v295 := s.c ^^^ s.b
  let v296 := v295 &&& s.a
  let v297 := s.c &&& s.b
  let v298 := v296 ^^^ v297
  let v299 := s.h + kw
  let v300 := v287 ^^^ v288
  let v301 := v299 + v300
  let v302 := v289 &&& s.e
  let v303 := v302 ^^^ s.g
  let v304 := v301 + v303
  let v305 := v304 + v294
  let v306 := v305 + v298
  let v307 := s.d + v304
  E[%281 := .value (BitVec.ofNat 64 r &&& 15#64),
    %282 := .value (BitVec.ofNat 64 (r + 1)),
    %283 := .value (scratch.add (BitVec.ofNat 64 (8 * (r - 64)))),
    %284 := .value kw,
    %285 := .value v285, %286 := .value v286, %287 := .value v287,
    %288 := .value v288, %289 := .value v289, %290 := .value v290,
    %291 := .value v291, %292 := .value v292, %293 := .value v293,
    %294 := .value v294, %295 := .value v295, %296 := .value v296,
    %297 := .value v297, %298 := .value v298, %299 := .value v299,
    %300 := .value v300, %301 := .value v301, %302 := .value v302,
    %303 := .value v303, %304 := .value v304, %305 := .value v305,
    %306 := .value v306, %307 := .value v307,
    %308 := .value (BitVec.ofBool (decide (r + 1 = 80)))]

/-- The actual loop backedge assigns bb6's nine block parameters. -/
def tailNextEnv (E : Env program.Γ) (r : Nat) (s : Spec.State) : Env program.Γ :=
  E[%272 := .value (BitVec.ofNat 64 r),
    %273 := .value s.h, %274 := .value s.e, %275 := .value s.g,
    %276 := .value s.f, %277 := .value s.a, %278 := .value s.b,
    %279 := .value s.c, %280 := .value s.d]

/-- The exact emitted arithmetic expression, before Boolean normalization. -/
def tailRound (s : Spec.State) (kw : Word) : Spec.State :=
  let t := s.h + kw + bigSigma1 s.e + ((s.f ^^^ s.g) &&& s.e ^^^ s.g)
  ⟨t + bigSigma0 s.a + (((s.c ^^^ s.b) &&& s.a) ^^^ (s.c &&& s.b)),
    s.a, s.b, s.c, s.d + t, s.e, s.f, s.g⟩

theorem tailRound_eq (s : Spec.State) (word constant : Word) :
    tailRound s (constant + word) = Spec.round s word constant := by
  rw [← avxRound_eq_round]
  simp only [tailRound, avxRound, majority_source]
  congr 1 <;> ac_rfl

/-- Execute all 28 body instructions from the imported bb6. The source's
signed/unsigned counter flags and all three GEP flags are discharged. -/
theorem tail_body (E : Env program.Γ) (mem : GlobalState) (scratch : Pointer)
    (r : Nat) (s : Spec.State) (words : List Word)
    (hlo : 64 ≤ r) (hhi : r < 80)
    (h : TailReady E scratch r s) (hs : TailSchedule mem.mem scratch words) :
    List.foldlM Instr.run E program.bb6.body mem =
      .value (tailBodyEnv E scratch r s
        (constants.toList.getD r 0 + words.getD r 0), mem) := by
  rcases h with ⟨h81, h272, ha, hb, hc, hd, he, hf, hg, hh,
    h1, h17, h36, h37, h38, h39, h40, h41, h44⟩
  have hinc := tail_index_add r hlo hhi
  have hidx := tail_index_gep r hlo hhi
  have hgep := hs.live.gep (k := 8 * (r - 64)) (by omega)
  have hfits := hs.live.fits_add (k := 8 * (r - 64)) (count := 8) (by omega)
  have hread := hs.words r hlo hhi
  have heq := tail_index_eq80 r hhi
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb6, List.foldlM_cons, List.foldlM_nil, Instr.run,
    tailBodyEnv, h81, h272, ha, hb, hc, hd, he, hf, hg, hh,
    h1, h17, h36, h37, h38, h39, h40, h41, h44,
    hinc, hidx, hgep, hfits, hread, heq,
    GepIndex.inboundsOffset, Operation.load,
    Operation.and, Operation.xor, hadd, Operation.icmp,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.SHA512.Execution.Avx2
