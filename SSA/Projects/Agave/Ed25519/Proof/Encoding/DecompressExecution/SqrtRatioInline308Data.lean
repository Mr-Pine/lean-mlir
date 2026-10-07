import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlinePrefixSquare
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixOperations
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtWords

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure Constants (E : Env program.Γ) : Prop where
  c1 : E.read (%1) = .value 40#64
  c3 : E.read (%3) = .value 8#64
  c4 : E.read (%4) = .value 16#64
  c5 : E.read (%5) = .value 24#64
  c6 : E.read (%6) = .value 32#64
  c7 : E.read (%7) = .value 51#64
  c8 : E.read (%8) = .value 2251799813685247#64
  c9 : E.read (%9) = .value 19#64
  c10 : E.read (%10) = .value 1#64
  c11 : E.read (%11) = .value 2#64
  c12 : E.read (%12) = .value 3#64
  c13 : E.read (%13) = .value 4#64
  c14 : E.read (%14) = .value 5#64
  c15 : E.read (%15) = .value 48#64
  c16 : E.read (%16) = .value 7#64
  c17 : E.read (%17) = .value 6#64
  c18 : E.read (%18) = .value 13#64
  c19 : E.read (%19) = .value 21#64
  c20 : E.read (%20) = .value 9#64
  c21 : E.read (%21) = .value 29#64
  c22 : E.read (%22) = .value 10#64
  c23 : E.read (%23) = .value 37#64
  c24 : E.read (%24) = .value 11#64
  c25 : E.read (%25) = .value 45#64
  c26 : E.read (%26) = .value 12#64
  c27 : E.read (%27) = .value 14#64
  c28 : E.read (%28) = .value 18#64
  c29 : E.read (%29) = .value 15#64
  c30 : E.read (%30) = .value 26#64
  c31 : E.read (%31) = .value 34#64
  c32 : E.read (%32) = .value 17#64
  c33 : E.read (%33) = .value 42#64
  c34 : E.read (%34) = .value 50#64
  c35 : E.read (%35) = .value 20#64
  c36 : E.read (%36) = .value 23#64
  c37 : E.read (%37) = .value 22#64
  c38 : E.read (%38) = .value 31#64
  c39 : E.read (%39) = .value 39#64
  c40 : E.read (%40) = .value 47#64
  c41 : E.read (%41) = .value 25#64
  c42 : E.read (%42) = .value 27#64
  c43 : E.read (%43) = .value 28#64
  c44 : E.read (%44) = .value 36#64
  c45 : E.read (%45) = .value 30#64
  c46 : E.read (%46) = .value 44#64
  c50 : E.read (%50) = .value 0#64
  c54 : E.read (%54) = .value 2251799813684944#64
  c59 : E.read (%59) = .value 36028797018963952#64
  c47 : E.read (%47) = Ty.wrap #v[36028797018963664#64, 36028797018963952#64, 36028797018963952#64, 36028797018963952#64]
  c48 : E.read (%48) = Ty.wrap (Vector.replicate 4 36028797018963952#64)
  c49 : E.read (%49) = Ty.wrap (Vector.replicate 4 51#64)
  c51 : E.read (%51) = Ty.wrap (Vector.replicate 4 2251799813685247#64)

def byteRegister : Fin 32 → Reg program.Γ (.bv 8) :=
  ![(%133), (%136), (%139), (%142), (%145), (%148), (%154), (%157), (%160), (%163), (%166), (%169), (%174), (%177), (%180), (%183), (%186), (%189), (%192), (%197), (%200), (%203), (%206), (%209), (%212), (%217), (%220), (%223), (%226), (%229), (%232), (%235)]

def Cached (E : Env program.Γ) (b : Fin 32 → BitVec 8) : Prop :=
  ∀ i, E.read (byteRegister i) = .value (b i)

/-- Only newly defined registers are changed. -/
def Frame (E F : Env program.Γ) (lo : Nat := 237) : Prop :=
  F.args = E.args ∧ ∀ i (h : i.val < lo), F.vals i = E.vals i

theorem frame_refl (E : Env program.Γ) (lo : Nat) : Frame E E lo := ⟨rfl, fun _ _ => rfl⟩

theorem frame_write (E F : Env program.Γ) (lo : Nat) (d : Dst program.Γ t)
    (v : ⟦t⟧) (h : Frame E F lo) (hd : lo ≤ d.i.val) :
    Frame E (F.write d v) lo := by
  constructor
  · exact h.1
  · intro i hi
    have hn : i ≠ d.i := by intro he; subst i; omega
    simpa only [Env.write, Env.set, dif_neg hn] using h.2 i hi

theorem frame_read (E F : Env program.Γ) (h : Frame E F lo)
    (i : Fin program.Γ.n) (hi : i.val < lo) (ht : program.Γ.ty i = t) :
    F.read (.val i ht) = E.read (.val i ht) := by
  cases ht
  exact h.2 i hi

theorem frame_constants (E F : Env program.Γ) (h : Frame E F) (hc : Constants E) :
    Constants F := by
  constructor
  · exact (frame_read E F h 1 (by decide) rfl).trans hc.c1
  · exact (frame_read E F h 3 (by decide) rfl).trans hc.c3
  · exact (frame_read E F h 4 (by decide) rfl).trans hc.c4
  · exact (frame_read E F h 5 (by decide) rfl).trans hc.c5
  · exact (frame_read E F h 6 (by decide) rfl).trans hc.c6
  · exact (frame_read E F h 7 (by decide) rfl).trans hc.c7
  · exact (frame_read E F h 8 (by decide) rfl).trans hc.c8
  · exact (frame_read E F h 9 (by decide) rfl).trans hc.c9
  · exact (frame_read E F h 10 (by decide) rfl).trans hc.c10
  · exact (frame_read E F h 11 (by decide) rfl).trans hc.c11
  · exact (frame_read E F h 12 (by decide) rfl).trans hc.c12
  · exact (frame_read E F h 13 (by decide) rfl).trans hc.c13
  · exact (frame_read E F h 14 (by decide) rfl).trans hc.c14
  · exact (frame_read E F h 15 (by decide) rfl).trans hc.c15
  · exact (frame_read E F h 16 (by decide) rfl).trans hc.c16
  · exact (frame_read E F h 17 (by decide) rfl).trans hc.c17
  · exact (frame_read E F h 18 (by decide) rfl).trans hc.c18
  · exact (frame_read E F h 19 (by decide) rfl).trans hc.c19
  · exact (frame_read E F h 20 (by decide) rfl).trans hc.c20
  · exact (frame_read E F h 21 (by decide) rfl).trans hc.c21
  · exact (frame_read E F h 22 (by decide) rfl).trans hc.c22
  · exact (frame_read E F h 23 (by decide) rfl).trans hc.c23
  · exact (frame_read E F h 24 (by decide) rfl).trans hc.c24
  · exact (frame_read E F h 25 (by decide) rfl).trans hc.c25
  · exact (frame_read E F h 26 (by decide) rfl).trans hc.c26
  · exact (frame_read E F h 27 (by decide) rfl).trans hc.c27
  · exact (frame_read E F h 28 (by decide) rfl).trans hc.c28
  · exact (frame_read E F h 29 (by decide) rfl).trans hc.c29
  · exact (frame_read E F h 30 (by decide) rfl).trans hc.c30
  · exact (frame_read E F h 31 (by decide) rfl).trans hc.c31
  · exact (frame_read E F h 32 (by decide) rfl).trans hc.c32
  · exact (frame_read E F h 33 (by decide) rfl).trans hc.c33
  · exact (frame_read E F h 34 (by decide) rfl).trans hc.c34
  · exact (frame_read E F h 35 (by decide) rfl).trans hc.c35
  · exact (frame_read E F h 36 (by decide) rfl).trans hc.c36
  · exact (frame_read E F h 37 (by decide) rfl).trans hc.c37
  · exact (frame_read E F h 38 (by decide) rfl).trans hc.c38
  · exact (frame_read E F h 39 (by decide) rfl).trans hc.c39
  · exact (frame_read E F h 40 (by decide) rfl).trans hc.c40
  · exact (frame_read E F h 41 (by decide) rfl).trans hc.c41
  · exact (frame_read E F h 42 (by decide) rfl).trans hc.c42
  · exact (frame_read E F h 43 (by decide) rfl).trans hc.c43
  · exact (frame_read E F h 44 (by decide) rfl).trans hc.c44
  · exact (frame_read E F h 45 (by decide) rfl).trans hc.c45
  · exact (frame_read E F h 46 (by decide) rfl).trans hc.c46
  · exact (frame_read E F h 50 (by decide) rfl).trans hc.c50
  · exact (frame_read E F h 54 (by decide) rfl).trans hc.c54
  · exact (frame_read E F h 59 (by decide) rfl).trans hc.c59
  · exact (frame_read E F h 47 (by decide) rfl).trans hc.c47
  · exact (frame_read E F h 48 (by decide) rfl).trans hc.c48
  · exact (frame_read E F h 49 (by decide) rfl).trans hc.c49
  · exact (frame_read E F h 51 (by decide) rfl).trans hc.c51

theorem frame_cached (E F : Env program.Γ) (h : Frame E F) (hb : Cached E b) :
    Cached F b := by
  intro i
  have hi := hb i
  fin_cases i <;> exact (frame_read E F h _ (by decide) rfl).trans hi

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
