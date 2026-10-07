import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseTable
import SSA.Projects.RIR.Run.Memory

/-! Generated source candidates: small exact instruction intervals from the
unchanged double-base CFG. Kernel checking, not this generator, establishes
each execution equality. Field contracts use explicit packed register reads. -/
namespace Agave.Ed25519.Avx2PointAdd.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR Phases

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

/-- The exact first-product copy. Its disjointness is an explicit
precondition supplied by the distinct scratch allocations in the caller. -/
theorem copy22_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%253) = .value dst)
    (hpsrc : E.read (%252) = .value src)
    (hlen : E.read (%153) = .value 160#64) :
    runSlice (avx2Kernel.bb22 p) E 64 1 s =
      .value (E, {s with mem := copyPointBytes s.mem dst src}) := by
  have hcopy := run_memcpy (s := s) (env := E) (len := 160#64) (n := 160)
    (by decide) hd hdst.fits hsrc.fits
  simp [runSlice, avx2Kernel.bb22, copyPointBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, hpdst, hpsrc, hlen, hcopy]

theorem copy22_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%253) = .value dst)
    (hpsrc : E.read (%252) = .value src)
    (hlen : E.read (%153) = .value 160#64) :
    (avx2Kernel.bb22 p).runBodyFrom E 64 s =
      (avx2Kernel.bb22 p).runBodyFrom E 65
        {s with mem := copyPointBytes s.mem dst src} := by
  exact runBodyFrom_slice _ E E 64 1 s _
    (copy22_slice p E s dst src hdst hsrc hd hpdst hpsrc hlen)

/-- The exact first-product copy. Its disjointness is an explicit
precondition supplied by the distinct scratch allocations in the caller. -/
theorem copy25_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%249) = .value dst)
    (hpsrc : E.read (%248) = .value src)
    (hlen : E.read (%153) = .value 160#64) :
    runSlice (avx2Kernel.bb25 p) E 34 1 s =
      .value (E, {s with mem := copyPointBytes s.mem dst src}) := by
  have hcopy := run_memcpy (s := s) (env := E) (len := 160#64) (n := 160)
    (by decide) hd hdst.fits hsrc.fits
  simp [runSlice, avx2Kernel.bb25, copyPointBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, hpdst, hpsrc, hlen, hcopy]

theorem copy25_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%249) = .value dst)
    (hpsrc : E.read (%248) = .value src)
    (hlen : E.read (%153) = .value 160#64) :
    (avx2Kernel.bb25 p).runBodyFrom E 34 s =
      (avx2Kernel.bb25 p).runBodyFrom E 35
        {s with mem := copyPointBytes s.mem dst src} := by
  exact runBodyFrom_slice _ E E 34 1 s _
    (copy25_slice p E s dst src hdst hsrc hd hpdst hpsrc hlen)

/-- The exact first-product copy. Its disjointness is an explicit
precondition supplied by the distinct scratch allocations in the caller. -/
theorem copy29_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%244) = .value dst)
    (hpsrc : E.read (%243) = .value src)
    (hlen : E.read (%153) = .value 160#64) :
    runSlice (avx2Kernel.bb29 p) E 64 1 s =
      .value (E, {s with mem := copyPointBytes s.mem dst src}) := by
  have hcopy := run_memcpy (s := s) (env := E) (len := 160#64) (n := 160)
    (by decide) hd hdst.fits hsrc.fits
  simp [runSlice, avx2Kernel.bb29, copyPointBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, hpdst, hpsrc, hlen, hcopy]

theorem copy29_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%244) = .value dst)
    (hpsrc : E.read (%243) = .value src)
    (hlen : E.read (%153) = .value 160#64) :
    (avx2Kernel.bb29 p).runBodyFrom E 64 s =
      (avx2Kernel.bb29 p).runBodyFrom E 65
        {s with mem := copyPointBytes s.mem dst src} := by
  exact runBodyFrom_slice _ E E 64 1 s _
    (copy29_slice p E s dst src hdst hsrc hd hpdst hpsrc hlen)

/-- The exact first-product copy. Its disjointness is an explicit
precondition supplied by the distinct scratch allocations in the caller. -/
theorem copy33_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%240) = .value dst)
    (hpsrc : E.read (%239) = .value src)
    (hlen : E.read (%153) = .value 160#64) :
    runSlice (avx2Kernel.bb33 p) E 34 1 s =
      .value (E, {s with mem := copyPointBytes s.mem dst src}) := by
  have hcopy := run_memcpy (s := s) (env := E) (len := 160#64) (n := 160)
    (by decide) hd hdst.fits hsrc.fits
  simp [runSlice, avx2Kernel.bb33, copyPointBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, hpdst, hpsrc, hlen, hcopy]

theorem copy33_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%240) = .value dst)
    (hpsrc : E.read (%239) = .value src)
    (hlen : E.read (%153) = .value 160#64) :
    (avx2Kernel.bb33 p).runBodyFrom E 34 s =
      (avx2Kernel.bb33 p).runBodyFrom E 35
        {s with mem := copyPointBytes s.mem dst src} := by
  exact runBodyFrom_slice _ E E 34 1 s _
    (copy33_slice p E s dst src hdst hsrc hd hpdst hpsrc hlen)


end Agave.Ed25519.Avx2PointAdd.CFG
