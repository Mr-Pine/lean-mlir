import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice

/-! Generated source candidates: small exact instruction intervals from the
unchanged double-base CFG. Kernel checking, not this generator, establishes
each execution equality. Field contracts use explicit packed register reads. -/
namespace Agave.Ed25519.Avx2PointAdd.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR Phases

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime22_10_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 10 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime22_10_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 10 s =
      (avx2Kernel.bb22 p).runBodyFrom E 11 s := by
  exact runBodyFrom_slice _ E E 10 1 s s (lifetime22_10_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime22_31_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 31 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime22_31_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 31 s =
      (avx2Kernel.bb22 p).runBodyFrom E 32 s := by
  exact runBodyFrom_slice _ E E 31 1 s s (lifetime22_31_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime22_62_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 62 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime22_62_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 62 s =
      (avx2Kernel.bb22 p).runBodyFrom E 63 s := by
  exact runBodyFrom_slice _ E E 62 1 s s (lifetime22_62_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime22_65_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 65 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime22_65_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 65 s =
      (avx2Kernel.bb22 p).runBodyFrom E 66 s := by
  exact runBodyFrom_slice _ E E 65 1 s s (lifetime22_65_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime22_96_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 96 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime22_96_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 96 s =
      (avx2Kernel.bb22 p).runBodyFrom E 97 s := by
  exact runBodyFrom_slice _ E E 96 1 s s (lifetime22_96_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime22_107_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 107 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime22_107_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 107 s =
      (avx2Kernel.bb22 p).runBodyFrom E 108 s := by
  exact runBodyFrom_slice _ E E 107 1 s s (lifetime22_107_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime22_119_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 119 4 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime22_119_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 119 s =
      (avx2Kernel.bb22 p).runBodyFrom E 123 s := by
  exact runBodyFrom_slice _ E E 119 4 s s (lifetime22_119_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime22_128_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 128 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime22_128_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 128 s =
      (avx2Kernel.bb22 p).runBodyFrom E 129 s := by
  exact runBodyFrom_slice _ E E 128 1 s s (lifetime22_128_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime25_1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 1 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime25_1_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 1 s =
      (avx2Kernel.bb25 p).runBodyFrom E 2 s := by
  exact runBodyFrom_slice _ E E 1 1 s s (lifetime25_1_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime25_32_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 32 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime25_32_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 32 s =
      (avx2Kernel.bb25 p).runBodyFrom E 33 s := by
  exact runBodyFrom_slice _ E E 32 1 s s (lifetime25_32_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime25_35_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 35 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime25_35_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 35 s =
      (avx2Kernel.bb25 p).runBodyFrom E 36 s := by
  exact runBodyFrom_slice _ E E 35 1 s s (lifetime25_35_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime25_66_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 66 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime25_66_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 66 s =
      (avx2Kernel.bb25 p).runBodyFrom E 67 s := by
  exact runBodyFrom_slice _ E E 66 1 s s (lifetime25_66_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime25_77_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 77 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime25_77_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 77 s =
      (avx2Kernel.bb25 p).runBodyFrom E 78 s := by
  exact runBodyFrom_slice _ E E 77 1 s s (lifetime25_77_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime25_89_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 89 3 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime25_89_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 89 s =
      (avx2Kernel.bb25 p).runBodyFrom E 92 s := by
  exact runBodyFrom_slice _ E E 89 3 s s (lifetime25_89_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime25_97_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 97 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime25_97_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 97 s =
      (avx2Kernel.bb25 p).runBodyFrom E 98 s := by
  exact runBodyFrom_slice _ E E 97 1 s s (lifetime25_97_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime29_10_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 10 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime29_10_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 10 s =
      (avx2Kernel.bb29 p).runBodyFrom E 11 s := by
  exact runBodyFrom_slice _ E E 10 1 s s (lifetime29_10_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime29_31_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 31 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime29_31_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 31 s =
      (avx2Kernel.bb29 p).runBodyFrom E 32 s := by
  exact runBodyFrom_slice _ E E 31 1 s s (lifetime29_31_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime29_62_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 62 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime29_62_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 62 s =
      (avx2Kernel.bb29 p).runBodyFrom E 63 s := by
  exact runBodyFrom_slice _ E E 62 1 s s (lifetime29_62_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime29_65_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 65 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime29_65_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 65 s =
      (avx2Kernel.bb29 p).runBodyFrom E 66 s := by
  exact runBodyFrom_slice _ E E 65 1 s s (lifetime29_65_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime29_96_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 96 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime29_96_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 96 s =
      (avx2Kernel.bb29 p).runBodyFrom E 97 s := by
  exact runBodyFrom_slice _ E E 96 1 s s (lifetime29_96_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime29_107_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 107 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime29_107_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 107 s =
      (avx2Kernel.bb29 p).runBodyFrom E 108 s := by
  exact runBodyFrom_slice _ E E 107 1 s s (lifetime29_107_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime29_119_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 119 4 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime29_119_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 119 s =
      (avx2Kernel.bb29 p).runBodyFrom E 123 s := by
  exact runBodyFrom_slice _ E E 119 4 s s (lifetime29_119_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime29_128_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 128 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime29_128_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 128 s =
      (avx2Kernel.bb29 p).runBodyFrom E 129 s := by
  exact runBodyFrom_slice _ E E 128 1 s s (lifetime29_128_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime33_1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 1 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime33_1_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 1 s =
      (avx2Kernel.bb33 p).runBodyFrom E 2 s := by
  exact runBodyFrom_slice _ E E 1 1 s s (lifetime33_1_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime33_32_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 32 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime33_32_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 32 s =
      (avx2Kernel.bb33 p).runBodyFrom E 33 s := by
  exact runBodyFrom_slice _ E E 32 1 s s (lifetime33_32_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime33_35_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 35 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime33_35_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 35 s =
      (avx2Kernel.bb33 p).runBodyFrom E 36 s := by
  exact runBodyFrom_slice _ E E 35 1 s s (lifetime33_35_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime33_66_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 66 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime33_66_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 66 s =
      (avx2Kernel.bb33 p).runBodyFrom E 67 s := by
  exact runBodyFrom_slice _ E E 66 1 s s (lifetime33_66_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime33_77_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 77 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime33_77_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 77 s =
      (avx2Kernel.bb33 p).runBodyFrom E 78 s := by
  exact runBodyFrom_slice _ E E 77 1 s s (lifetime33_77_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime33_89_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 89 3 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime33_89_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 89 s =
      (avx2Kernel.bb33 p).runBodyFrom E 92 s := by
  exact runBodyFrom_slice _ E E 89 3 s s (lifetime33_89_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime33_97_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 97 1 s = .value (E, s) := by
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime33_97_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 97 s =
      (avx2Kernel.bb33 p).runBodyFrom E 98 s := by
  exact runBodyFrom_slice _ E E 97 1 s s (lifetime33_97_slice p E s)


end Agave.Ed25519.Avx2PointAdd.CFG
