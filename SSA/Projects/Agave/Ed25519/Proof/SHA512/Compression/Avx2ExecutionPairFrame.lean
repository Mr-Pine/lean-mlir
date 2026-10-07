import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairFirst
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionSchedulePrefix
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairStore

/-! Register frames for composing the four exact slices of the bb5 pair body. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR

/-- Arguments and every value register outside the inclusive interval are preserved. -/
def RegFrame (lo hi : Nat) {Γ : Ctx} (before after : Env Γ) : Prop :=
  after.args = before.args ∧
    ∀ i : Fin Γ.n, (i.val < lo ∨ hi < i.val) → after.vals i = before.vals i

/-- Arguments are always outside a value-register write interval. -/
def RegOutside (lo hi : Nat) {Γ : Ctx} {t : Ty} : Reg Γ t → Prop
  | .arg _ _ => True
  | .val i _ => i.val < lo ∨ hi < i.val

instance {Γ : Ctx} {t : Ty} (lo hi : Nat) (reg : Reg Γ t) :
    Decidable (RegOutside lo hi reg) := by
  cases reg <;> unfold RegOutside <;> infer_instance

theorem RegFrame.refl {Γ : Ctx} (lo hi : Nat) (E : Env Γ) : RegFrame lo hi E E :=
  ⟨rfl, fun _ _ => rfl⟩

theorem RegFrame.trans {Γ : Ctx} {lo hi : Nat} {E₀ E₁ E₂ : Env Γ}
    (h₀ : RegFrame lo hi E₀ E₁) (h₁ : RegFrame lo hi E₁ E₂) :
    RegFrame lo hi E₀ E₂ :=
  ⟨h₁.1.trans h₀.1, fun i hi => (h₁.2 i hi).trans (h₀.2 i hi)⟩

theorem RegFrame.enlarge {Γ : Ctx} {lo hi lo' hi' : Nat} {E₀ E₁ : Env Γ}
    (h : RegFrame lo hi E₀ E₁) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    RegFrame lo' hi' E₀ E₁ := by
  exact ⟨h.1, fun i hi => h.2 i (by omega)⟩

/-- Typed read transport, with concrete register bounds discharged automatically. -/
theorem RegFrame.read {Γ : Ctx} {lo hi : Nat} {E₀ E₁ : Env Γ}
    (h : RegFrame lo hi E₀ E₁) {t : Ty} (reg : Reg Γ t)
    (hout : RegOutside lo hi reg := by decide) : E₁.read reg = E₀.read reg := by
  cases reg with
  | arg i ht => simp only [Env.read, h.1]
  | val i ht => simp only [Env.read, h.2 i hout]

theorem RegFrame.write {Γ : Ctx} {lo hi : Nat} {E₀ E₁ : Env Γ}
    (h : RegFrame lo hi E₀ E₁) (dst : Dst Γ t) (v : t.denote)
    (hlo : lo ≤ dst.i.val) (hhi : dst.i.val ≤ hi) :
    RegFrame lo hi E₀ (E₁.write dst v) := by
  refine ⟨h.1, ?_⟩
  intro i hi'
  have hne : i ≠ dst.i := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  simpa only [Env.write, Env.set, dite_eq_right hne] using h.2 i hi'

abbrev PairBodyFrame (before after : Env program.Γ) : Prop := RegFrame 191 271 before after
abbrev GroupFrame (before after : Env program.Γ) : Prop := RegFrame 153 280 before after

theorem pairScheduleEnv_frame (E : Env program.Γ) (k : Pointer) (r j : Nat)
    (q : Spec.Window) (k0 k1 : Spec.Word) :
    RegFrame 191 217 E (pairScheduleEnv E k r j q k0 k1) := by
  unfold pairScheduleEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem pairFirstEnv_frame (E : Env program.Γ) (scratch : Pointer) (j : Nat)
    (s : Spec.State) (kw : Spec.Word) :
    RegFrame 218 243 E (pairFirstEnv E scratch j s kw) := by
  unfold pairFirstEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem pairSecondEnv_frame (E : Env program.Γ) (pairptr : Pointer)
    (s : Spec.State) (kw : Spec.Word) :
    RegFrame 244 268 E (pairSecondEnv E pairptr s kw) := by
  unfold pairSecondEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem pairStoreEnv_frame (E : Env program.Γ) (scratch : Pointer) (r j : Nat) :
    RegFrame 269 271 E (pairStoreEnv E scratch r j) := by
  unfold pairStoreEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

/-- The working state survives the final scratch store and counter updates. -/
theorem PairSecondFinalReady.of_frame {E E' : Env program.Γ} {s : Spec.State}
    (h : PairSecondFinalReady E s) (hf : RegFrame 269 271 E E') :
    PairSecondFinalReady E' s := by
  constructor
  · exact (hf.read (%267)).trans h.a
  · exact (hf.read (%242)).trans h.b
  · exact (hf.read (%187)).trans h.c
  · exact (hf.read (%188)).trans h.d
  · exact (hf.read (%268)).trans h.e
  · exact (hf.read (%243)).trans h.f
  · exact (hf.read (%184)).trans h.g
  · exact (hf.read (%186)).trans h.h

/-- Schedule generation leaves all first-round inputs intact. -/
theorem PairFirstReady.of_frame {E E' : Env program.Γ} {scratch : Pointer}
    {j : Nat} {s : Spec.State} (h : PairFirstReady E scratch j s)
    (hf : RegFrame 191 217 E E') : PairFirstReady E' scratch j s := by
  constructor
  · exact (hf.read (%81)).trans h.scratchPtr
  · exact (hf.read (%174)).trans h.slot
  · exact (hf.read (%187)).trans h.a
  · exact (hf.read (%188)).trans h.b
  · exact (hf.read (%189)).trans h.c
  · exact (hf.read (%190)).trans h.d
  · exact (hf.read (%184)).trans h.e
  · exact (hf.read (%186)).trans h.f
  · exact (hf.read (%185)).trans h.g
  · exact (hf.read (%183)).trans h.h
  · exact (hf.read (%3)).trans h.eight
  · exact (hf.read (%35)).trans h.shift
  · exact (hf.read (%36)).trans h.rot14
  · exact (hf.read (%37)).trans h.rot18
  · exact (hf.read (%38)).trans h.rot41
  · exact (hf.read (%39)).trans h.rot28
  · exact (hf.read (%40)).trans h.rot34
  · exact (hf.read (%41)).trans h.rot39

end Agave.Ed25519.SHA512.Execution.Avx2
