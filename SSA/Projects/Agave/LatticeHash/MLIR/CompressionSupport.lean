/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.GArithmetic

/-!
Algebraic support for proving the compiled `compress_pre` loop.

These are specification lemmas, not a `Cfg.denote` refinement. In particular,
the connection from LLVM instructions and memory to these invariants is
an additional obligation.
-/
namespace AgaveLatticeHash.MLIR
open Blake3Compression
open LeanMLIR.SLLVM

/-- Arithmetic order in the inlined round differs from the standalone G
wrapper: the first sum is `(a+b)+x`, the second is `(y+a₁)+b₁`. -/
def roundG (a b c d x y : Word) : Quad Word :=
  let a₁ := a + b + x
  let d₁ := fshlBV (a₁ ^^^ d) (a₁ ^^^ d) 16
  let c₁ := d₁ + c
  let b₁ := fshlBV (c₁ ^^^ b) (c₁ ^^^ b) 20
  let a₂ := (y + a₁) + b₁
  let d₂ := fshlBV (a₂ ^^^ d₁) (a₂ ^^^ d₁) 24
  let c₂ := d₂ + c₁
  let b₂ := fshlBV (c₂ ^^^ b₁) (c₂ ^^^ b₁) 25
  ⟨a₂, b₂, c₂, d₂⟩

theorem roundG_eq (a b c d x y : Word) :
    roundG a b c d x y = scalarG a b c d x y := by
  simp only [roundG, scalarG, funnel16, funnel20, funnel24, funnel25,
    BitVec.add_comm, word_add_left_comm, BitVec.add_assoc, BitVec.xor_comm]

/-- General round congruence keeps the large seven-round arithmetic DAG out of
subsequent loop-invariant proofs. -/
theorem roundFn_congr {α : Type} (g h : GFn α)
    (hg : ∀ a b c d x y, g a b c d x y = h a b c d x y)
    (s m : State α) (r : Fin 7) : roundFn g s m r = roundFn h s m r := by
  have : g = h := funext fun a => funext fun b => funext fun c =>
    funext fun d => funext fun x => funext fun y => hg a b c d x y
  rw [this]

/-- Sixteen result registers in the order used by the compiled loop back-edge.
The message argument is already selected by the round's schedule row. This
factorization lets the block proof retain eight named G results. -/
def roundRegisters {α : Type} (g : GFn α) (s m : State α) : State α :=
  let q₀ := g (s 0) (s 4) (s 8) (s 12) (m 0) (m 1)
  let q₁ := g (s 1) (s 5) (s 9) (s 13) (m 2) (m 3)
  let q₂ := g (s 2) (s 6) (s 10) (s 14) (m 4) (m 5)
  let q₃ := g (s 3) (s 7) (s 11) (s 15) (m 6) (m 7)
  let q₄ := g q₀.a q₁.b q₂.c q₃.d (m 8) (m 9)
  let q₅ := g q₁.a q₂.b q₃.c q₀.d (m 10) (m 11)
  let q₆ := g q₂.a q₃.b q₀.c q₁.d (m 12) (m 13)
  let q₇ := g q₃.a q₀.b q₁.c q₂.d (m 14) (m 15)
  fun i => match i.val with
    | 0 => q₄.a | 1 => q₅.a | 2 => q₆.a | 3 => q₇.a
    | 4 => q₇.b | 5 => q₄.b | 6 => q₅.b | 7 => q₆.b
    | 8 => q₆.c | 9 => q₇.c | 10 => q₄.c | 11 => q₅.c
    | 12 => q₅.d | 13 => q₆.d | 14 => q₇.d | _ => q₄.d

/-- Keep named quarter-round results opaque when evaluating the loop terminator. -/
theorem roundRegisters_of_quads {α : Type} (g : GFn α) (s m : State α)
    (q₀ q₁ q₂ q₃ q₄ q₅ q₆ q₇ : Quad α)
    (h₀ : q₀ = g (s 0) (s 4) (s 8) (s 12) (m 0) (m 1))
    (h₁ : q₁ = g (s 1) (s 5) (s 9) (s 13) (m 2) (m 3))
    (h₂ : q₂ = g (s 2) (s 6) (s 10) (s 14) (m 4) (m 5))
    (h₃ : q₃ = g (s 3) (s 7) (s 11) (s 15) (m 6) (m 7))
    (h₄ : q₄ = g q₀.a q₁.b q₂.c q₃.d (m 8) (m 9))
    (h₅ : q₅ = g q₁.a q₂.b q₃.c q₀.d (m 10) (m 11))
    (h₆ : q₆ = g q₂.a q₃.b q₀.c q₁.d (m 12) (m 13))
    (h₇ : q₇ = g q₃.a q₀.b q₁.c q₂.d (m 14) (m 15)) :
    roundRegisters g s m = (fun i => match i.val with
      | 0 => q₄.a | 1 => q₅.a | 2 => q₆.a | 3 => q₇.a
      | 4 => q₇.b | 5 => q₄.b | 6 => q₅.b | 7 => q₆.b
      | 8 => q₆.c | 9 => q₇.c | 10 => q₄.c | 11 => q₅.c
      | 12 => q₅.d | 13 => q₆.d | 14 => q₇.d | _ => q₄.d) := by
  simp only [roundRegisters, ← h₀, ← h₁, ← h₂, ← h₃, ← h₄, ← h₅, ← h₆, ← h₇]

/-- Wiring is independent of word arithmetic or SIMD width. -/
theorem roundRegisters_eq {α : Type} (g : GFn α) (s m : State α) (r : Fin 7) :
    roundRegisters g s (fun i => m (schedule r i)) = roundFn g s m r := by
  funext ⟨i, hi⟩
  have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst i <;> rfl

theorem gStep_vectors_lane {n : Nat} (s : State (Vector Word n))
    (a b c d : Fin 16) (x y : Vector Word n) (lane : Fin n) :
    (fun i => (gStep gVectors s a b c d x y i)[lane]) =
      gStep scalarG (fun i => (s i)[lane]) a b c d x[lane] y[lane] := by
  have hq := gVectors_lane (s a) (s b) (s c) (s d) x y lane
  funext i
  simp only [gStep]
  split
  · exact congrArg Quad.a hq
  split
  · exact congrArg Quad.b hq
  split
  · exact congrArg Quad.c hq
  split
  · exact congrArg Quad.d hq
  · rfl

/-- The sixteen compiled round-result registers implement the scalar round
in each lane once the instruction-level G equalities have been established. -/
theorem roundRegisters_lane {n : Nat} (s m : State (Vector Word n))
    (r : Fin 7) (lane : Fin n) :
    (fun i => (roundRegisters gVectors s (fun j => m (schedule r j)) i)[lane]) =
      roundFn scalarG (fun i => (s i)[lane]) (fun i => (m i)[lane]) r := by
  rw [roundRegisters_eq]
  simp only [roundFn, gStep_vectors_lane]

theorem roundFn_vectors_lane {n : Nat} (s m : State (Vector Word n))
    (r : Fin 7) (lane : Fin n) :
    (fun i => (roundFn gVectors s m r i)[lane]) =
      roundFn scalarG (fun i => (s i)[lane]) (fun i => (m i)[lane]) r := by
  rw [← roundRegisters_eq]
  exact roundRegisters_lane s m r lane

theorem rounds_vectors_lane {n : Nat} (rs : List (Fin 7))
    (s m : State (Vector Word n)) (lane : Fin n) :
    (fun i => (rounds gVectors rs s m i)[lane]) =
      rounds scalarG rs (fun i => (s i)[lane]) (fun i => (m i)[lane]) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp only [rounds, ih, roundFn_vectors_lane]

/-- The arithmetic produced after all seven compiled round steps refines the
existing scalar compression model on every lane. -/
theorem sevenRounds_vectors_compressPre {n : Nat} (cv : CV (Lanes n))
    (m : State (Lanes n)) (counter : Counters n) (blockLen flags : Lanes n)
    (lane : Fin n) :
    (fun i => (sevenRounds gVectors
      (fun j => Vector.ofFn (laneInit cv counter blockLen flags j))
      (fun j => Vector.ofFn (m j)) i)[lane]) =
      scalarCompressPre (project cv lane) (project m lane) (counter lane)
        (blockLen lane) (flags lane) := by
  have hi : (fun i => (Vector.ofFn (laneInit cv counter blockLen flags i))[lane]) =
      project (laneInit cv counter blockLen flags) lane := by
    funext i
    simp [project]
  have hm : (fun i => (Vector.ofFn (m i))[lane]) = project m lane := by
    funext i
    simp [project]
  rw [sevenRounds, rounds_vectors_lane, hi, hm, laneInit_project]
  rfl

/-- Word-major vector layout of independently specified scalar compression
outputs; this is the observable result used by the memory conformance theorem. -/
def scalarPreVectors {n : Nat} (cv : CV (Lanes n)) (m : State (Lanes n))
    (counter : Counters n) (blockLen flags : Lanes n) : State (Vector Word n) :=
  fun i => Vector.ofFn fun lane =>
    scalarCompressPre (project cv lane) (project m lane) (counter lane)
      (blockLen lane) (flags lane) i

theorem sevenRounds_vectors_eq_scalarPreVectors {n : Nat} (cv : CV (Lanes n))
    (m : State (Lanes n)) (counter : Counters n) (blockLen flags : Lanes n) :
    sevenRounds gVectors (fun i => Vector.ofFn (laneInit cv counter blockLen flags i))
      (fun i => Vector.ofFn (m i)) = scalarPreVectors cv m counter blockLen flags := by
  funext i
  apply Vector.ext
  intro lane hlane
  simpa only [scalarPreVectors, Fin.getElem_fin, Vector.getElem_ofFn] using
    congrFun (sevenRounds_vectors_compressPre cv m counter blockLen flags ⟨lane, hlane⟩) i

/-- The invariant at the header with round counter `r` has executed exactly the
prefix of the seven-round schedule of length `r`. -/
def loopState {α : Type} (g : GFn α) (initial m : State α) (r : Nat) : State α :=
  rounds g (sevenRoundSchedule.take r) initial m

@[simp] theorem loopState_zero {α : Type} (g : GFn α) (initial m : State α) :
    loopState g initial m 0 = initial := rfl

theorem rounds_append {α : Type} (g : GFn α) (xs ys : List (Fin 7))
    (initial m : State α) :
    rounds g (xs ++ ys) initial m = rounds g ys (rounds g xs initial m) m := by
  induction xs generalizing initial with
  | nil => rfl
  | cons r rs ih => exact ih (roundFn g initial m r)

/-- Matches the compiled loop's increment-before-test branch: execute round
`r`, carry the resulting sixteen values with counter `r+1`. -/
theorem loopState_succ {α : Type} (g : GFn α) (initial m : State α)
    (r : Fin 7) :
    loopState g initial m (r.val + 1) =
      roundFn g (loopState g initial m r.val) m r := by
  have hr := r.isLt
  have hs : sevenRoundSchedule.take (r.val + 1) =
      sevenRoundSchedule.take r.val ++ [r] := by
    rcases r with ⟨r, hr⟩
    have he : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
    rcases he with h | h | h | h | h | h | h <;> subst r <;> rfl
  simp only [loopState, hs, rounds_append, rounds]

@[simp] theorem loopState_seven {α : Type} (g : GFn α) (initial m : State α) :
    loopState g initial m 7 = sevenRounds g initial m := rfl

/-- The loop exit feeds the full sixteen-word state to the stores, before
BLAKE3 feed-forward. -/
theorem loopState_compressPre {n : Nat} (cv : CV (Lanes n))
    (m : State (Lanes n)) (counter : Counters n) (blockLen flags : Lanes n) :
    loopState laneG (laneInit cv counter blockLen flags) m 7 =
      laneCompressPre cv m counter blockLen flags := rfl

/-- Projecting the loop-exit invariant is enough to obtain the existing scalar
compression specification, once the sixteen compiled stores are established. -/
theorem loopState_compressPre_project {n : Nat} (cv : CV (Lanes n))
    (m : State (Lanes n)) (counter : Counters n) (blockLen flags : Lanes n)
    (lane : Fin n) :
    project (loopState laneG (laneInit cv counter blockLen flags) m 7) lane =
      scalarCompressPre (project cv lane) (project m lane) (counter lane)
        (blockLen lane) (flags lane) :=
  laneCompressPre_project cv m counter blockLen flags lane

end AgaveLatticeHash.MLIR
