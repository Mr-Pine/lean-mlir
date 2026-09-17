/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_pow22523
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_sqr
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_mul

/-!
# `fd_f25519_pow22523` conforms to its spec

The region is 31 `sqr`/`mul` calls over three 40-byte locals -- `t₀`, `t₁`,
`t₂`, as `fd_f25519.c` names them -- with seven of the segments counted loops
(`Blocks.run_loop`). Every segment is stated in terms of `State`, the
assertion that the three locals hold given powers of `a` with tight limbs and
that one `FrameBelow` fact keeps the caller's blocks (the input `a` and the
out-parameter `o`) untouched.
`sqr_step`/`mul_step` peel one call each: the run equation for `peel_call`,
the new facts at `dst`, and survival of everything else; `State.update₀/₁/₂`
rebuild the invariant.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/- Scaffolding for the `fd_f25519_pow22523` derivation. Only
`fd_f25519_pow22523_conforms`, below, escapes; everything here is internal, so
the names stay short without crowding `Firedancer.Ref`, which 80-odd ref
proofs share. -/
namespace Pow22523

/-- The block ids of the pow22523 frame: three locals allocated at the entry
counter `n₀`, the caller's operands strictly below it. Constant through the
whole derivation. -/
structure Ids (t₀ t₁ t₂ a o : Pointer) (n₀ : Nat) : Prop where
  id₀ : t₀.id.id = n₀
  id₁ : t₁.id.id = n₀ + 1
  id₂ : t₂.id.id = n₀ + 2
  ida : a.id.id < n₀
  ido : o.id.id < n₀

namespace Ids

variable {t₀ t₁ t₂ a o : Pointer} {n₀ : Nat} (ids : Ids t₀ t₁ t₂ a o n₀)
include ids

theorem ne₁₀ : t₁.id ≠ t₀.id := fun h => by
  have h0 := ids.id₀; have h1 := ids.id₁; rw [h] at h1; omega
theorem ne₂₀ : t₂.id ≠ t₀.id := fun h => by
  have h0 := ids.id₀; have h2 := ids.id₂; rw [h] at h2; omega
theorem ne₂₁ : t₂.id ≠ t₁.id := fun h => by
  have h1 := ids.id₁; have h2 := ids.id₂; rw [h] at h2; omega
theorem nea₀ : a.id ≠ t₀.id := fun h => by
  have h0 := ids.id₀; have ha := ids.ida; rw [h] at ha; omega
theorem nea₁ : a.id ≠ t₁.id := fun h => by
  have h1 := ids.id₁; have ha := ids.ida; rw [h] at ha; omega
theorem nea₂ : a.id ≠ t₂.id := fun h => by
  have h2 := ids.id₂; have ha := ids.ida; rw [h] at ha; omega
theorem neo₀ : o.id ≠ t₀.id := fun h => by
  have h0 := ids.id₀; have ho := ids.ido; rw [h] at ho; omega
theorem neo₁ : o.id ≠ t₁.id := fun h => by
  have h1 := ids.id₁; have ho := ids.ido; rw [h] at ho; omega
theorem neo₂ : o.id ≠ t₂.id := fun h => by
  have h2 := ids.id₂; have ho := ids.ido; rw [h] at ho; omega

theorem below₀ {b : BlockId} (hb : b.id < n₀) : t₀.id ≠ b := fun h => by
  have h0 := ids.id₀; rw [← h] at hb; omega
theorem below₁ {b : BlockId} (hb : b.id < n₀) : t₁.id ≠ b := fun h => by
  have h1 := ids.id₁; rw [← h] at hb; omega
theorem below₂ {b : BlockId} (hb : b.id < n₀) : t₂.id ≠ b := fun h => by
  have h2 := ids.id₂; rw [← h] at hb; omega

end Ids

/-- What holds of a state part-way through the pow22523 derivation: the three
locals hold the values `v₀ v₁ v₂` with tight limbs, and every block below the
frame reads as it did on entry. The values change at every step -- only the
frame clause is invariant. `z₀ z₁ z₂` say what all-zero limbs in a local imply:
`True` for a fresh local, all-zero limbs of the input once it is written. -/
structure State (t₀ t₁ t₂ : Pointer) (n₀ : Nat) (s₀ : GlobalState)
    (v₀ v₁ v₂ : ZMod _root_.p) (z₀ z₁ z₂ : Prop) (u : GlobalState) : Prop where
  wf : u.WF
  fb : FrameBelow n₀ s₀ u
  p₀ : IsFieldElemPtr u.mem t₀
  p₁ : IsFieldElemPtr u.mem t₁
  p₂ : IsFieldElemPtr u.mem t₂
  v₀h : readFieldElem p₀ = v₀
  v₁h : readFieldElem p₁ = v₁
  v₂h : readFieldElem p₂ = v₂
  b₀ : LimbBounds p₀
  b₁ : LimbBounds p₁
  b₂ : LimbBounds p₂
  zh₀ : ZeroLimbs t₀ u.mem → z₀
  zh₁ : ZeroLimbs t₁ u.mem → z₁
  zh₂ : ZeroLimbs t₂ u.mem → z₂

/-! ### Rebuilding the state assertion after a step

One lemma per written local: the new facts come from `StepFacts`, everything
else survives because the write touched only `dst`'s block. -/

section Update

variable {t₀ t₁ t₂ a o : Pointer} {n₀ : Nat} {s₀ : GlobalState}
  {v₀ v₁ v₂ w : ZMod _root_.p} {z₀ z₁ z₂ y : Prop} {u u' : GlobalState}

theorem State.update₀ (ids : Ids t₀ t₁ t₂ a o n₀)
    (ps : State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ u) (st : StepFacts t₀ w u u')
    (hz : ZeroLimbs t₀ u'.mem → y) :
    State t₀ t₁ t₂ n₀ s₀ w v₁ v₂ y z₁ z₂ u' := by
  obtain ⟨p₁, hv₁, hb₁⟩ := survive (st.live _ (Ne.symm ids.ne₁₀)) ps.p₁ ps.v₁h ps.b₁
  obtain ⟨p₂, hv₂, hb₂⟩ := survive (st.live _ (Ne.symm ids.ne₂₀)) ps.p₂ ps.v₂h ps.b₂
  exact {
    wf := st.wf
    fb := fun b hb => (st.live b (ids.below₀ hb)).trans (ps.fb b hb)
    p₀ := st.ptr, p₁ := p₁, p₂ := p₂
    v₀h := st.val, v₁h := hv₁, v₂h := hv₂
    b₀ := st.bnd, b₁ := hb₁, b₂ := hb₂
    zh₀ := hz
    zh₁ := fun h => ps.zh₁ (ZeroLimbs.of_live?_eq (st.live _ (Ne.symm ids.ne₁₀)) h)
    zh₂ := fun h => ps.zh₂ (ZeroLimbs.of_live?_eq (st.live _ (Ne.symm ids.ne₂₀)) h) }

theorem State.update₁ (ids : Ids t₀ t₁ t₂ a o n₀)
    (ps : State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ u) (st : StepFacts t₁ w u u')
    (hz : ZeroLimbs t₁ u'.mem → y) :
    State t₀ t₁ t₂ n₀ s₀ v₀ w v₂ z₀ y z₂ u' := by
  obtain ⟨p₀, hv₀, hb₀⟩ := survive (st.live _ ids.ne₁₀) ps.p₀ ps.v₀h ps.b₀
  obtain ⟨p₂, hv₂, hb₂⟩ := survive (st.live _ (Ne.symm ids.ne₂₁)) ps.p₂ ps.v₂h ps.b₂
  exact {
    wf := st.wf
    fb := fun b hb => (st.live b (ids.below₁ hb)).trans (ps.fb b hb)
    p₀ := p₀, p₁ := st.ptr, p₂ := p₂
    v₀h := hv₀, v₁h := st.val, v₂h := hv₂
    b₀ := hb₀, b₁ := st.bnd, b₂ := hb₂
    zh₀ := fun h => ps.zh₀ (ZeroLimbs.of_live?_eq (st.live _ ids.ne₁₀) h)
    zh₁ := hz
    zh₂ := fun h => ps.zh₂ (ZeroLimbs.of_live?_eq (st.live _ (Ne.symm ids.ne₂₁)) h) }

theorem State.update₂ (ids : Ids t₀ t₁ t₂ a o n₀)
    (ps : State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ u) (st : StepFacts t₂ w u u')
    (hz : ZeroLimbs t₂ u'.mem → y) :
    State t₀ t₁ t₂ n₀ s₀ v₀ v₁ w z₀ z₁ y u' := by
  obtain ⟨p₀, hv₀, hb₀⟩ := survive (st.live _ ids.ne₂₀) ps.p₀ ps.v₀h ps.b₀
  obtain ⟨p₁, hv₁, hb₁⟩ := survive (st.live _ ids.ne₂₁) ps.p₁ ps.v₁h ps.b₁
  exact {
    wf := st.wf
    fb := fun b hb => (st.live b (ids.below₂ hb)).trans (ps.fb b hb)
    p₀ := p₀, p₁ := p₁, p₂ := st.ptr
    v₀h := hv₀, v₁h := hv₁, v₂h := st.val
    b₀ := hb₀, b₁ := hb₁, b₂ := st.bnd
    zh₀ := fun h => ps.zh₀ (ZeroLimbs.of_live?_eq (st.live _ ids.ne₂₀) h)
    zh₁ := fun h => ps.zh₁ (ZeroLimbs.of_live?_eq (st.live _ ids.ne₂₁) h)
    zh₂ := hz }

/-- Re-express the tracked values; the towers a derivation accumulates are
`ring`-equal to the closed powers a statement wants. -/
theorem State.cast (ps : State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ u)
    {w₀ w₁ w₂ : ZMod _root_.p}
    (h0 : w₀ = v₀) (h1 : w₁ = v₁) (h2 : w₂ = v₂) :
    State t₀ t₁ t₂ n₀ s₀ w₀ w₁ w₂ z₀ z₁ z₂ u := h0 ▸ h1 ▸ h2 ▸ ps

end Update

/-- The caller's operands (`a`, `o`) live below the frame, so every fact
about them at entry survives to any `State` state. -/
theorem State.operand_facts {t₀ t₁ t₂ : Pointer} {n₀ : Nat} {s₀ : GlobalState}
    {v₀ v₁ v₂ : ZMod _root_.p} {z₀ z₁ z₂ : Prop} {u : GlobalState}
    (ps : State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ u) {q : Pointer} (hqid : q.id.id < n₀)
    (hq : IsFieldElemPtr s₀.mem q) (hqb : LimbBounds.Loose hq) :
    ∃ hq' : IsFieldElemPtr u.mem q,
      readFieldElem hq' = readFieldElem hq ∧ LimbBounds.Loose hq' := by
  have hl := ps.fb q.id hqid
  refine ⟨isFieldElemPtr_of_live?_eq hl hq, ?_, ?_⟩
  · exact readFieldElem_eq_of
      ((readFieldElem?_of_live?_eq hl).trans (readFieldElem?_eq_some hq rfl))
  · exact limbBounds_of_readLimb? _ fun i l hl' =>
      limbBounds_readLimb? hq hqb i l (by rwa [readLimb?_of_live?_eq hl] at hl')

/-- A fresh 40-byte local reads back as five zero limbs. -/
private theorem readLimb?_afterAlloca_self (s : GlobalState) (i : Fin 5) :
    readLimb? (⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ : Pointer) i (s.afterAlloca (5 * 64)).mem
      = some 0 := by
  simp [readLimb?, live?_afterAlloca_self, Pointer.offsetInBits]


/-- The ambient environment every tail block reads: the three locals, the six
loop constants, and the region arguments. The `Γout` indices are spelled here
once -- `bb0_run` discharges them by `rfl` against the entry block's literal
valuation, so no later segment has to reduce the `Cfg` to look a value up. -/
structure EntryEnv (t₀ t₁ t₂ a o : Pointer)
    (V : fd_f25519_pow22523.Γout.Valuation) : Prop where
  /-- `%8` -/
  v8 : V (⟨8, by rfl⟩ : fd_f25519_pow22523.Γout.Var Ty.ptr) = .value t₂
  /-- `%7` -/
  v7 : V (⟨9, by rfl⟩ : fd_f25519_pow22523.Γout.Var Ty.ptr) = .value t₁
  /-- `%6` -/
  v6 : V (⟨10, by rfl⟩ : fd_f25519_pow22523.Γout.Var Ty.ptr) = .value t₀
  /-- `%5 = 100` -/
  c100 : V (⟨11, by rfl⟩ : fd_f25519_pow22523.Γout.Var (Ty.bitvec 32))
    = .value (BitVec.ofInt 32 100)
  /-- `%4 = 50` -/
  c50 : V (⟨12, by rfl⟩ : fd_f25519_pow22523.Γout.Var (Ty.bitvec 32))
    = .value (BitVec.ofInt 32 50)
  /-- `%3 = 20` -/
  c20 : V (⟨13, by rfl⟩ : fd_f25519_pow22523.Γout.Var (Ty.bitvec 32))
    = .value (BitVec.ofInt 32 20)
  /-- `%2 = 10` -/
  c10 : V (⟨14, by rfl⟩ : fd_f25519_pow22523.Γout.Var (Ty.bitvec 32))
    = .value (BitVec.ofInt 32 10)
  /-- `%1 = 5` -/
  c5 : V (⟨15, by rfl⟩ : fd_f25519_pow22523.Γout.Var (Ty.bitvec 32))
    = .value (BitVec.ofInt 32 5)
  /-- `%0 = 1` -/
  c1 : V (⟨16, by rfl⟩ : fd_f25519_pow22523.Γout.Var (Ty.bitvec 32))
    = .value (BitVec.ofInt 32 1)
  /-- `%arg1`, the input -/
  va : V (⟨17, by rfl⟩ : fd_f25519_pow22523.Γout.Var Ty.ptr) = .value a
  /-- `%arg0`, the out-parameter -/
  vo : V (⟨18, by rfl⟩ : fd_f25519_pow22523.Γout.Var Ty.ptr) = .value o

set_option linter.all false
in
/-- The entry block: three locals, eight calls (`t₀ ← a³¹`, `t₁ ← a⁶²`), and
the branch into the first loop header (`^bb2`, block index 1) with the
counter at `1`. -/
lemma bb0_run (o a : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o) (ha : IsFieldElemPtr s.mem a)
    (halimb : LimbBounds.Loose ha) :
    ∃ (t₀ t₁ t₂ : Pointer) (w₂ : ZMod p) (u : GlobalState)
      (V : fd_f25519_pow22523.Γout.Valuation),
      Ids t₀ t₁ t₂ a o s.alloc.nextFreeBlock
      ∧ State t₀ t₁ t₂ s.alloc.nextFreeBlock s
          (readFieldElem ha ^ 31) (readFieldElem ha ^ 62) w₂
          (ZeroLimbs a s.mem) (ZeroLimbs a s.mem) True u
      ∧ EntryEnv t₀ t₁ t₂ a o V
      ∧ StateT.run (fd_f25519_pow22523.denote
          (Ctxt.Valuation.ofHVector [.value a, .value o]ₕ)) s
        = StateT.run (fd_f25519_pow22523.blocks.run V
            ⟨1, by rfl, [PoisonOr.value (BitVec.ofInt 32 1)]ₕ⟩) u := by
  -- the three locals
  obtain ⟨t₀, s₀, hs₀def, ht₀def, hs₀WF, hfit₀, hid₀, hoff₀, hctr₀, hfr₀⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (5 * 64)
  obtain ⟨t₁, s₁, hs₁def, ht₁def, hs₁WF, hfit₁, hid₁, hoff₁, hctr₁, hfr₁⟩ :=
    GlobalState.exists_afterAlloca_facts s₀ hs₀WF (5 * 64)
  obtain ⟨t₂, s₂, hs₂def, ht₂def, hs₂WF, hfit₂, hid₂, hoff₂, hctr₂, hfr₂⟩ :=
    GlobalState.exists_afterAlloca_facts s₁ hs₁WF (5 * 64)
  have ids : Ids t₀ t₁ t₂ a o s.alloc.nextFreeBlock :=
    ⟨hid₀, by rw [hid₁, hctr₀], by rw [hid₂, hctr₁, hctr₀],
     lt_nextFreeBlock_of_fits hs ha.1, lt_nextFreeBlock_of_fits hs ho.1⟩
  -- one frame fact through the three allocas
  have fb₂ : FrameBelow s.alloc.nextFreeBlock s s₂ :=
    ht₂def ▸ FrameBelow.afterAlloca (by omega)
      (ht₁def ▸ FrameBelow.afterAlloca (by omega)
        (ht₀def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)))
  -- the locals in `s₂`
  have pt₀ : IsFieldElemPtr s₂.mem t₀ :=
    ⟨fits_of_live?_eq (hfr₂ t₀.id (Ne.symm ids.ne₂₀))
      (fits_of_live?_eq (hfr₁ t₀.id (Ne.symm ids.ne₁₀)) hfit₀), by simp [hoff₀]⟩
  have pt₁ : IsFieldElemPtr s₂.mem t₁ :=
    ⟨fits_of_live?_eq (hfr₂ t₁.id (Ne.symm ids.ne₂₁)) hfit₁, by simp [hoff₁]⟩
  have pt₂ : IsFieldElemPtr s₂.mem t₂ := ⟨hfit₂, by simp [hoff₂]⟩
  -- fresh locals read back as zero limbs, so their bounds are trivial
  have hz₀ : ∀ i : Fin 5, readLimb? t₀ i s₂.mem = some 0 := fun i => by
    rw [readLimb?_of_live?_eq (hfr₂ t₀.id (Ne.symm ids.ne₂₀)),
        readLimb?_of_live?_eq (hfr₁ t₀.id (Ne.symm ids.ne₁₀)), ht₀def, hs₀def]
    exact readLimb?_afterAlloca_self s i
  have hz₁ : ∀ i : Fin 5, readLimb? t₁ i s₂.mem = some 0 := fun i => by
    rw [readLimb?_of_live?_eq (hfr₂ t₁.id (Ne.symm ids.ne₂₁)), ht₁def, hs₁def]
    exact readLimb?_afterAlloca_self s₀ i
  have hz₂ : ∀ i : Fin 5, readLimb? t₂ i s₂.mem = some 0 := fun i => by
    rw [ht₂def, hs₂def]
    exact readLimb?_afterAlloca_self s₁ i
  have ps₀ : State t₀ t₁ t₂ s.alloc.nextFreeBlock s
      (readFieldElem pt₀) (readFieldElem pt₁) (readFieldElem pt₂) True True True s₂ := {
    wf := hs₂WF, fb := fb₂
    p₀ := pt₀, p₁ := pt₁, p₂ := pt₂
    v₀h := rfl, v₁h := rfl, v₂h := rfl
    b₀ := limbBounds_of_readLimb? _ fun i l hl => by
      rw [hz₀ i, Option.some.injEq] at hl; omega
    b₁ := limbBounds_of_readLimb? _ fun i l hl => by
      rw [hz₁ i, Option.some.injEq] at hl; omega
    b₂ := limbBounds_of_readLimb? _ fun i l hl => by
      rw [hz₂ i, Option.some.injEq] at hl; omega
    zh₀ := fun _ => trivial, zh₁ := fun _ => trivial, zh₂ := fun _ => trivial }
  -- all-zero limbs of the input, read at any state of the walk
  have za : ∀ {u : GlobalState} {v₀ v₁ v₂ : ZMod p} {z₀ z₁ z₂ : Prop},
      State t₀ t₁ t₂ s.alloc.nextFreeBlock s v₀ v₁ v₂ z₀ z₁ z₂ u →
      ZeroLimbs a u.mem → ZeroLimbs a s.mem :=
    fun ps => ZeroLimbs.of_live?_eq (ps.fb a.id ids.ida)
  -- %9: t₀ ← a²
  obtain ⟨hau₀, hva₀, hba₀⟩ := ps₀.operand_facts ids.ida ha halimb
  obtain ⟨u₁, hrun₁, st₁, hz₁⟩ := sqr_step' ps₀.wf ps₀.p₀ hau₀ hva₀ hba₀
  have ps₁ := State.update₀ (y := ZeroLimbs a s.mem) ids ps₀ st₁ fun h => za ps₀ (hz₁ h)
  -- %10: t₁ ← a⁴
  obtain ⟨u₂, hrun₂, st₂, hz₂⟩ :=
    sqr_step' ps₁.wf ps₁.p₁ ps₁.p₀ ps₁.v₀h ps₁.b₀.loose
  have ps₂ := State.update₁ (y := ZeroLimbs a s.mem) ids ps₁ st₂ fun h => ps₁.zh₀ (hz₂ h)
  -- %11: t₁ ← a⁸
  obtain ⟨u₃, hrun₃, st₃, hz₃⟩ :=
    sqr_step' ps₂.wf ps₂.p₁ ps₂.p₁ ps₂.v₁h ps₂.b₁.loose
  have ps₃ := State.update₁ (y := ZeroLimbs a s.mem) ids ps₂ st₃ fun h => ps₂.zh₁ (hz₃ h)
  -- %12: t₁ ← a⁹
  obtain ⟨hau₃, hva₃, hba₃⟩ := ps₃.operand_facts ids.ida ha halimb
  obtain ⟨u₄, hrun₄, st₄, hz₄⟩ :=
    mul_step' ps₃.wf ps₃.p₁ hau₃ ps₃.p₁ hva₃ ps₃.v₁h hba₃
      ps₃.b₁.loose
  have ps₄ := State.update₁ (y := ZeroLimbs a s.mem) ids ps₃ st₄ fun h =>
    (hz₄ h).elim (za ps₃) ps₃.zh₁
  -- %13: t₀ ← a¹¹
  obtain ⟨u₅, hrun₅, st₅, hz₅⟩ :=
    mul_step' ps₄.wf ps₄.p₀ ps₄.p₀ ps₄.p₁ ps₄.v₀h ps₄.v₁h
      ps₄.b₀.loose
      ps₄.b₁.loose
  have ps₅ := State.update₀ (y := ZeroLimbs a s.mem) ids ps₄ st₅ fun h =>
    (hz₅ h).elim ps₄.zh₀ ps₄.zh₁
  -- %14: t₀ ← a²²
  obtain ⟨u₆, hrun₆, st₆, hz₆⟩ :=
    sqr_step' ps₅.wf ps₅.p₀ ps₅.p₀ ps₅.v₀h ps₅.b₀.loose
  have ps₆ := State.update₀ (y := ZeroLimbs a s.mem) ids ps₅ st₆ fun h => ps₅.zh₀ (hz₆ h)
  -- %15: t₀ ← a³¹
  obtain ⟨u₇, hrun₇, st₇, hz₇⟩ :=
    mul_step' ps₆.wf ps₆.p₀ ps₆.p₁ ps₆.p₀ ps₆.v₁h ps₆.v₀h
      ps₆.b₁.loose
      ps₆.b₀.loose
  have ps₇ := State.update₀ (y := ZeroLimbs a s.mem) ids ps₆ st₇ fun h =>
    (hz₇ h).elim ps₆.zh₁ ps₆.zh₀
  -- %16: t₁ ← a⁶²
  obtain ⟨u₈, hrun₈, st₈, hz₈⟩ :=
    sqr_step' ps₇.wf ps₇.p₁ ps₇.p₀ ps₇.v₀h ps₇.b₀.loose
  have ps₈ := State.update₁ (y := ZeroLimbs a s.mem) ids ps₇ st₈ fun h => ps₇.zh₀ (hz₈ h)
  refine ⟨t₀, t₁, t₂, readFieldElem pt₂, u₈,
    (.value t₁ ::ᵥ .value t₀ ::ᵥ .value t₀ ::ᵥ .value t₀ ::ᵥ .value t₁ ::ᵥ
     .value t₁ ::ᵥ .value t₁ ::ᵥ .value t₀ ::ᵥ .value t₂ ::ᵥ .value t₁ ::ᵥ .value t₀ ::ᵥ
     .value (BitVec.ofInt 32 100) ::ᵥ .value (BitVec.ofInt 32 50) ::ᵥ
     .value (BitVec.ofInt 32 20) ::ᵥ .value (BitVec.ofInt 32 10) ::ᵥ
     .value (BitVec.ofInt 32 5) ::ᵥ .value (BitVec.ofInt 32 1) ::ᵥ
     Ctxt.Valuation.ofHVector [.value a, .value o]ₕ),
    ids, ps₈.cast (by ring) (by ring) rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?run⟩
  case run =>
    simp only [Cfg.denote]
    denote_step_all v 5
    denote_eval v 0 5
    simp only [LLVM.const?] at hv0 hv1 hv2 hv3 hv4 hv5
    subst hv0 hv1 hv2 hv3 hv4 hv5
    peel_alloca from s as s₀ with ht₀def
    peel_alloca from s₀ as s₁ with ht₁def
    peel_alloca from s₁ as s₂ with ht₂def
    rw [← hs₀def, ← hs₁def, ← hs₂def]
    rw [BlockCom.run_bind_denote_lifetime, BlockCom.run_bind_denote_lifetime,
        BlockCom.run_bind_denote_lifetime]
    peel_call hrun₁
    peel_call hrun₂
    peel_call hrun₃
    peel_call hrun₄
    peel_call hrun₅
    peel_call hrun₆
    peel_call hrun₇
    peel_call hrun₈
    simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote_mk,
      simp_denote, simp_sllvm]

/-! ### The seven loops

Every loop header in the region is the same block up to four parameters:
which local it squares, which constant bounds the counter, and its own and
its exit block's indices:

    ^bb(self)(%c: i32):
      %r = llvm.call @fd_f25519_sqr(%t, %t)
      %i = llvm.add %c, %0 nsw nuw
      %b = llvm.icmp eq %i, %n
      llvm.cond_br %b [^bb(exit), ^bb(self)] (%i)

`loopBody` is that shape with the four pieces abstracted; `loop_run` runs it
from counter `1` to the exit block once and for all, with the squared local
behind a step predicate `P`. Each `bbN_run` is an instantiation. -/

/-- The counter stays in `1..n ≤ 100`, so `add nsw nuw` never poisons. -/
private lemma not_saddOverflow {k : ℕ} (hk : k ≤ 100) :
    ¬ ((BitVec.ofInt 32 (1 + k)).saddOverflow 1#32) := by
  have h : (1 + (k : Int)) = ((1 + k : ℕ) : Int) := by push_cast; ring
  rw [h, BitVec.ofInt_natCast]
  simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq, not_or, ge_iff_le,
    not_le, not_lt, BitVec.toInt_ofNat', Int.bmod_def]
  norm_num
  constructor <;> split <;> omega

private lemma not_uaddOverflow {k : ℕ} (hk : k ≤ 100) :
    ¬ ((BitVec.ofInt 32 (1 + k)).uaddOverflow 1#32) := by
  have h : (1 + (k : Int)) = ((1 + k : ℕ) : Int) := by push_cast; ring
  rw [h, BitVec.ofInt_natCast]
  simp only [BitVec.uaddOverflow, decide_eq_true_eq, ge_iff_le, not_le]
  bv_omega

/-- The latch test and the iteration count agree: `(1+k)+1 == n` exactly at
`k + 1 = n - 1`, the last of the `n - 1` iterations. -/
private lemma exit_cond {k n : ℕ} (hk : k < n - 1) (h2 : 2 ≤ n) (h100 : n ≤ 100) :
    (BitVec.ofBool (BitVec.ofInt 32 (1 + (k : Int)) + 1#32 == BitVec.ofNat 32 n) = 1)
      = (k + 1 = n - 1) := by
  have h : (1 + (k : Int)) = ((1 + k : ℕ) : Int) := by push_cast; ring
  rw [eq_iff_iff, h, BitVec.ofInt_natCast]
  have hofBool : ∀ b : Bool, (BitVec.ofBool b = 1) = (b = true) := by decide
  rw [hofBool, beq_iff_eq, BitVec.toNat_eq]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Branch target: loop header `i`, counter at `1`. -/
private abbrev hdr (i : Nat)
    (h : fd_f25519_pow22523.sigs[i]? = some [Ty.bitvec 32] := by rfl) :
    SuccArgs fd_f25519_pow22523.sigs :=
  ⟨i, h, [PoisonOr.value (BitVec.ofInt 32 1)]ₕ⟩

/-- Branch target: straight-line block `i`, no arguments. -/
private abbrev seg (i : Nat)
    (h : fd_f25519_pow22523.sigs[i]? = some [] := by rfl) :
    SuccArgs fd_f25519_pow22523.sigs :=
  ⟨i, h, HVector.nil⟩

/-- The walk from `src` reaches `dst`, in a state satisfying `Q`. -/
private abbrev Hop (V : fd_f25519_pow22523.Γout.Valuation) (u : GlobalState)
    (src dst : SuccArgs fd_f25519_pow22523.sigs) (Q : GlobalState → Prop) : Prop :=
  ∃ u',
    StateT.run (fd_f25519_pow22523.blocks.run V src) u
      = StateT.run (fd_f25519_pow22523.blocks.run V dst) u'
    ∧ Q u'

/-- The shared loop-header shape. `γt` names the squared local and `γb` the
bound constant, both as `Γout` indices; the argument indices are spelled
`γ + 1 + …` so `Valuation.cons_succ` peels them without knowing `γ`. -/
private def loopBody (γt γb γc exit self : Nat)
    (hγt : fd_f25519_pow22523.Γout[γt]? = some Ty.ptr)
    (hγb : fd_f25519_pow22523.Γout[γb]? = some (Ty.bitvec 32))
    (hγc : fd_f25519_pow22523.Γout[γc]? = some (Ty.bitvec 32))
    (hexit : fd_f25519_pow22523.sigs[exit]? = some [])
    (hself : fd_f25519_pow22523.sigs[self]? = some [Ty.bitvec 32]) :
    BlockCom (Ctxt.ofList [Ty.bitvec 32].reverse ++ fd_f25519_pow22523.Γout)
      ([Ty.bitvec 1] ++ ([Ty.bitvec 32] ++ ([Ty.ptr] ++
        (Ctxt.ofList [Ty.bitvec 32].reverse ++ fd_f25519_pow22523.Γout))))
      [Ty.ptr] fd_f25519_pow22523.sigs :=
  BlockCom.call (argTys := [Ty.ptr, Ty.ptr])
    "fd_f25519_sqr" fd_f25519_sqr.entry fd_f25519_sqr.blocks
    (⟨γt + 1, by exact hγt⟩ ::ₕ ⟨γt + 1, by exact hγt⟩ ::ₕ .nil)
    (.var (Expr.mk
        (SLLVMOp.arith (InstCombine.MOp.binary (.concrete 32)
          (.add { nsw := true, nuw := true })))
        rfl (by constructor)
        (⟨1, by rfl⟩ ::ₕ ⟨γc + 1 + 1, by exact hγc⟩ ::ₕ .nil) .nil)
      (.var (Expr.mk
          (SLLVMOp.arith (InstCombine.MOp.icmp .eq (.concrete 32)))
          rfl (by constructor)
          (⟨0, by rfl⟩ ::ₕ ⟨γb + 1 + 1 + 1, by exact hγb⟩ ::ₕ .nil) .nil)
        (.term (Terminator.condBr ⟨0, by rfl⟩
          ⟨exit, hexit, .nil⟩
          ⟨self, hself, ⟨1, by rfl⟩ ::ₕ .nil⟩))))

set_option linter.all false in
/-- Run one loop from its header with the counter at `1` to its exit block:
`n - 1` squarings of the local `P` tracks. -/
private lemma loop_run {γt γb γc exit self : Nat}
    {hγt : fd_f25519_pow22523.Γout[γt]? = some Ty.ptr}
    {hγb : fd_f25519_pow22523.Γout[γb]? = some (Ty.bitvec 32)}
    {hγc : fd_f25519_pow22523.Γout[γc]? = some (Ty.bitvec 32)}
    {hexit : fd_f25519_pow22523.sigs[exit]? = some []}
    {hself : fd_f25519_pow22523.sigs[self]? = some [Ty.bitvec 32]}
    (V : fd_f25519_pow22523.Γout.Valuation) {tp : Pointer}
    (n : Nat) (h2 : 2 ≤ n) (h100 : n ≤ 100)
    (hVt : V ⟨γt, hγt⟩ = .value tp)
    (hVb : V ⟨γb, hγb⟩ = .value (BitVec.ofInt 32 n))
    (hV1 : V ⟨γc, hγc⟩ = .value (BitVec.ofInt 32 1))
    (hget : fd_f25519_pow22523.blocks.get self hself
      = ⟨_, loopBody γt γb γc exit self hγt hγb hγc hexit hself⟩)
    (P : ZMod p → GlobalState → Prop)
    (hP : ∀ w u, P w u → ∃ u',
      StateT.run (runFunction (fd_f25519_sqr.denote
          (Ctxt.Valuation.ofHVector [.value tp, .value tp]ₕ))) u
        = .value ([.value tp]ₕ, u')
      ∧ P (w * w) u')
    {v : ZMod p} {u : GlobalState} (h₀ : P v u) :
    ∃ u',
      StateT.run (fd_f25519_pow22523.blocks.run V
          ⟨self, hself, [PoisonOr.value (BitVec.ofInt 32 1)]ₕ⟩) u
        = StateT.run (fd_f25519_pow22523.blocks.run V ⟨exit, hexit, HVector.nil⟩) u'
      ∧ P (v ^ 2 ^ (n - 1)) u' := by
  refine Exists.imp (fun u' h => ⟨?ends, h.2⟩)
    (Blocks.run_loop (bs := fd_f25519_pow22523.blocks) (Vamb := V)
      (Inv := fun k s => P (v ^ 2 ^ k) s)
      (t := fun k => if k = n - 1 then ⟨exit, hexit, HVector.nil⟩
        else ⟨self, hself, [PoisonOr.value (BitVec.ofInt 32 (1 + k))]ₕ⟩)
      (n := n - 1) ?hstep (by simpa using h₀))
  case ends =>
    have hrun := h.1
    beta_reduce at hrun
    rw [if_neg (by omega), if_pos rfl] at hrun
    simpa using hrun
  case hstep =>
    intro k s hk state
    obtain ⟨u₁, hcall, st⟩ := hP _ s state
    beta_reduce
    rw [if_neg (by omega : ¬ k = n - 1)]
    dsimp only
    rw [hget]
    delta loopBody
    have h  := not_saddOverflow (k := k) (by omega)
    have h' := not_uaddOverflow (k := k) (by omega)
    refine ⟨?val, u₁, ?run,
      by suffices v ^ 2 ^ k * v ^ 2 ^ k = v ^ 2 ^ (k + 1) from this ▸ st; ring⟩
    case run =>
      peel_call hcall with Ctxt.Valuation.cons_succ, hVt
      denote_step_all w 3
      denote_eval w 2 3
      have hlast : (PoisonOr.value (BitVec.ofInt 32 (1 + (k : Int))) ::ᵥ V)
          (Ctxt.Var.last fd_f25519_pow22523.Γout (Ty.bitvec 32)) = .value (BitVec.ofInt 32 (1 + k)) :=
        rfl
      simp [Expr.toPure, HVector.get, LLVM.add, LLVM.add?, hlast, hV1, h, h'] at hw2
      -- `simp` leaves the `liftEffect`/`cast` wrapper; `change` sees through it
      change w2 = .value (BitVec.ofInt 32 (1 + (k : Int)) + 1#32) at hw2
      subst hw2
      set_option backward.isDefEq.respectTransparency false in
        simp [Expr.toPure, HVector.get, LLVM.icmp, LLVM.icmp?, LLVM.icmp', hVb] at hw3
      subst hw3
      simp only [BlockCom.denote_term, simp_denote, simp_sllvm, apply_ite]
      simp only [exit_cond hk h2 h100]
      have hadd : BitVec.ofInt 32 (1 + (k : Int)) + 1#32
          = BitVec.ofInt 32 (1 + ((k : Int) + 1)) := by
        simp [BitVec.ofInt_add, BitVec.add_assoc]
      split <;>
        simp [LLVM.add, LLVM.add?, Ctxt.Valuation.cons_last (s := V),
          hV1, h, h', hadd] <;>
        rfl

/-- The shared inter-loop block shape (`^bb1`/`^bb3`/`^bb5`/`^bb7`/`^bb9`/
`^bb11`): one `mul`, one `sqr`, and the branch into the next loop header with
the counter reset to `%0 = 1`:

    ^bb(self):
      %x = llvm.call @fd_f25519_mul(%md, %m₀, %m₁)
      %y = llvm.call @fd_f25519_sqr(%sd, %ss)
      llvm.br ^bb(next) (%0)
-/
private def interBody (γmd γm₀ γm₁ γsd γss γc next : Nat)
    (hγmd : fd_f25519_pow22523.Γout[γmd]? = some Ty.ptr)
    (hγm₀ : fd_f25519_pow22523.Γout[γm₀]? = some Ty.ptr)
    (hγm₁ : fd_f25519_pow22523.Γout[γm₁]? = some Ty.ptr)
    (hγsd : fd_f25519_pow22523.Γout[γsd]? = some Ty.ptr)
    (hγss : fd_f25519_pow22523.Γout[γss]? = some Ty.ptr)
    (hγc : fd_f25519_pow22523.Γout[γc]? = some (Ty.bitvec 32))
    (hnext : fd_f25519_pow22523.sigs[next]? = some [Ty.bitvec 32]) :
    BlockCom (Ctxt.ofList ([] : List SLLVM.Ty).reverse ++ fd_f25519_pow22523.Γout)
      ([Ty.ptr] ++ ([Ty.ptr] ++
        (Ctxt.ofList ([] : List SLLVM.Ty).reverse ++ fd_f25519_pow22523.Γout)))
      [Ty.ptr] fd_f25519_pow22523.sigs :=
  BlockCom.call (argTys := [Ty.ptr, Ty.ptr, Ty.ptr])
    "fd_f25519_mul" fd_f25519_mul.entry fd_f25519_mul.blocks
    (⟨γmd, by exact hγmd⟩ ::ₕ ⟨γm₀, by exact hγm₀⟩ ::ₕ
     ⟨γm₁, by exact hγm₁⟩ ::ₕ .nil)
    (BlockCom.call (argTys := [Ty.ptr, Ty.ptr])
      "fd_f25519_sqr" fd_f25519_sqr.entry fd_f25519_sqr.blocks
      (⟨γsd + 1, by exact hγsd⟩ ::ₕ ⟨γss + 1, by exact hγss⟩ ::ₕ .nil)
      (.term (Terminator.br
        ⟨next, hnext, ⟨γc + 1 + 1, by exact hγc⟩ ::ₕ .nil⟩)))

set_option linter.all false in
/-- Run one inter-loop block, with the two written locals behind the staged
predicates `Q₀ → Q₁ → Q₂`. -/
private lemma inter_run {γmd γm₀ γm₁ γsd γss γc self next : Nat}
    {hγmd : fd_f25519_pow22523.Γout[γmd]? = some Ty.ptr}
    {hγm₀ : fd_f25519_pow22523.Γout[γm₀]? = some Ty.ptr}
    {hγm₁ : fd_f25519_pow22523.Γout[γm₁]? = some Ty.ptr}
    {hγsd : fd_f25519_pow22523.Γout[γsd]? = some Ty.ptr}
    {hγss : fd_f25519_pow22523.Γout[γss]? = some Ty.ptr}
    {hγc : fd_f25519_pow22523.Γout[γc]? = some (Ty.bitvec 32)}
    {hself : fd_f25519_pow22523.sigs[self]? = some []}
    {hnext : fd_f25519_pow22523.sigs[next]? = some [Ty.bitvec 32]}
    (V : fd_f25519_pow22523.Γout.Valuation) {md m₀ m₁ sd ss : Pointer}
    (hVmd : V ⟨γmd, hγmd⟩ = .value md)
    (hVm₀ : V ⟨γm₀, hγm₀⟩ = .value m₀)
    (hVm₁ : V ⟨γm₁, hγm₁⟩ = .value m₁)
    (hVsd : V ⟨γsd, hγsd⟩ = .value sd)
    (hVss : V ⟨γss, hγss⟩ = .value ss)
    (hV1 : V ⟨γc, hγc⟩ = .value (BitVec.ofInt 32 1))
    (hget : fd_f25519_pow22523.blocks.get self hself
      = ⟨_, interBody γmd γm₀ γm₁ γsd γss γc next hγmd hγm₀ hγm₁ hγsd hγss hγc hnext⟩)
    {Q₀ Q₁ Q₂ : GlobalState → Prop}
    (hmul : ∀ s, Q₀ s → ∃ s',
      StateT.run (runFunction (fd_f25519_mul.denote
          (Ctxt.Valuation.ofHVector [.value m₁, .value m₀, .value md]ₕ))) s
        = .value ([.value md]ₕ, s')
      ∧ Q₁ s')
    (hsqr : ∀ s, Q₁ s → ∃ s',
      StateT.run (runFunction (fd_f25519_sqr.denote
          (Ctxt.Valuation.ofHVector [.value ss, .value sd]ₕ))) s
        = .value ([.value sd]ₕ, s')
      ∧ Q₂ s')
    {u : GlobalState} (h₀ : Q₀ u) :
    Hop V u (seg self hself) (hdr next hnext) Q₂ := by
  obtain ⟨u₁, hrun₁, h₁⟩ := hmul u h₀
  obtain ⟨u₂, hrun₂, h₂⟩ := hsqr u₁ h₁
  have key : ∃ Vout,
      StateT.run ((fd_f25519_pow22523.blocks.get self hself).2.denote
          (Ctxt.Valuation.ofHVector
            (HVector.nil : HVector _ ([] : List SLLVM.Ty)).reverse ++ V)) u
        = .value ((Vout, .inr (hdr next hnext)), u₂) := by
    rw [hget]
    dsimp only
    delta interBody
    refine ⟨?val, ?run⟩
    case run =>
      peel_call hrun₁ with hVmd, hVm₀, hVm₁
      peel_call hrun₂ with hVsd, hVss
      simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote_mk,
        simp_denote, simp_sllvm,
        HVector.reverse_nil, Ctxt.Valuation.ofHVector_nil,
        Ctxt.Valuation.nil_append, hV1]
      rfl
  obtain ⟨Vout, hrun⟩ := key
  refine ⟨u₂, ?_, h₂⟩
  rw [Blocks.run_step (t := seg self hself)]
  dsimp only
  rw [EffectM.run_bind, hrun, PoisonOr.value_bind]

section Loops

variable {t₀ t₁ t₂ a o : Pointer} {n₀ : Nat} {s₀ : GlobalState}
  {v₀ v₁ v₂ : ZMod p} {z₀ z₁ z₂ : Prop} {u : GlobalState}
  (V : fd_f25519_pow22523.Γout.Valuation)

/-- The `loop_run` step obligation for a loop over `t₁`. -/
private def step₁ (ids : Ids t₀ t₁ t₂ a o n₀) :
    ∀ w s, State t₀ t₁ t₂ n₀ s₀ v₀ w v₂ z₀ z₁ z₂ s → ∃ s',
      StateT.run (runFunction (fd_f25519_sqr.denote
          (Ctxt.Valuation.ofHVector [.value t₁, .value t₁]ₕ))) s
        = .value ([.value t₁]ₕ, s')
      ∧ State t₀ t₁ t₂ n₀ s₀ v₀ (w * w) v₂ z₀ z₁ z₂ s' := fun _ _ pw => by
  obtain ⟨s', hrun, st, hz⟩ := sqr_step' pw.wf pw.p₁ pw.p₁ pw.v₁h pw.b₁.loose
  exact ⟨s', hrun, State.update₁ ids pw st fun h => pw.zh₁ (hz h)⟩

/-- The `loop_run` step obligation for a loop over `t₂`. -/
private def step₂ (ids : Ids t₀ t₁ t₂ a o n₀) :
    ∀ w s, State t₀ t₁ t₂ n₀ s₀ v₀ v₁ w z₀ z₁ z₂ s → ∃ s',
      StateT.run (runFunction (fd_f25519_sqr.denote
          (Ctxt.Valuation.ofHVector [.value t₂, .value t₂]ₕ))) s
        = .value ([.value t₂]ₕ, s')
      ∧ State t₀ t₁ t₂ n₀ s₀ v₀ v₁ (w * w) z₀ z₁ z₂ s' := fun _ _ pw => by
  obtain ⟨s', hrun, st, hz⟩ := sqr_step' pw.wf pw.p₂ pw.p₂ pw.v₂h pw.b₂.loose
  exact ⟨s', hrun, State.update₂ ids pw st fun h => pw.zh₂ (hz h)⟩

/-- `t₀ ← t₁ · t₀` (the mul of `^bb1`/`^bb7`). -/
private def mulStepA (ids : Ids t₀ t₁ t₂ a o n₀) :
    ∀ s, State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ s → ∃ s',
      StateT.run (runFunction (fd_f25519_mul.denote
          (Ctxt.Valuation.ofHVector [.value t₀, .value t₁, .value t₀]ₕ))) s
        = .value ([.value t₀]ₕ, s')
      ∧ State t₀ t₁ t₂ n₀ s₀ (v₁ * v₀) v₁ v₂ (z₁ ∨ z₀) z₁ z₂ s' := fun _ pw => by
  obtain ⟨s', hrun, st, hz⟩ :=
    mul_step' pw.wf pw.p₀ pw.p₁ pw.p₀ pw.v₁h pw.v₀h pw.b₁.loose pw.b₀.loose
  exact ⟨s', hrun, State.update₀ ids pw st fun h => (hz h).imp pw.zh₁ pw.zh₀⟩

/-- `t₁ ← t₀ ^ 2` (the sqr of `^bb1`/`^bb7`). -/
private def sqrStepA (ids : Ids t₀ t₁ t₂ a o n₀) :
    ∀ s, State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ s → ∃ s',
      StateT.run (runFunction (fd_f25519_sqr.denote
          (Ctxt.Valuation.ofHVector [.value t₀, .value t₁]ₕ))) s
        = .value ([.value t₁]ₕ, s')
      ∧ State t₀ t₁ t₂ n₀ s₀ v₀ (v₀ ^ 2) v₂ z₀ z₀ z₂ s' := fun _ pw => by
  obtain ⟨s', hrun, st, hz⟩ := sqr_step' pw.wf pw.p₁ pw.p₀ pw.v₀h pw.b₀.loose
  exact ⟨s', hrun, (State.update₁ ids pw st fun h => pw.zh₀ (hz h)).cast rfl (by ring) rfl⟩

/-- `t₁ ← t₁ · t₀` (the mul of `^bb3`/`^bb9`). -/
private def mulStepB (ids : Ids t₀ t₁ t₂ a o n₀) :
    ∀ s, State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ s → ∃ s',
      StateT.run (runFunction (fd_f25519_mul.denote
          (Ctxt.Valuation.ofHVector [.value t₀, .value t₁, .value t₁]ₕ))) s
        = .value ([.value t₁]ₕ, s')
      ∧ State t₀ t₁ t₂ n₀ s₀ v₀ (v₁ * v₀) v₂ z₀ (z₁ ∨ z₀) z₂ s' := fun _ pw => by
  obtain ⟨s', hrun, st, hz⟩ :=
    mul_step' pw.wf pw.p₁ pw.p₁ pw.p₀ pw.v₁h pw.v₀h pw.b₁.loose pw.b₀.loose
  exact ⟨s', hrun, State.update₁ ids pw st fun h => (hz h).imp pw.zh₁ pw.zh₀⟩

/-- `t₂ ← t₁ ^ 2` (the sqr of `^bb3`/`^bb9`). -/
private def sqrStepB (ids : Ids t₀ t₁ t₂ a o n₀) :
    ∀ s, State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ s → ∃ s',
      StateT.run (runFunction (fd_f25519_sqr.denote
          (Ctxt.Valuation.ofHVector [.value t₁, .value t₂]ₕ))) s
        = .value ([.value t₂]ₕ, s')
      ∧ State t₀ t₁ t₂ n₀ s₀ v₀ v₁ (v₁ ^ 2) z₀ z₁ z₁ s' := fun _ pw => by
  obtain ⟨s', hrun, st, hz⟩ := sqr_step' pw.wf pw.p₂ pw.p₁ pw.v₁h pw.b₁.loose
  exact ⟨s', hrun, (State.update₂ ids pw st fun h => pw.zh₁ (hz h)).cast rfl rfl (by ring)⟩

/-- `t₁ ← t₂ · t₁` (the mul of `^bb5`/`^bb11`). -/
private def mulStepC (ids : Ids t₀ t₁ t₂ a o n₀) :
    ∀ s, State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ s → ∃ s',
      StateT.run (runFunction (fd_f25519_mul.denote
          (Ctxt.Valuation.ofHVector [.value t₁, .value t₂, .value t₁]ₕ))) s
        = .value ([.value t₁]ₕ, s')
      ∧ State t₀ t₁ t₂ n₀ s₀ v₀ (v₂ * v₁) v₂ z₀ (z₂ ∨ z₁) z₂ s' := fun _ pw => by
  obtain ⟨s', hrun, st, hz⟩ :=
    mul_step' pw.wf pw.p₁ pw.p₂ pw.p₁ pw.v₂h pw.v₁h pw.b₂.loose pw.b₁.loose
  exact ⟨s', hrun, State.update₁ ids pw st fun h => (hz h).imp pw.zh₂ pw.zh₁⟩

/-- `t₁ ← t₁ ^ 2` (the sqr of `^bb5`/`^bb11`). -/
private def sqrStepC (ids : Ids t₀ t₁ t₂ a o n₀) :
    ∀ s, State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ s → ∃ s',
      StateT.run (runFunction (fd_f25519_sqr.denote
          (Ctxt.Valuation.ofHVector [.value t₁, .value t₁]ₕ))) s
        = .value ([.value t₁]ₕ, s')
      ∧ State t₀ t₁ t₂ n₀ s₀ v₀ (v₁ ^ 2) v₂ z₀ z₁ z₂ s' := fun _ pw => by
  obtain ⟨s', hrun, st, hz⟩ := sqr_step' pw.wf pw.p₁ pw.p₁ pw.v₁h pw.b₁.loose
  exact ⟨s', hrun, (State.update₁ ids pw st fun h => pw.zh₁ (hz h)).cast rfl (by ring) rfl⟩

variable (ids : Ids t₀ t₁ t₂ a o n₀)
  {V : fd_f25519_pow22523.Γout.Valuation}
  (env : EntryEnv t₀ t₁ t₂ a o V)
  (ps : State t₀ t₁ t₂ n₀ s₀ v₀ v₁ v₂ z₀ z₁ z₂ u)
include ids env ps

/-- `^bb2` (block index 1) → `^bb1` (index 0): four `sqr(t₁, t₁)`,
so `t₁ ← t₁ ^ 2 ^ 4`. -/
lemma bb2_run :
    Hop V u (hdr 1) (seg 0)
      (State t₀ t₁ t₂ n₀ s₀ v₀ (v₁ ^ 2 ^ 4) v₂ z₀ z₁ z₂) :=
  loop_run V 5 (by norm_num) (by norm_num) env.v7 (by exact_mod_cast env.c5) env.c1
    (by rfl) _ (step₁ ids) ps

/-- `^bb4` (index 3) → `^bb3` (index 2): nine `sqr(t₁, t₁)`. -/
lemma bb4_run :
    Hop V u (hdr 3) (seg 2)
      (State t₀ t₁ t₂ n₀ s₀ v₀ (v₁ ^ 2 ^ 9) v₂ z₀ z₁ z₂) :=
  loop_run V 10 (by norm_num) (by norm_num) env.v7 (by exact_mod_cast env.c10) env.c1
    (by rfl) _ (step₁ ids) ps

/-- `^bb6` (index 5) → `^bb5` (index 4): nineteen `sqr(t₂, t₂)`. -/
lemma bb6_run :
    Hop V u (hdr 5) (seg 4)
      (State t₀ t₁ t₂ n₀ s₀ v₀ v₁ (v₂ ^ 2 ^ 19) z₀ z₁ z₂) :=
  loop_run V 20 (by norm_num) (by norm_num) env.v8 (by exact_mod_cast env.c20) env.c1
    (by rfl) _ (step₂ ids) ps

/-- `^bb8` (index 7) → `^bb7` (index 6): nine `sqr(t₁, t₁)`. -/
lemma bb8_run :
    Hop V u (hdr 7) (seg 6)
      (State t₀ t₁ t₂ n₀ s₀ v₀ (v₁ ^ 2 ^ 9) v₂ z₀ z₁ z₂) :=
  loop_run V 10 (by norm_num) (by norm_num) env.v7 (by exact_mod_cast env.c10) env.c1
    (by rfl) _ (step₁ ids) ps

/-- `^bb10` (index 9) → `^bb9` (index 8): forty-nine `sqr(t₁, t₁)`. -/
lemma bb10_run :
    Hop V u (hdr 9) (seg 8)
      (State t₀ t₁ t₂ n₀ s₀ v₀ (v₁ ^ 2 ^ 49) v₂ z₀ z₁ z₂) :=
  loop_run V 50 (by norm_num) (by norm_num) env.v7 (by exact_mod_cast env.c50) env.c1
    (by rfl) _ (step₁ ids) ps

/-- `^bb12` (index 11) → `^bb11` (index 10): ninety-nine `sqr(t₂, t₂)`. -/
lemma bb12_run :
    Hop V u (hdr 11) (seg 10)
      (State t₀ t₁ t₂ n₀ s₀ v₀ v₁ (v₂ ^ 2 ^ 99) z₀ z₁ z₂) :=
  loop_run V 100 (by norm_num) (by norm_num) env.v8 (by exact_mod_cast env.c100) env.c1
    (by rfl) _ (step₂ ids) ps

/-- `^bb14` (index 13) → `^bb13` (index 12): forty-nine `sqr(t₁, t₁)`. -/
lemma bb14_run :
    Hop V u (hdr 13) (seg 12)
      (State t₀ t₁ t₂ n₀ s₀ v₀ (v₁ ^ 2 ^ 49) v₂ z₀ z₁ z₂) :=
  loop_run V 50 (by norm_num) (by norm_num) env.v7 (by exact_mod_cast env.c50) env.c1
    (by rfl) _ (step₁ ids) ps

/-- `^bb1` (index 0) → `^bb4` (index 3): `t₀ ← t₁·t₀`, `t₁ ← t₀²`. -/
lemma bb1_run :
    Hop V u (seg 0) (hdr 3)
      (State t₀ t₁ t₂ n₀ s₀ (v₁ * v₀) ((v₁ * v₀) ^ 2) v₂ (z₁ ∨ z₀) (z₁ ∨ z₀) z₂) :=
  inter_run V env.v6 env.v7 env.v6 env.v7 env.v6 env.c1 (by rfl)
    (mulStepA ids) (sqrStepA ids) ps

/-- `^bb3` (index 2) → `^bb6` (index 5): `t₁ ← t₁·t₀`, `t₂ ← t₁²`. -/
lemma bb3_run :
    Hop V u (seg 2) (hdr 5)
      (State t₀ t₁ t₂ n₀ s₀ v₀ (v₁ * v₀) ((v₁ * v₀) ^ 2) z₀ (z₁ ∨ z₀) (z₁ ∨ z₀)) :=
  inter_run V env.v7 env.v7 env.v6 env.v8 env.v7 env.c1 (by rfl)
    (mulStepB ids) (sqrStepB ids) ps

/-- `^bb5` (index 4) → `^bb8` (index 7): `t₁ ← t₂·t₁`, `t₁ ← t₁²`. -/
lemma bb5_run :
    Hop V u (seg 4) (hdr 7)
      (State t₀ t₁ t₂ n₀ s₀ v₀ ((v₂ * v₁) ^ 2) v₂ z₀ (z₂ ∨ z₁) z₂) :=
  inter_run V env.v7 env.v8 env.v7 env.v7 env.v7 env.c1 (by rfl)
    (mulStepC ids) (sqrStepC ids) ps

/-- `^bb7` (index 6) → `^bb10` (index 9): `t₀ ← t₁·t₀`, `t₁ ← t₀²`. -/
lemma bb7_run :
    Hop V u (seg 6) (hdr 9)
      (State t₀ t₁ t₂ n₀ s₀ (v₁ * v₀) ((v₁ * v₀) ^ 2) v₂ (z₁ ∨ z₀) (z₁ ∨ z₀) z₂) :=
  inter_run V env.v6 env.v7 env.v6 env.v7 env.v6 env.c1 (by rfl)
    (mulStepA ids) (sqrStepA ids) ps

/-- `^bb9` (index 8) → `^bb12` (index 11): `t₁ ← t₁·t₀`, `t₂ ← t₁²`. -/
lemma bb9_run :
    Hop V u (seg 8) (hdr 11)
      (State t₀ t₁ t₂ n₀ s₀ v₀ (v₁ * v₀) ((v₁ * v₀) ^ 2) z₀ (z₁ ∨ z₀) (z₁ ∨ z₀)) :=
  inter_run V env.v7 env.v7 env.v6 env.v8 env.v7 env.c1 (by rfl)
    (mulStepB ids) (sqrStepB ids) ps

/-- `^bb11` (index 10) → `^bb14` (index 13): `t₁ ← t₂·t₁`, `t₁ ← t₁²`. -/
lemma bb11_run :
    Hop V u (seg 10) (hdr 13)
      (State t₀ t₁ t₂ n₀ s₀ v₀ ((v₂ * v₁) ^ 2) v₂ z₀ (z₂ ∨ z₁) z₂) :=
  inter_run V env.v7 env.v8 env.v7 env.v7 env.v7 env.c1 (by rfl)
    (mulStepC ids) (sqrStepC ids) ps

end Loops

/-- `^bb13` (index 12), the tail: `t₀ ← t₁·t₀`, `t₀ ← t₀²`, `t₀ ← t₀²`,
`o ← t₀·a`, three dead `lifetime.end`s, `return o`:

    ^bb13:
      %53 = llvm.call @fd_f25519_mul(%6, %7, %6)
      %54 = llvm.call @fd_f25519_sqr(%6, %6)
      %55 = llvm.call @fd_f25519_sqr(%6, %6)
      %56 = llvm.call @fd_f25519_mul(%arg0, %6, %arg1)
      llvm.intr.lifetime.end %8 ; %7 ; %6
      llvm.return %arg0

The walk ends here, so
the conclusion is the spec's own shape: `o` reads `(v₁·v₀)⁴·a` with tight
limbs, and the final state is the entry state plus that one splice, up to
`popFrame` (`popFrame_equiv_splice` -- the frame is pinned to
`s₀.alloc.nextFreeBlock`, which that lemma wants). -/
lemma bb13_run {t₀ t₁ t₂ a o : Pointer} {s₀ : GlobalState}
    {v₀ v₁ v₂ : ZMod p} {z₀ z₁ z₂ : Prop} {u : GlobalState}
    {V : fd_f25519_pow22523.Γout.Valuation}
    (hs₀ : s₀.WF) (ho : IsFieldElemPtr s₀.mem o) (ha : IsFieldElemPtr s₀.mem a)
    (halimb : LimbBounds.Loose ha)
    (ids : Ids t₀ t₁ t₂ a o s₀.alloc.nextFreeBlock)
    (env : EntryEnv t₀ t₁ t₂ a o V)
    (ps : State t₀ t₁ t₂ s₀.alloc.nextFreeBlock s₀ v₀ v₁ v₂ z₀ z₁ z₂ u) :
    ∃ (out : Fin 5 → BitVec 64) (final : GlobalState),
      StateT.run (fd_f25519_pow22523.blocks.run V (seg 12)) u
        = .value ([.value o]ₕ, final)
      ∧ readFieldElem (isFieldElemPtr_splice (p := o) (x := packLimbs out) ho)
          = (v₁ * v₀) ^ 4 * readFieldElem ha
      ∧ LimbBounds (isFieldElemPtr_splice (p := o) (x := packLimbs out) ho)
      ∧ ({ s₀ with mem := s₀.mem.splice o (packLimbs out) } : GlobalState)
          ≈ s₀.popFrame final.mem
      ∧ (ZeroLimbs o (s₀.mem.splice o (packLimbs out)) → (z₁ ∨ z₀) ∨ ZeroLimbs a s₀.mem) := by
  -- `t₀ ← t₁·t₀`, `t₀ ← t₀²`, `t₀ ← t₀²`
  obtain ⟨u₁, hrun₁, st₁, hz₁⟩ :=
    mul_step' ps.wf ps.p₀ ps.p₁ ps.p₀ ps.v₁h ps.v₀h ps.b₁.loose ps.b₀.loose
  have ps₁ := State.update₀ ids ps st₁ fun h => (hz₁ h).imp ps.zh₁ ps.zh₀
  obtain ⟨u₂, hrun₂, st₂, hz₂⟩ := sqr_step' ps₁.wf ps₁.p₀ ps₁.p₀ ps₁.v₀h ps₁.b₀.loose
  have ps₂ := State.update₀ ids ps₁ st₂ fun h => ps₁.zh₀ (hz₂ h)
  obtain ⟨u₃, hrun₃, st₃, hz₃⟩ := sqr_step' ps₂.wf ps₂.p₀ ps₂.p₀ ps₂.v₀h ps₂.b₀.loose
  have ps₃ := State.update₀ ids ps₂ st₃ fun h => ps₂.zh₀ (hz₃ h)
  -- `o ← t₀·a`: both operands live below the frame
  have po : IsFieldElemPtr u₃.mem o :=
    isFieldElemPtr_of_live?_eq (ps₃.fb o.id ids.ido) ho
  obtain ⟨pa, hva, hba⟩ := ps₃.operand_facts ids.ida ha halimb
  obtain ⟨u₄, hrun₄, st₄, hz₄⟩ :=
    mul_step' ps₃.wf po ps₃.p₀ pa ps₃.v₀h hva ps₃.b₀.loose hba
  obtain ⟨x, hx⟩ := st₄.splice
  -- `o` in the final state is the entry `o` plus the last write
  have hlive : (s₀.mem.splice o x).live? o.id = u₄.mem.live? o.id :=
    (live?_splice_congr (ps₃.fb o.id ids.ido).symm).trans hx.symm
  refine ⟨fun i => x.extractLsb' (64 * i.toNat) 64, u₄, ?run, ?rest⟩
  case rest =>
    rw [packLimbs_extractLsb']
    refine ⟨?val, ?bnd, ?equiv, fun h => ?zero⟩
    case zero =>
      exact (hz₄ (ZeroLimbs.of_live?_eq hlive h)).imp ps₃.zh₀
        (ZeroLimbs.of_live?_eq (ps₃.fb a.id ids.ida))
    case val =>
      refine (readFieldElem_eq_of
        ((readFieldElem?_of_live?_eq hlive).trans
          (readFieldElem?_eq_some st₄.ptr st₄.val))).trans ?_
      ring
    case bnd =>
      exact limbBounds_of_readLimb? _ fun i l hl =>
        limbBounds_readLimb? st₄.ptr st₄.bnd i l
          (by rwa [readLimb?_of_live?_eq hlive] at hl)
    case equiv =>
      exact popFrame_equiv_splice hs₀ ids.ido
        (fun b hb hbo => (st₄.live b (Ne.symm hbo)).trans (ps₃.fb b hb)) hlive.symm
  case run =>
    have key : ∃ Vout,
        StateT.run ((fd_f25519_pow22523.blocks.get 12 (by rfl)).2.denote
            (Ctxt.Valuation.ofHVector
              (HVector.nil : HVector _ ([] : List SLLVM.Ty)).reverse ++ V)) u
          = .value ((Vout, .inl [.value o]ₕ), u₄) := by
      -- `^bb13` is used once, so no `loopBody`-style template: reduce
      -- `blocks.get 12` to the literal block in place
      denote_reduce_get
      refine ⟨?val, ?run⟩
      case run =>
        peel_call hrun₁ with env.v6, env.v7
        peel_call hrun₂ with env.v6
        peel_call hrun₃ with env.v6
        peel_call hrun₄ with env.v6, env.va, env.vo
        simp only [BlockCom.denote_var, BlockCom.denote_term, Terminator.denote_ret,
          simp_denote, simp_sllvm, HVector.map]
        -- the returned lookup is `V`'s `%o` slot up to defeq
        exact congrArg (fun x => ((_, Sum.inl (x ::ₕ HVector.nil)), u₄)) env.vo
    obtain ⟨Vout, hrun⟩ := key
    rw [Blocks.run_step (t := seg 12)]
    dsimp only
    rw [EffectM.run_bind, hrun, PoisonOr.value_bind]
    rfl

end Pow22523

open Pow22523 in
theorem fd_f25519_pow22523_conforms (o a : Pointer) (s : GlobalState)
    (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o)
    (ha : IsFieldElemPtr s.mem a)
    (halimb : LimbBounds.Loose ha) :
    fd_f25519_pow22523_spec o a s ho ha := by
  simp only [fd_f25519_pow22523_spec]
  -- After `^bb0`:
  -- t₀, t₁, t₂: Temp value pointers
  -- w₂: Value of t₂
  -- u: GlobalState after
  -- ids: Statements about the pointers
  -- ps: what holds of the locals afterwards
  -- hentry: Execution equivalence
  obtain ⟨t₀, t₁, t₂, w₂, u, V, ids, ps, env, hentry⟩ := bb0_run o a s hs ho ha halimb
  -- Remove the runFunction wrapper
  suffices h : ∃ (out : Fin 5 → BitVec 64) (final : GlobalState),
      StateT.run (fd_f25519_pow22523.denote
          (Ctxt.Valuation.ofHVector [.value a, .value o]ₕ)) s
        = .value ([.value o]ₕ, final)
      ∧ readFieldElem (isFieldElemPtr_splice (p := o) (x := packLimbs out) ho)
          = readFieldElem ha ^ (2 ^ 252 - 3)
      ∧ LimbBounds (isFieldElemPtr_splice (p := o) (x := packLimbs out) ho)
      ∧ ({ s with mem := s.mem.splice o (packLimbs out) } : GlobalState)
          ≈ s.popFrame final.mem
      ∧ (ZeroLimbs o (s.mem.splice o (packLimbs out)) → ZeroLimbs a s.mem) by
    obtain ⟨out, final, hrun, hval, hbnd, heq, hzero⟩ := h
    exact ⟨out, hval, hbnd, ⟨s.popFrame final.mem, run_runFunction hrun, heq⟩, hzero⟩
  -- Everything left is the walk from `^bb2` with the counter at `1`.
  rw [hentry]
  clear hentry
  obtain ⟨u, hu, ps⟩ := bb2_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb1_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb4_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb3_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb6_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb5_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb8_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb7_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb10_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb9_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb12_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb11_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨u, hu, ps⟩ := bb14_run ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  obtain ⟨out, u, hu, ps⟩ := bb13_run hs ho ha halimb ids env ps; rw [hu]; rename_i u' st'; clear hu st' u'
  -- the flags are towers of the input's all-zero limbs
  refine ⟨out, u, by rfl, ?_, ps.2.1, ps.2.2.1, fun h => by simpa only [or_self] using ps.2.2.2 h⟩

  rw [ps.left]
  ring

end Firedancer.Ref
