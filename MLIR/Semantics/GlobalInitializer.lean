module

public import MLIR.GlobalInitializer
public import MLIR.Semantics.Func
import Std.Data.ExtHashMap.Lemmas

namespace MLIR

@[expose] public section

def GlobalInitializer.blockParams {Γ : Ctx} : Fin 1 → Dsts Γ [] := fun _ => Dsts.nil

def GlobalInitializer.initEnv (initializer : GlobalInitializer) :=
  Env.init (Γ := initializer.Γ)
    (fun i => by
      simp [initializer.hΓ] at i
      exact i.elim0)

def GlobalInitializer.value (initializer : GlobalInitializer) := do
  let (_, blockVal) ← initializer.block.run blockParams initializer.initEnv
  let .inl (Vals.cons v Vals.nil) := blockVal | throwUB
  return v

theorem GlobalInitializer.compute_value (initializer : GlobalInitializer) v
    (h :
      ∃ env',
        initializer.block.run blockParams initializer.initEnv s =
          .value ((env', .inl (Vals.cons v Vals.nil)), s)) :
    initializer.value s = .value (v, s) := by
  unfold value
  obtain ⟨env, h'⟩ := h
  rw [EffectM.bind_eq, h']
  dsimp
  rfl

/-- The state an initializer is run in: it reads none. -/
def GlobalInitializer.runState : GlobalState :=
  ⟨⟨1⟩, ⟨∅⟩⟩

/-- A global's bytes: its value's bits and definedness, padded to whole bytes undefined (all
undefined for a UB initializer). -/
def GlobalInitializer.image (g : GlobalInitializer) : GlobalImage :=
  match g.value runState with
  | .value (x, _) =>
    ⟨(g.t.width + 7) / 8, (g.t.flattenDef x).1.setWidth _, (g.t.flattenDef x).2.setWidth _,
      g.constant, g.unnamedAddr⟩
  | .poison => ⟨(g.t.width + 7) / 8, 0, 0, g.constant, g.unnamedAddr⟩

/-- The image of a global whose initializer gives `x`. -/
theorem GlobalInitializer.image_eq {g : GlobalInitializer} {x : ⟦g.t⟧}
    (hv : ∀ s, g.value s = .value (x, s)) :
    g.image =
      ⟨(g.t.width + 7) / 8, (g.t.flattenDef x).1.setWidth _, (g.t.flattenDef x).2.setWidth _,
        g.constant, g.unnamedAddr⟩ := by
  simp [image, hv]

/-- A global's block: its table entry's, else the null pointer's. -/
def MemoryState.globalBlock (m : MemoryState) (sym : String) : BlockId :=
  ((m.globals sym).map Prod.fst).getD ⟨0⟩

/-- `m` holds the globals `G`: each one's symbol has a block with its image. -/
def MemoryState.Globals (m : MemoryState) (G : List Global) : Prop :=
  ∀ g ∈ G, ∃ b, m.globals g.sym = some (b, g.init.image)

/-- Fewer globals, in a memory with the same table. -/
theorem MemoryState.Globals.mono {m m' : MemoryState} {G G' : List Global} (h : m.Globals G)
    (ht : m'.globals = m.globals) (hsub : ∀ g ∈ G', g ∈ G) : m'.Globals G' := by
  intro g hg
  rw [ht]
  exact h g (hsub g hg)

/-- No globals. -/
theorem MemoryState.Globals.nil {m : MemoryState} : m.Globals [] := fun _ h =>
  absurd h List.not_mem_nil

/-- The block of `g`, held: `addressof` gives its start. -/
theorem MemoryState.Globals.block {m : MemoryState} {G : List Global} (h : m.Globals G)
    (hg : g ∈ G) : ∃ b, m.globals g.sym = some (b, g.init.image) :=
  h g hg

/-- A held global's table entry: its block and image. -/
theorem MemoryState.Globals.globals_eq {m : MemoryState} {G : List Global} (h : m.Globals G)
    (hg : g ∈ G) : m.globals g.sym = some (m.globalBlock g.sym, g.init.image) := by
  obtain ⟨b, hb⟩ := h g hg
  simp [globalBlock, hb]

/-- An image is its initializer's constness. -/
theorem GlobalInitializer.image_constant {g : GlobalInitializer} :
    g.image.constant = g.constant := by
  unfold image; split <;> rfl

/-- A constant global's block in a `WF` state holds its image. -/
theorem GlobalState.WF.const_block {s : GlobalState} (hwf : s.WF)
    (h : s.mem.globals sym = some (b, g)) (hc : g.constant = true) : s.mem[b]? = some g.block := by
  have := hwf.global sym b g h
  simpa [hc] using this

/-- A mutable global's block in a `WF` state is writable, its image's length. -/
theorem GlobalState.WF.mutable_block {s : GlobalState} (hwf : s.WF)
    (h : s.mem.globals sym = some (b, g)) (hc : g.constant = false) :
    ∃ blk, s.mem[b]? = some blk ∧ blk.writable = true ∧ blk.length = g.bytes := by
  have := hwf.global sym b g h
  simpa [hc] using this

/-- A global's block in a `WF` state is below the counter. -/
theorem GlobalState.WF.global_lt {s : GlobalState} (hwf : s.WF)
    (h : s.mem.globals sym = some (b, g)) : b.id < s.alloc.nextFreeBlock := by
  have hm : b ∈ s.mem.mem := by
    rw [Std.ExtHashMap.mem_iff_isSome_getElem?, ← MemoryState.getElem?_eq]
    have := hwf.global sym b g h
    split at this
    · simp [this]
    · obtain ⟨blk, hb, -⟩ := this; simp [hb]
  exact hwf.bound b hm

/-! ### Placing globals -/

/-- `s` with `img` placed in the next block and recorded for `sym`. -/
def GlobalState.place (s : GlobalState) (sym : String) (img : GlobalImage) : GlobalState :=
  { alloc := ⟨s.alloc.nextFreeBlock + 1⟩,
    mem :=
      @MemoryState.mk (s.mem.mem.insert ⟨s.alloc.nextFreeBlock⟩ img.block) s.mem.unspec
        ⟨fun x => if x = sym then some (⟨s.alloc.nextFreeBlock⟩, img) else s.mem.globals x⟩ }

/-- `s` with the globals `G` placed in new blocks, each symbol once (its first entry): an initial
state for running a program. -/
def GlobalState.withGlobals (G : List Global) (s : GlobalState) : GlobalState :=
  G.foldl (fun s g => if (s.mem.globals g.sym).isSome then s else s.place g.sym g.init.image) s

/-- Each symbol's entries in `G` have one image. -/
def Global.Consistent (G : List Global) : Prop :=
  ∀ g ∈ G, ∀ h ∈ G, g.sym = h.sym → g.init.image = h.init.image

theorem GlobalState.place_globals {s : GlobalState} :
    (s.place sym img).mem.globals x =
      if x = sym then some (⟨s.alloc.nextFreeBlock⟩, img) else s.mem.globals x :=
  rfl

theorem GlobalState.place_getElem? {s : GlobalState} {b : BlockId} :
    (s.place sym img).mem[b]? =
      if b = ⟨s.alloc.nextFreeBlock⟩ then some img.block else s.mem[b]? := by
  simp only [place, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  split <;> split <;> simp_all

/-- Placing a global for a symbol without one keeps a state `WF`. -/
theorem GlobalState.WF.place {s : GlobalState} (hs : s.WF) (hnone : s.mem.globals sym = none) :
    (s.place sym img).WF := by
  have hfresh : ∀ b : BlockId, s.mem[b]?.isSome → b ≠ ⟨s.alloc.nextFreeBlock⟩ := by
    intro b hb he
    have hm : b ∈ s.mem.mem := by
      rw [Std.ExtHashMap.mem_iff_isSome_getElem?, ← MemoryState.getElem?_eq]; exact hb
    have := hs.bound b hm
    simp [he] at this
  have hold : ∀ x (b : BlockId) g, s.mem.globals x = some (b, g) → b ≠ ⟨s.alloc.nextFreeBlock⟩ := by
    intro x b g h
    apply hfresh
    have := hs.global x b g h
    split at this
    · simp [this]
    · obtain ⟨blk, hb, -⟩ := this; simp [hb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp only [GlobalState.place, Std.ExtHashMap.mem_insert] at hk ⊢
    rcases hk with hk | hk
    · have : (⟨s.alloc.nextFreeBlock⟩ : BlockId) = k := by simpa using hk
      subst this; simp
    · have := hs.bound k hk; omega
  · simp [GlobalState.place]
  · simp only [GlobalState.place, Std.ExtHashMap.mem_insert, not_or]
    have := hs.pos
    exact
      ⟨by
        simp; omega, hs.null⟩
  · intro x b g h
    rw [place_globals] at h
    split at h
    · cases h
      rw [place_getElem?]
      by_cases hc : img.constant <;> simp [hc, GlobalImage.block]
    · have := hs.global x b g h
      rw [place_getElem?]
      simpa [hold x b g h] using this
  · intro x x' b g g' h h' hne
    rw [place_globals] at h h'
    split at h <;> split at h'
    · subst_vars; exact absurd rfl hne
    · cases h; exact absurd rfl (hold _ _ _ h')
    · cases h'; exact absurd rfl (hold _ _ _ h)
    · exact hs.merged x x' b g g' h h' hne

/-- `withGlobals` keeps a state `WF`. -/
theorem GlobalState.WF.withGlobals {s : GlobalState} (hs : s.WF) : (s.withGlobals G).WF := by
  induction G generalizing s with
  | nil => exact hs
  | cons g G ih =>
    simp only [GlobalState.withGlobals, List.foldl_cons]
    split
    · exact ih hs
    · rename_i h
      exact ih (hs.place (Option.not_isSome_iff_eq_none.1 h))

/-- Without a table entry yet, `withGlobals` keeps the entries it finds. -/
theorem GlobalState.withGlobals_globals_of_some {s : GlobalState} (h : s.mem.globals x = some e) :
    (s.withGlobals G).mem.globals x = some e := by
  induction G generalizing s with
  | nil => exact h
  | cons g G ih =>
    simp only [GlobalState.withGlobals, List.foldl_cons]
    split
    · exact ih h
    · apply ih
      rw [place_globals]
      have : x ≠ g.sym := by
        rintro rfl; simp_all
      simpa [this] using h

/-- `withGlobals` of consistent globals over a table without others for their symbols holds them. -/
theorem GlobalState.withGlobals_globals {s : GlobalState} (hG : Global.Consistent G)
    (hs : ∀ g ∈ G, s.mem.globals g.sym = none ∨ ∃ b, s.mem.globals g.sym = some (b, g.init.image)) :
    (s.withGlobals G).mem.Globals G := by
  induction G generalizing s with
  | nil => exact MemoryState.Globals.nil
  | cons g G
    ih =>
    have hG' : Global.Consistent G := fun a ha b hb => hG a (by simp [ha]) b (by simp [hb])
    simp only [GlobalState.withGlobals, List.foldl_cons]
    split
    · rename_i hsome
      obtain ⟨b, hb⟩ : ∃ b, s.mem.globals g.sym = some (b, g.init.image) := by
        rcases hs g (by simp) with h | h
        · simp [h] at hsome
        · exact h
      intro h hh
      rcases List.mem_cons.1 hh with rfl | hh
      · exact ⟨b, withGlobals_globals_of_some hb⟩
      · exact ih hG' (fun k hk => hs k (by simp [hk])) h hh
    · rename_i hnone
      have hgs :
        (s.place g.sym g.init.image).mem.globals g.sym =
          some (⟨s.alloc.nextFreeBlock⟩, g.init.image) := by
        simp [place_globals]
      intro h hh
      rcases List.mem_cons.1 hh with rfl | hh
      · exact ⟨_, withGlobals_globals_of_some hgs⟩
      · refine ih hG' (fun k hk => ?_) h hh
        rw [place_globals]
        split
        · rename_i he
          exact .inr ⟨_, by rw [hG g (by simp) k (by simp [hk]) he.symm]⟩
        · exact hs k (by simp [hk])

end

end MLIR
