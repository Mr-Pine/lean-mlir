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

/-- A global's bytes: its value's bits and definedness, padded to whole bytes undefined, and its
pointer members (all undefined, none, for a UB initializer). -/
def GlobalInitializer.image (g : GlobalInitializer) : GlobalImage :=
  match g.value runState with
  | .value (x, _) =>
    ⟨(g.t.width + 7) / 8, (g.t.flattenDef x).1.setWidth _, (g.t.flattenDef x).2.setWidth _,
      g.constant, g.unnamedAddr, g.ptrs⟩
  | .poison => ⟨(g.t.width + 7) / 8, 0, 0, g.constant, g.unnamedAddr, []⟩

/-- The image of a global whose initializer gives `x`. -/
theorem GlobalInitializer.image_eq {g : GlobalInitializer} {x : ⟦g.t⟧}
    (hv : ∀ s, g.value s = .value (x, s)) :
    g.image =
      ⟨(g.t.width + 7) / 8, (g.t.flattenDef x).1.setWidth _, (g.t.flattenDef x).2.setWidth _,
        g.constant, g.unnamedAddr, g.ptrs⟩ := by
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
    (h : s.mem.globals sym = some (b, g)) (hc : g.constant = true) :
    s.mem[b]? = some (s.mem.imageBlock g) := by
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

/-- `s` with `img` placed in the next block and recorded for `sym`, its pointer members resolved by
`r`. -/
def GlobalState.place (s : GlobalState) (sym : String) (img : GlobalImage)
    (r : String → Option BlockId) : GlobalState :=
  { alloc := ⟨s.alloc.nextFreeBlock + 1⟩,
    mem :=
      @MemoryState.mk (s.mem.mem.insert ⟨s.alloc.nextFreeBlock⟩ (img.block r s.mem.addr))
        s.mem.unspec
        ⟨fun x => if x = sym then some (⟨s.alloc.nextFreeBlock⟩, img) else s.mem.globals x⟩ }

/-- One global's entry: a symbol without one given the global's image in the next block. -/
def GlobalState.tableStep (tn : (String → Option (BlockId × GlobalImage)) × Nat) (g : Global) :
    (String → Option (BlockId × GlobalImage)) × Nat :=
  if (tn.1 g.sym).isSome then tn
  else (fun x => if x = g.sym then some (⟨tn.2⟩, g.init.image) else tn.1 x, tn.2 + 1)

/-- The table `withGlobals G` leaves `s` with: each symbol's first entry in `G`, in the next free
block, unless `s` has one. -/
def GlobalState.tableWith (G : List Global) (s : GlobalState) :
    String → Option (BlockId × GlobalImage) :=
  (G.foldl tableStep (s.mem.globals, s.alloc.nextFreeBlock)).1

/-- The globals `G` placed over `s` as `withGlobals` does, pointer members resolved by `r`. -/
def GlobalState.placeAll (r : String → Option BlockId) (G : List Global) (s : GlobalState) :
    GlobalState :=
  G.foldl (fun s g => if (s.mem.globals g.sym).isSome then s else s.place g.sym g.init.image r) s

/-- `s` with the globals `G` placed in new blocks, each symbol once (its first entry), pointer
members resolved by the table they make: an initial state for running a program. -/
def GlobalState.withGlobals (G : List Global) (s : GlobalState) : GlobalState :=
  placeAll (fun sym => (tableWith G s sym).map Prod.fst) G s

/-- Each symbol's entries in `G` have one image. -/
def Global.Consistent (G : List Global) : Prop :=
  ∀ g ∈ G, ∀ h ∈ G, g.sym = h.sym → g.init.image = h.init.image

theorem GlobalState.place_globals {s : GlobalState} :
    (s.place sym img r).mem.globals x =
      if x = sym then some (⟨s.alloc.nextFreeBlock⟩, img) else s.mem.globals x :=
  rfl

theorem GlobalState.place_getElem? {s : GlobalState} {b : BlockId} :
    (s.place sym img r).mem[b]? =
      if b = ⟨s.alloc.nextFreeBlock⟩ then some (img.block r s.mem.addr) else s.mem[b]? := by
  simp only [place, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  split <;> split <;> simp_all

/-- `placeAll`'s table and counter: `tableWith`'s fold's. -/
theorem GlobalState.placeAll_table {s : GlobalState} :
    ((placeAll r G s).mem.globals, (placeAll r G s).alloc.nextFreeBlock) =
      G.foldl tableStep (s.mem.globals, s.alloc.nextFreeBlock) := by
  induction G generalizing s with
  | nil => rfl
  | cons g G ih =>
    simp only [placeAll, List.foldl_cons] at ih ⊢
    split
    · rename_i h
      rw [ih]
      simp [tableStep, h]
    · rename_i h
      rw [ih]
      simp only [tableStep, h, Bool.false_eq_true, ite_false]
      rfl

/-- `withGlobals`'s table: `tableWith`'s. -/
theorem GlobalState.withGlobals_table {s : GlobalState} :
    (s.withGlobals G).mem.globals = tableWith G s :=
  congrArg Prod.fst placeAll_table

/-- `WF` but for constants' blocks holding their images resolved by `r`. -/
structure GlobalState.WFWith (r : String → Option BlockId) (s : GlobalState) : Prop where
  bound : ∀ k ∈ s.mem.mem, k.id < s.alloc.nextFreeBlock
  pos : 0 < s.alloc.nextFreeBlock
  null : (⟨0⟩ : BlockId) ∉ s.mem.mem
  global : ∀ sym b g, s.mem.globals sym = some (b, g) →
    if g.constant then s.mem[b]? = some (g.block r s.mem.addr)
    else ∃ blk, s.mem[b]? = some blk ∧ blk.writable = true ∧ blk.length = g.bytes
  merged : ∀ sym sym' b g g', s.mem.globals sym = some (b, g) → s.mem.globals sym' = some (b, g') →
    sym ≠ sym' → g.constant = true ∧ g'.constant = true ∧ (g.unnamedAddr || g'.unnamedAddr) = true

/-- Placing a global for a symbol without one keeps `WFWith`. -/
theorem GlobalState.WFWith.place {s : GlobalState} (hs : s.WFWith r)
    (hnone : s.mem.globals sym = none) : (s.place sym img r).WFWith r := by
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
      by_cases hc : img.constant <;> simp [hc, GlobalImage.block] <;> rfl
    · have := hs.global x b g h
      rw [place_getElem?, ite_eq_right (hold x b g h)]
      exact this
  · intro x x' b g g' h h' hne
    rw [place_globals] at h h'
    split at h <;> split at h'
    · subst_vars; exact absurd rfl hne
    · cases h; exact absurd rfl (hold _ _ _ h')
    · cases h'; exact absurd rfl (hold _ _ _ h)
    · exact hs.merged x x' b g g' h h' hne

/-- `placeAll` keeps `WFWith`. -/
theorem GlobalState.WFWith.placeAll {s : GlobalState} (hs : s.WFWith r) :
    (GlobalState.placeAll r G s).WFWith r := by
  induction G generalizing s with
  | nil => exact hs
  | cons g G ih =>
    simp only [GlobalState.placeAll, List.foldl_cons] at ih ⊢
    split
    · exact ih hs
    · rename_i h
      exact ih (hs.place (Option.not_isSome_iff_eq_none.1 h))

/-- `withGlobals` of a state without globals keeps it `WF`. -/
theorem GlobalState.WF.withGlobals {s : GlobalState} (hs : s.WF)
    (hnone : ∀ x, s.mem.globals x = none) : (s.withGlobals G).WF := by
  have h : (s.withGlobals G).WFWith fun sym => (tableWith G s sym).map Prod.fst :=
    GlobalState.WFWith.placeAll
      ⟨hs.bound, hs.pos, hs.null, fun sym _ _ h => by simp [hnone sym] at h,
        fun sym _ _ _ _ h => by simp [hnone sym] at h⟩
  obtain ⟨hb, hp, hn, hg, hm⟩ := h
  refine ⟨hb, hp, hn, fun sym b g he => ?_, hm⟩
  have hr : (s.withGlobals G).mem.globalBlocks = fun sym => (tableWith G s sym).map Prod.fst := by
    funext sym
    simp [MemoryState.globalBlocks, withGlobals_table]
  rw [MemoryState.imageBlock, hr]
  exact hg sym b g he

/-- The table's fold keeps the entries it finds. -/
theorem GlobalState.tableStep_foldl_of_some {G : List Global} {x : String}
    {e : BlockId × GlobalImage} {tn : (String → Option (BlockId × GlobalImage)) × Nat}
    (h : tn.1 x = some e) : (G.foldl tableStep tn).1 x = some e := by
  induction G generalizing tn with
  | nil => exact h
  | cons g G ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [tableStep]
    split
    · exact h
    · have : x ≠ g.sym := by
        rintro rfl; simp_all
      simpa [this] using h

/-- Without a table entry yet, `withGlobals` keeps the entries it finds. -/
theorem GlobalState.withGlobals_globals_of_some {s : GlobalState} (h : s.mem.globals x = some e) :
    (s.withGlobals G).mem.globals x = some e := by
  rw [withGlobals_table]
  exact tableStep_foldl_of_some (tn := (s.mem.globals, s.alloc.nextFreeBlock)) h

/-- `withGlobals` of consistent globals over a table without others for their symbols holds them. -/
theorem GlobalState.withGlobals_globals {s : GlobalState} (hG : Global.Consistent G)
    (hs : ∀ g ∈ G, s.mem.globals g.sym = none ∨ ∃ b, s.mem.globals g.sym = some (b, g.init.image)) :
    (s.withGlobals G).mem.Globals G := by
  intro g' hg'
  rw [withGlobals_table, tableWith]
  -- the fold from any table holding `G`'s entries' images or none for them
  suffices ∀ (tn : (String → Option (BlockId × GlobalImage)) × Nat),
      (∀ g ∈ G, tn.1 g.sym = none ∨ ∃ b, tn.1 g.sym = some (b, g.init.image)) →
        ∀ g ∈ G, ∃ b, (G.foldl tableStep tn).1 g.sym = some (b, g.init.image) from
    this _ hs g' hg'
  clear hs g' hg'
  induction G with
  | nil => intro _ _ g hg; exact absurd hg List.not_mem_nil
  | cons g G ih =>
    have hG' : Global.Consistent G := fun a ha b hb => hG a (by simp [ha]) b (by simp [hb])
    intro tn htn h hh
    simp only [List.foldl_cons]
    have hstep : ∀ k ∈ G, (tableStep tn g).1 k.sym = none ∨
        ∃ b, (tableStep tn g).1 k.sym = some (b, k.init.image) := by
      intro k hk
      simp only [tableStep]
      split
      · exact htn k (by simp [hk])
      · by_cases he : k.sym = g.sym
        · exact .inr ⟨⟨tn.2⟩, by simp [he, hG g (by simp) k (by simp [hk]) he.symm]⟩
        · simpa [he] using htn k (by simp [hk])
    rcases List.mem_cons.1 hh with rfl | hh
    · -- `h`'s own entry: there before, or made now; kept either way
      have : ∃ b, (tableStep tn h).1 h.sym = some (b, h.init.image) := by
        simp only [tableStep]
        split
        · rename_i hsome
          rcases htn h (by simp) with h0 | h0
          · simp [h0] at hsome
          · exact h0
        · simp
      obtain ⟨b, hb⟩ := this
      exact ⟨b, tableStep_foldl_of_some hb⟩
    · exact ih hG' _ hstep h hh

end

end MLIR
