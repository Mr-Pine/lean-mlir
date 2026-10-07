import SSA.Projects.RIR.Semantics.Instruction

/-! Register transport for the straight-line instruction subset used by the
inlined field serializers. The simulation preserves the entire global state,
including UB; arithmetic operations and overflow flags are never rewritten.
The two coherence fields are proved for each concrete embedding, not assumed
as execution contracts. Unsupported instructions cannot satisfy `Supported`. -/

namespace Agave.Ed25519.SmallOrder.Execution.Transport
open LeanMLIR.RIR

structure Renaming (Γ Δ : Ctx) where
  reg : {t : Ty} → Reg Γ t → Reg Δ t
  dst : {t : Ty} → Dst Γ t → Dst Δ t
  pull : Env Δ → Env Γ
  read : ∀ {t} (E : Env Δ) (r : Reg Γ t), (pull E).read r = E.read (reg r)
  write : ∀ {t} (E : Env Δ) (d : Dst Γ t) (v : ⟦t⟧),
    pull (E.write (dst d) v) = (pull E).write d v

def Renaming.index (ρ : Renaming Γ Δ) : GepIndex Γ → GepIndex Δ
  | .constant k => .constant k
  | .scaled n r => .scaled n (ρ.reg r)

def Renaming.instr (ρ : Renaming Γ Δ) : Instr Γ → Instr Δ
  | .noaliasScopeDecl s => .noaliasScopeDecl s
  | .fenceSingleThread => .fenceSingleThread
  | .gep d p ix => .gep (ρ.dst d) (ρ.reg p) (ix.map ρ.index)
  | .gepInbounds d p ix => .gepInbounds (ρ.dst d) (ρ.reg p) (ix.map ρ.index)
  | .const v d => .const v (ρ.dst d)
  | .poison d => .poison (ρ.dst d)
  | .unop op d a => .unop op (ρ.dst d) (ρ.reg a)
  | .binop op d a b => .binop op (ρ.dst d) (ρ.reg a) (ρ.reg b)
  | .ternop op d a b c => .ternop op (ρ.dst d) (ρ.reg a) (ρ.reg b) (ρ.reg c)
  | .load d p => .load (ρ.dst d) (ρ.reg p)
  | .loadMonotonic d p => .loadMonotonic (ρ.dst d) (ρ.reg p)
  | .store p v => .store (ρ.reg p) (ρ.reg v)
  | .lifetimeStart p n => .lifetimeStart (ρ.reg p) n
  | .lifetimeEnd p n => .lifetimeEnd (ρ.reg p) n
  | _ => .noaliasScopeDecl "unsupported transport"

def Supported : Instr Γ → Prop
  | .assume _ | .memset _ _ _ | .memcpy _ _ _ | .alloca _ _ | .call _ _ _ => False
  | _ => True

def Renaming.result (ρ : Renaming Γ Δ) (x : PoisonOr (Env Δ × GlobalState)) :
    PoisonOr (Env Γ × GlobalState) := (fun p => (ρ.pull p.1, p.2)) <$> x

@[simp] theorem Renaming.offset (ρ : Renaming Γ Δ) (E : Env Δ) (i : GepIndex Γ) :
    (ρ.index i).offset E = i.offset (ρ.pull E) := by
  cases i <;> simp [index, GepIndex.offset, ρ.read]

@[simp] theorem Renaming.inboundsOffset (ρ : Renaming Γ Δ)
    (E : Env Δ) (i : GepIndex Γ) :
    (ρ.index i).inboundsOffset E = i.inboundsOffset (ρ.pull E) := by
  cases i <;> simp [index, GepIndex.inboundsOffset, ρ.read]

private theorem load_transport (ρ : Renaming Γ Δ) (E : Env Δ)
    (d : Dst Γ t) (p : PoisonOr Pointer) (s : GlobalState) :
    ρ.result (Operation.load (ρ.dst d) p E s) =
      Operation.load d p (ρ.pull E) s := by
  cases p with
  | poison => rfl
  | value p =>
    by_cases h : Fits s.mem p t.width <;>
      simp [Operation.load, Renaming.result, EffectM.bind_eq, EffectM.get_eq,
        EffectM.pure_eq, throwUBIf, h, ρ.write]

private theorem store_transport (ρ : Renaming Γ Δ) (E : Env Δ)
    (p : PoisonOr Pointer) (v : ⟦t⟧) (s : GlobalState) :
    ρ.result (Operation.store p v E s) = Operation.store p v (ρ.pull E) s := by
  cases p with
  | poison => rfl
  | value p =>
    by_cases h : Fits s.mem p t.width <;> cases hv : t.flatten v <;>
      simp [Operation.store, Renaming.result, EffectM.bind_eq, EffectM.get_eq,
        EffectM.set_eq, EffectM.pure_eq, throwUBIf, h, hv]

/-- Exact one-instruction simulation, retaining poison and all memory effects. -/
theorem Renaming.run (ρ : Renaming Γ Δ) (i : Instr Γ) (hi : Supported i)
    (E : Env Δ) (s : GlobalState) :
    ρ.result (Instr.run E (ρ.instr i) s) = Instr.run (ρ.pull E) i s := by
  cases i <;> try contradiction
  all_goals simp only [Renaming.instr, Instr.run, EffectM.bind_eq,
    EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, Renaming.result,
    PoisonOr.map_value, ρ.write, ρ.read]
  all_goals first
    | rfl
    | simp [List.map_map, Function.comp_def, ρ.offset, ρ.inboundsOffset, ρ.read]
    | exact load_transport ρ E _ _ s
    | exact store_transport ρ E _ _ s

/-- Lists compose without repeating any scalar normalization proof. -/
theorem Renaming.fold (ρ : Renaming Γ Δ) (body : List (Instr Γ))
    (hs : ∀ i ∈ body, Supported i) (E : Env Δ) (s : GlobalState) :
    ρ.result ((body.map ρ.instr).foldlM Instr.run E s) =
      body.foldlM Instr.run (ρ.pull E) s := by
  induction body generalizing E s with
  | nil => rfl
  | cons i body ih =>
    have hi := ρ.run i (hs i (by simp)) E s
    have ht : ∀ j ∈ body, Supported j := fun j hj => hs j (by simp [hj])
    simp only [List.map_cons, List.foldlM_cons, EffectM.bind_eq]
    cases he : Instr.run E (ρ.instr i) s with
    | poison =>
      have hi' : Instr.run (ρ.pull E) i s = .poison := by
        simpa [he, Renaming.result] using hi.symm
      simp [he, hi', Renaming.result]
    | value es =>
      have hi' : Instr.run (ρ.pull E) i s = .value (ρ.pull es.1, es.2) := by
        simpa [he, Renaming.result] using hi.symm
      simp only [he, hi', PoisonOr.value_bind]
      exact ih ht es.1 es.2

/-- A successful source execution yields an actual target environment and the
same final state. The environment outside the embedding remains unconstrained. -/
theorem Renaming.fold_success (ρ : Renaming Γ Δ) (body : List (Instr Γ))
    (hs : ∀ i ∈ body, Supported i) (E : Env Δ) (s t : GlobalState) (F : Env Γ)
    (h : body.foldlM Instr.run (ρ.pull E) s = .value (F, t)) :
    ∃ G, (body.map ρ.instr).foldlM Instr.run E s = .value (G, t) ∧ ρ.pull G = F := by
  have hm := ρ.fold body hs E s
  rw [h] at hm
  cases he : (body.map ρ.instr).foldlM Instr.run E s with
  | poison =>
    rw [he] at hm
    change PoisonOr.poison = PoisonOr.value (F, t) at hm
    cases hm
  | value gs =>
    have hp : (ρ.pull gs.1, gs.2) = (F, t) := by
      simpa [he, Renaming.result] using hm
    obtain ⟨hF, ht⟩ := Prod.mk.inj hp
    exact ⟨gs.1, by cases gs; simpa using ht, hF⟩

end Agave.Ed25519.SmallOrder.Execution.Transport
