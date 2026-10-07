import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.InstructionTransport

/-! Environment frames for the scalar instruction subset. These lemmas let
each serializer retain hoisted constants, buffer pointers, the other inline
copies' fresh registers, and the first byte-comparison result. Memory changes
are deliberately unrestricted here: they are covered by `PrivateFrame`. -/
namespace Agave.Ed25519.SmallOrder.Execution.EnvironmentFrame
open LeanMLIR.RIR

def Disjoint (r : Reg Γ t) (d : Dst Γ u) : Prop :=
  match r with
  | .arg _ _ => True
  | .val i _ => i ≠ d.i

theorem read_write (E : Env Γ) (r : Reg Γ t) (d : Dst Γ u) (v : ⟦u⟧)
    (h : Disjoint r d) : (E.write d v).read r = E.read r := by
  cases r with
  | arg i hi => rfl
  | val i hi => exact Env.read_write_ne E d h

def Preserves (r : Reg Γ t) : Instr Γ → Prop
  | .gep d _ _ => Disjoint r d
  | .gepInbounds d _ _ => Disjoint r d
  | .const _ d => Disjoint r d
  | .poison d => Disjoint r d
  | .unop _ d _ => Disjoint r d
  | .binop _ d _ _ => Disjoint r d
  | .ternop _ d _ _ _ => Disjoint r d
  | .load d _ => Disjoint r d
  | .loadMonotonic d _ => Disjoint r d
  | .noaliasScopeDecl _ | .fenceSingleThread | .store _ _ |
      .lifetimeStart _ _ | .lifetimeEnd _ _ => True
  | _ => False

private theorem unchanged_success (r : Reg Γ t) (E F : Env Γ)
    (s u : GlobalState) (h : PoisonOr.value (E, s) = .value (F, u)) :
    F.read r = E.read r := by
  have he := (Prod.mk.inj (PoisonOr.value_inj.mp h)).1
  rw [he]

private theorem write_success (r : Reg Γ t) (E F : Env Γ)
    (d : Dst Γ u) (v : ⟦u⟧) (s z : GlobalState)
    (hd : Disjoint r d) (h : PoisonOr.value (E.write d v, s) = .value (F, z)) :
    F.read r = E.read r := by
  have he := (Prod.mk.inj (PoisonOr.value_inj.mp h)).1
  rw [← he]
  exact read_write E r d v hd

private theorem load_success (r : Reg Γ t) (E F : Env Γ) (d : Dst Γ u)
    (p : PoisonOr Pointer) (s z : GlobalState) (hd : Disjoint r d)
    (h : Operation.load d p E s = .value (F, z)) : F.read r = E.read r := by
  cases p with
  | poison => simp [Operation.load, EffectM.bind_eq, throwUB, StateT.lift, PoisonOr.poison_ne_value] at h
  | value p =>
    by_cases hp : Fits s.mem p u.width
    · have hs : PoisonOr.value (E.write d (u.unflatten (s.mem.readAt p u.width)), s) =
          .value (F, z) := by
        simpa [Operation.load, EffectM.bind_eq, EffectM.get_eq, throwUBIf, hp] using h
      exact write_success r E F d _ s z hd hs
    · simp [Operation.load, EffectM.bind_eq, EffectM.get_eq, throwUBIf, hp, throwUB, StateT.lift, PoisonOr.poison_ne_value] at h

private theorem store_success (r : Reg Γ t) (E F : Env Γ)
    (p : PoisonOr Pointer) (v : ⟦u⟧) (s z : GlobalState)
    (h : Operation.store p v E s = .value (F, z)) : F.read r = E.read r := by
  cases p with
  | poison => simp [Operation.store, EffectM.bind_eq, throwUB, StateT.lift, PoisonOr.poison_ne_value] at h
  | value p =>
    by_cases hp : Fits s.mem p u.width <;> cases hv : u.flatten v
    all_goals simp [Operation.store, EffectM.bind_eq, EffectM.get_eq,
      EffectM.set_eq, throwUBIf, throwUB, StateT.lift, PoisonOr.poison_ne_value, hp, hv] at h
    all_goals obtain ⟨hE, _⟩ := h
    all_goals subst F; rfl

theorem instruction (r : Reg Γ t) (i : Instr Γ) (hi : Preserves r i)
    (E F : Env Γ) (s z : GlobalState)
    (h : Instr.run E i s = .value (F, z)) : F.read r = E.read r := by
  cases i <;> try contradiction
  all_goals simp only [Instr.run, EffectM.bind_eq, EffectM.get_eq,
    EffectM.pure_eq, PoisonOr.value_bind] at h
  all_goals first
    | exact unchanged_success r E F _ z h
    | exact write_success r E F _ _ _ z hi h
    | exact load_success r E F _ _ s z hi h
    | exact store_success r E F _ _ s z h

theorem fold (r : Reg Γ t) (body : List (Instr Γ))
    (hi : ∀ i ∈ body, Preserves r i) (E F : Env Γ) (s z : GlobalState)
    (h : body.foldlM Instr.run E s = .value (F, z)) : F.read r = E.read r := by
  induction body generalizing E s with
  | nil => exact unchanged_success r E F s z h
  | cons i body ih =>
    simp only [List.foldlM_cons, EffectM.bind_eq] at h
    cases he : Instr.run E i s with
    | poison => simp [he, PoisonOr.poison_ne_value] at h
    | value es =>
      have hh : body.foldlM Instr.run es.1 es.2 = .value (F, z) := by simpa [he] using h
      exact (ih (fun j hj => hi j (by simp [hj])) es.1 es.2 hh).trans
        (instruction r i (hi i (by simp)) E es.1 s es.2 he)

/-- A syntactic write interval. Unsupported operations cannot acquire a
frame certificate through the default branch. -/
def WritesWithin (lo hi : Nat) : Instr Γ → Prop
  | .gep d _ _ => lo ≤ d.i.val ∧ d.i.val ≤ hi
  | .gepInbounds d _ _ => lo ≤ d.i.val ∧ d.i.val ≤ hi
  | .const _ d => lo ≤ d.i.val ∧ d.i.val ≤ hi
  | .poison d => lo ≤ d.i.val ∧ d.i.val ≤ hi
  | .unop _ d _ => lo ≤ d.i.val ∧ d.i.val ≤ hi
  | .binop _ d _ _ => lo ≤ d.i.val ∧ d.i.val ≤ hi
  | .ternop _ d _ _ _ => lo ≤ d.i.val ∧ d.i.val ≤ hi
  | .load d _ => lo ≤ d.i.val ∧ d.i.val ≤ hi
  | .loadMonotonic d _ => lo ≤ d.i.val ∧ d.i.val ≤ hi
  | .noaliasScopeDecl _ | .fenceSingleThread | .store _ _ |
      .lifetimeStart _ _ | .lifetimeEnd _ _ => True
  | _ => False

def Outside (lo hi : Nat) (r : Reg Γ t) : Prop :=
  match r with
  | .arg _ _ => True
  | .val i _ => i.val < lo ∨ hi < i.val

theorem preserves_of_outside (lo hi : Nat) (r : Reg Γ t) (i : Instr Γ)
    (hw : WritesWithin lo hi i) (hr : Outside lo hi r) : Preserves r i := by
  cases r with
  | arg j hj => cases i <;> simp_all [WritesWithin, Preserves, Disjoint]
  | val j hj =>
    cases i <;> simp_all only [WritesWithin, Preserves, Disjoint, Outside]
    all_goals intro he
    all_goals have := congrArg Fin.val he
    all_goals omega

theorem fold_of_outside (lo hi : Nat) (r : Reg Γ t) (body : List (Instr Γ))
    (hw : ∀ i ∈ body, WritesWithin lo hi i) (hr : Outside lo hi r)
    (E F : Env Γ) (s z : GlobalState)
    (h : body.foldlM Instr.run E s = .value (F, z)) : F.read r = E.read r :=
  fold r body (fun i hi' => preserves_of_outside lo hi r i (hw i hi') hr) E F s z h

end Agave.Ed25519.SmallOrder.Execution.EnvironmentFrame
