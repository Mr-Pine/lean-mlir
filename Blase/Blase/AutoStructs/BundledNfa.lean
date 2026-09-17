import Blase.AutoStructs.ForMathlib
import Blase.FinEnum

structure NFA' (n : Nat) where
  σ : Type
  M : NFA (BitVec n) σ
  -- all reachable? complete? etc

namespace NFA'

/--
The encoded tuples of bit vectors accepted by an automaton.
-/
def accepts' (M : NFA' n) : Set (BitVecs' n) :=
  M.M.accepts

/--
The tuples of bit vectors accepted by an automaton.
-/
def accepts (M : NFA' n) : Set (BitVecs n) :=
  dec '' M.accepts'

@[implicit_reducible]
noncomputable def complete (M : NFA' n) : NFA' n where
  σ := _
  M := M.M.complete

@[implicit_reducible]
def product (final? : Prop → Prop → Prop) (M N : NFA' n) : NFA' n where
  σ := _
  M := M.M.product final? N.M

@[implicit_reducible]
def inter (M N : NFA' n) : NFA' n :=
  ⟨_, M.M.inter N.M⟩

lemma inter_eq (M N : NFA' n) : M.inter N = NFA'.product And M N := by
  simp [inter, product, NFA.inter]

@[simp]
lemma inter_accepts (M N : NFA' n) : (M.inter N).accepts = M.accepts ∩ N.accepts := by
  simp [accepts, accepts', inter]; exact Set.image_inter dec_inj

@[implicit_reducible]
def union (M N : NFA' n) : NFA' n :=
  ⟨_, M.M.union N.M⟩

lemma union_eq (M N : NFA' n) : M.union N = NFA'.product Or M.complete N.complete := by
  simp [union, product, NFA.union, NFA.union', complete]

@[simp]
lemma union_accepts (M N : NFA' n) : (M.union N).accepts = M.accepts ∪ N.accepts := by
  simp [accepts, accepts', union]; exact Set.image_union ..

@[implicit_reducible]
def flipAccept (M : NFA' n) : NFA' n where
  σ := _
  M := M.M.flipAccept

@[implicit_reducible]
def neg (M : NFA' n) : NFA' n where
  σ := _
  M := M.M.neg

@[simp]
lemma neg_accepts (M : NFA' n) : M.neg.accepts = M.acceptsᶜ := by
  simp [accepts, accepts', neg]; exact Set.image_compl_eq dec_bij

@[implicit_reducible]
def reduce (M : NFA' n) : NFA' n where
  σ := _
  M := M.M.reduce

@[simp]
lemma reduce_accepts {M : NFA' n} : M.reduce.accepts = M.accepts := by
  simp [reduce, accepts, accepts']

@[implicit_reducible]
def determinize (M : NFA' n) : NFA' n where
  σ := _
  M := M.M.toDFA.toNFA

lemma neg_eq {M : NFA' n} : M.neg = M.determinize.flipAccept := by rfl

@[implicit_reducible]
def reverse (M : NFA' n) : NFA' n where
  σ := _
  M := M.M.reverse

@[implicit_reducible]
def lift (f : Fin n → Fin m) (M : NFA' n) : NFA' m where
  σ := _
  M := M.M.lift f

@[implicit_reducible]
def proj (f : Fin m → Fin n) (M : NFA' n) : NFA' m where
  σ := _
  M := M.M.proj f

@[simp]
lemma lift_accepts (M : NFA' n) (f : Fin n → Fin m) :
    (M.lift f).accepts = BitVecs.transport f ⁻¹' M.accepts := by
  simp [accepts, accepts', lift]; exact dec_transport_preim

@[simp]
lemma proj_accepts (M : NFA' m) (f : Fin n → Fin m) :
    (M.proj f).accepts = BitVecs.transport f '' M.accepts := by
  simp [accepts, accepts', proj]; exact dec_transport_image f

end NFA'

class DecidableNFA' (M : NFA' α) [Fintype M.σ] [DecidableEq M.σ] [DecidableNFA M.M]
