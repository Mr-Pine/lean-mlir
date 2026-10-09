module

public import MLIR.Context

/-!
# Type tries

A `TyTree` holds a list of types for lookups in logarithmic depth: `mlir_def` proves each value
register's type `Γ.ty k = t` by `rfl` on `get`, not by walking `Γ.vals`.
-/

namespace MLIR

@[expose] public section

/-- A binary trie of types. -/
inductive TyTree
  | leaf (t : Ty)
  | node (l r : TyTree)
  deriving DecidableEq

namespace TyTree

/-- Entry `i`: bit 0 of `i` picks the subtree, `i / 2` indexes into it. -/
def get : TyTree → Nat → Ty
  | leaf t, _ => t
  | node l r, i => if i % 2 = 0 then l.get (i / 2) else r.get (i / 2)

/-- The entries at even positions. -/
def evens : List Ty → List Ty
  | [] => []
  | [a] => [a]
  | a :: _ :: l => a :: evens l

/-- The depth-`d` trie of `l`'s first `2 ^ d` entries. -/
def ofList : Nat → List Ty → TyTree
  | 0, l => leaf (l.headD (.bv 0))
  | d + 1, l => node (ofList d (evens l)) (ofList d (evens l.tail))

theorem getElem?_evens (l : List Ty) (j : Nat) : (evens l)[j]? = l[2 * j]? := by
  induction l using evens.induct generalizing j with
  | case1 => simp [evens]
  | case2 a => cases j <;> simp [evens]
  | case3 a b l ih =>
    cases j with
    | zero => simp [evens]
    | succ j => simp [evens, ih, Nat.mul_succ]

theorem get_ofList (d : Nat) (l : List Ty) (i : Nat) (hi : i < 2 ^ d) :
    (ofList d l).get i = l.getD i (.bv 0) := by
  induction d generalizing l i with
  | zero =>
    obtain rfl : i = 0 := by simpa using hi
    cases l <;> simp [ofList, get]
  | succ d
    ih =>
    have hi' : i / 2 < 2 ^ d := by
      rw [Nat.pow_succ] at hi; omega
    simp only [ofList, get]
    split
    · rw [ih _ _ hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_evens]
      congr 2
      omega
    · rw [ih _ _ hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_evens]
      cases l with
      | nil => simp
      | cons a l =>
        simp only [List.tail_cons]
        rw [show i = 2 * (i / 2) + 1 by omega, List.getElem?_cons_succ]
        congr 3
        omega

end TyTree

/-- `Γ.ty k` is entry `k` of a trie of `Γ.vals`. -/
theorem Ctx.ty_eq_get {Γ : Ctx} {t : TyTree} {d : Nat} (ht : t = .ofList d Γ.vals)
    (hn : Γ.n ≤ 2 ^ d) (k : Fin Γ.n) : Γ.ty k = t.get k := by
  have hk : k.1 < Γ.vals.length := Nat.lt_of_lt_of_eq k.2 Γ.hn.symm
  subst ht
  rw [TyTree.get_ofList _ _ _ (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

end

end MLIR
