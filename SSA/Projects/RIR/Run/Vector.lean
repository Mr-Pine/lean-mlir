module

public import SSA.Projects.RIR.Semantics.Func

namespace LeanMLIR.RIR

public section

open Lean Meta in
dsimproc [mlir_operation]expandOfFn (Vector.ofFn _) := fun e => do
  let_expr Vector.ofFn n α f := e | return .continue
  let some k := (← instantiateMVars n).nat? | return .continue
  let mut elems := #[]
  for i in [0:k] do
    let lt ← mkAppM ``LT.lt #[mkNatLit i, n]
    let fi ← mkAppM ``Fin.mk #[mkNatLit i, ← mkDecideProof lt]
    let lane ←
      Meta.transform (f.beta #[fi]) (post := fun x => do
          let_expr GetElem.getElem _ _ _ _ _ xs j _ := x | return .continue -- (ofFn f)[j] -- xs[j]
          unless j == fi do
            return .continue
          let xsTy ← whnfR (← inferType xs)
          let_expr Vector β m := xsTy | return .continue
          let nat := mkConst ``Nat
          let valid ←
            withLocalDeclD `xs xsTy fun v =>
                withLocalDeclD `i nat fun j => do
                  mkLambdaFVars #[v, j] (← mkAppM ``LT.lt #[j, m])
          let inst ← synthInstance (← mkAppM ``GetElem #[xsTy, nat, β, valid])
          let pf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, m])
          return .done
              (← mkAppOptM ``GetElem.getElem #[xsTy, nat, β, valid, inst, xs, mkNatLit i, pf]))
    -- We rebuilt the single lane expression
    elems := elems.push lane
  let arr ← mkAppM ``List.toArray #[← mkListLit α elems.toList]
  return .visit (mkApp4 (mkConst ``Vector.mk [← getDecLevel α]) α n arr (← mkEqRefl n))

/-- `↑(k : Fin n)` of a literal: `simp` itself reduces it only for `k ≤ 2`. -/
@[simp, mlir_operation]
theorem Fin.val_ofNat_lit {n k : Nat} [NeZero n] :
    ((no_index (OfNat.ofNat k : Fin n)) : Nat) = k % n :=
  rfl

open Lean Meta in
/-- `xs[i]'_` for a vector `xs` and a literal `i`, the bound by `decide`. -/
meta def mkVecGetElem (xs : Expr) (i : Nat) : MetaM (Option Expr) := do
  let xsTy ← whnfR (← inferType xs)
  let_expr Vector β m := xsTy | return none
  let nat := mkConst ``Nat
  let valid ←
    withLocalDeclD `xs xsTy fun v =>
        withLocalDeclD `i nat fun j => do
          mkLambdaFVars #[v, j] (← mkAppM ``LT.lt #[j, m])
  let inst ← synthInstance (← mkAppM ``GetElem #[xsTy, nat, β, valid])
  let pf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, m])
  some <$> mkAppOptM ``GetElem.getElem #[xsTy, nat, β, valid, inst, xs, mkNatLit i, pf]

open Lean Meta in
/-- `shufflevector` with a literal mask, to its lanes: `a[k]`, `b[k - n]` or poison. Before the
unfolded `Vector.ofFn` is simplified with a symbolic lane, which cannot decide the mask. -/
dsimproc ↓[simp, mlir_operation]reduceShufflevector (Operation.shufflevector _ _ _) := fun e => do
  let_expr Operation.shufflevector l₁ l₂ _ mask a b := e | return .continue
  let some n ← (evalNat l₁).run | return .continue
  let some m ← (evalNat l₂).run | return .continue
  let_expr Vector.mk _ _ arr _ := ← whnfR mask | return .continue
  let_expr List.toArray _ lst := arr | return .continue
  let some (_, entries) := lst.listLit? | return .continue
  let_expr Vector β _ := ← whnfR (← inferType a) | return .continue
  let_expr PoisonOr α := β | return .continue
  let mut lanes := #[]
  for entry in entries do
    match_expr entry with
    | Option.some fin k =>
      let some j :=
        (← whnfD (mkApp2 (mkConst ``Fin.val) (fin.appArg!) k)).rawNatLit? <|>
          (← whnfD (mkApp2 (mkConst ``Fin.val) (fin.appArg!) k)).nat?
        | return .continue
      let some lane ←
        if j < n then
          mkVecGetElem a j
        else
          mkVecGetElem b (j - n) | return .continue
      lanes := lanes.push lane
    | Option.none _ =>
      lanes := lanes.push (mkApp (mkConst ``PoisonOr.poison) α)
    | _ =>
      return .continue
  let arr ← mkAppM ``List.toArray #[← mkListLit β lanes.toList]
  let nE := mkNatLit m
  return .visit (mkApp4 (mkConst ``Vector.mk [← getDecLevel β]) β nE arr (← mkEqRefl nE))

/-- `zipWith` as an `ofFn`, for `expandOfFn` to split into lanes. -/
@[mlir_operation]
theorem zipWith_eq_ofFn {f : α → β → γ} {as : Vector α n} {bs : Vector β n} :
    Vector.zipWith f as bs = Vector.ofFn fun i => f as[i] bs[i] := by
  ext; simp

/-- Rewrite under `Vector.mk arr h` proving the new size afresh: `simp` would cast `h` along the
rewrite, tying the vector to that rewrite's hypotheses. -/
@[congr]
theorem Vector.mk_congr {a a' : Array α} (e : a = a') (h : a.size = n)
    (h' : a'.size ≤ n ∧ n ≤ a'.size) :
    Vector.mk a h = Vector.mk a' (Nat.le_antisymm h'.1 h'.2) := by
  subst e; rfl

open Lean Meta in
/-- `Vector.map PoisonOr.value xs` unfolded, `⟨xs.toArray.map .value, _⟩`, back to `Ty.wrap xs`. -/
dsimproc [simp]rewrapMap (Vector.mk _ _) := fun e => do
  let_expr Vector.mk _ n arr _ := e | return .continue
  let_expr Array.map _ _ f a := arr | return .continue
  unless f.isAppOfArity ``PoisonOr.value 1 do
    return .continue
  let_expr Vector.toArray _ _ xs := a | return .continue
  let_expr BitVec w := f.appArg! | return .continue
  return .done (← mkAppOptM ``Ty.wrap #[mkApp2 (mkConst ``Ty.vec) n w, xs])

/-- Rewrite a vector under `xs[i]'h` keeping `h`: its type `i < n` does not mention `xs`, but `simp`
would cast it along the rewrite's proof. -/
@[congr]
theorem Vector.getElem_congr_coll' {xs ys : Vector α n} (hxs : xs = ys) (i : Nat) (h : i < n) :
    xs[i] = ys[i] := by
  subst hxs; rfl

theorem mk_map_toArray (l : List α) (f : α → β) (h : (l.map f).toArray.size = n)
    (h' : l.toArray.size = n) :
    Vector.mk (l.map f).toArray h = Vector.map f (Vector.mk l.toArray h') := by
  subst h'; apply Vector.toArray_inj.mp; simp only [Vector.toArray_map, List.map_toArray]

open Lean Meta in
/-- `#v[.value x₀, …, .value xₙ]` to `Ty.wrap #v[x₀, …, xₙ]`: the `PoisonOr` moves out of the lanes. -/
simproc pullWrap (Vector.mk _ _) := fun e => do
  let_expr Vector.mk α _ arr h := e | return .continue
  let_expr PoisonOr β := α | return .continue
  let_expr BitVec w := β | return .continue
  let_expr List.toArray _ l := arr | return .continue
  let some xs := l.listLit? | return .continue
  let some raw := xs.2.mapM (fun x => x.app2? ``PoisonOr.value |>.map (·.2)) | return .continue
  let l' ← mkListLit β raw
  let val := mkApp (mkConst ``PoisonOr.value) β
  -- `#v[…]` literals have size `#[…].size`; the lanes' count is the same, by `rfl`
  let n := mkNatLit raw.length
  let sizeRfl (l : Expr) := do
    return mkExpectedPropHint (← mkEqRefl n)
        (← mkEq (← mkAppM ``Array.size #[← mkAppM ``List.toArray #[l]]) n)
  let pf ←
    mkAppM ``mk_map_toArray #[l', val, ← sizeRfl (← mkAppM ``List.map #[val, l']), ← sizeRfl l']
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  let wrapped ← mkAppOptM ``Ty.wrap #[mkApp2 (mkConst ``Ty.vec) n w, rhs.appArg!]
  return .done { expr := wrapped, proof? := some (← mkExpectedTypeHint pf (← mkEq e wrapped)) }

open Lean Meta in
/-- `Vector.ofFn fun i => .value (g i)` to `Ty.wrap (Vector.ofFn g)`. -/
simproc [simp]pullWrapOfFn (Vector.ofFn _) := fun e => do
  let_expr Vector.ofFn n α f := e | return .continue
  let_expr PoisonOr β := α | return .continue
  let_expr BitVec w := β | return .continue
  let .lam x ty body bi := f | return .continue
  let_expr PoisonOr.value _ v := body | return .continue
  let g := Expr.lam x ty v bi
  let inner ← mkAppM ``Vector.ofFn #[g]
  -- `(ofFn g).map value = ofFn (value ∘ g)`
  let pf ← mkAppOptM ``Vector.map_ofFn #[none, none, none, g, mkApp (mkConst ``PoisonOr.value) β]
  let wrapped ← mkAppOptM ``Ty.wrap #[mkApp2 (mkConst ``Ty.vec) n w, inner]
  return .done
      { expr := wrapped, proof? := some (← mkExpectedTypeHint (← mkEqSymm pf) (← mkEq e wrapped)) }

open Lean Meta in
/-- `(Ty.wrap vs)[i]` to `.value vs[i]`. -/
simproc [simp]wrapGetElem (GetElem.getElem _ _ _) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ xs i h := e | return .continue
  let_expr Ty.wrap t vs := xs | return .continue
  -- `t` may be an abbreviation, like a program's `V` for `.vec 8 64`
  let_expr Ty.vec _ _ := ← whnfR t | return .continue
  let_expr Vector β _ := ← whnfR (← inferType vs) | return .continue
  let pf ←
    mkAppOptM ``Vector.getElem_map #[none, none, none, i, mkApp (mkConst ``PoisonOr.value) β, vs, h]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .done { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

end

end LeanMLIR.RIR
