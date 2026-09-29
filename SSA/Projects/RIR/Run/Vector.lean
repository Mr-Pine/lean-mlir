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

/-- `zipWith` as an `ofFn`, for `expandOfFn` to split into lanes. -/
@[mlir_operation]
theorem zipWith_eq_ofFn {f : α → β → γ} {as : Vector α n} {bs : Vector β n} :
    Vector.zipWith f as bs = Vector.ofFn fun i => f as[i] bs[i] := by
  ext; simp

open Lean Meta in
/-- `Vector.mk arr h` with `h` mentioning locals, to `Vector.mk arr rfl`: `simp` casts `h` along a
rewrite of `arr`, which ties the value to that rewrite's hypotheses. -/
dsimproc [simp]reproveVectorMk (Vector.mk _ _) := fun e => do
  let_expr Vector.mk α n arr h := e | return .continue
  unless h.hasFVar do
    return .continue
  -- only a literal's size is `n` by `rfl`
  let_expr List.toArray _ l := arr | return .continue
  unless l.listLit?.isSome do
    return .continue
  let ty ← mkEq (← mkAppM ``Array.size #[arr]) n
  return .visit (mkApp4 e.getAppFn α n arr (mkExpectedPropHint (← mkEqRefl n) ty))

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
  let_expr Ty.vec _ _ := t | return .continue
  let_expr Vector β _ := ← whnfR (← inferType vs) | return .continue
  let pf ←
    mkAppOptM ``Vector.getElem_map #[none, none, none, i, mkApp (mkConst ``PoisonOr.value) β, vs, h]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .done { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

end

end LeanMLIR.RIR
