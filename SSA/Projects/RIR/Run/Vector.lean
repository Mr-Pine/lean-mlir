module

public import SSA.Projects.RIR.Semantics.Func

namespace LeanMLIR.RIR

public section

open Lean Meta in
/-- `Vector.ofFn f` of a literal length as its lanes `#v[f 0, …]`, each lane's `xs[↑i]` as
`xs[k]`; definitionally equal. -/
meta def ofFnLanes? (e : Expr) : MetaM (Option Expr) := do
  let_expr Vector.ofFn n α f := e | return none
  let some k := (← instantiateMVars n).nat? | return none
  let mut elems := #[]
  for i in [0:k] do
    let lt ← mkAppM ``LT.lt #[mkNatLit i, n]
    let fi ← mkAppM ``Fin.mk #[mkNatLit i, ← mkDecideProof lt]
    let lane ←
      Meta.transform (f.beta #[fi]) (post := fun x => do
          -- `↑fi` as the literal
          if let some j := x.app2? ``Fin.val |>.map (·.2) then
            return if j == fi then .done (mkNatLit i) else .continue
          let_expr GetElem.getElem _ _ _ _ _ xs j _ := x | return .continue -- (ofFn f)[j] -- xs[j]
          unless j == fi || j == mkNatLit i do
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
  return some (mkApp4 (mkConst ``Vector.mk [← getDecLevel α]) α n arr (← mkEqRefl n))

open Lean Meta in
dsimproc [mlir_operation]expandOfFn (Vector.ofFn _) := fun e => do
  let some lanes ← ofFnLanes? e | return .continue
  return .visit lanes

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
/-- The type, size, list and elements of a literal `#v[…]`. -/
meta def vecLit? (xs : Expr) : Option (Expr × Expr × Expr × Expr × Array Expr) := do
  let_expr Vector.mk α n arr h := xs | none
  let_expr List.toArray _ l := arr | none
  let (_, elems) ← l.listLit?
  return (α, n, l, h, elems.toArray)

/-- A literal vector's lane, by `l[k]? = some a`: its `rfl` evaluates the list, not the lanes. -/
theorem Vector.getElem_mk_of_getElem? {α : Type u} {n : Nat} (l : List α) (h : l.toArray.size = n)
    (k : Nat) (hk : k < n) (a : α) (hl : l[k]? = some a) : (Vector.mk l.toArray h)[k] = a := by
  have hk' : k < l.length := by simpa [← h] using hk
  rw [List.getElem?_eq_getElem hk', Option.some.injEq] at hl
  simpa using hl

open Lean Meta in
/-- The value of a literal index: `k`, `↑⟨k, _⟩`, `⟨k, _⟩` or `(k : Fin n)`. -/
meta def litIndex? (i : Expr) : MetaM (Option Nat) := do
  let i ← instantiateMVars i
  let i :=
    match_expr i with
    | Fin.val _ j => j
    | _ => i
  match_expr i with
  | Fin.mk _ k _ =>
    (evalNat k).run
  | OfNat.ofNat ty k _ =>
    match_expr ← whnfR ty with
    | Fin n =>
      let some n ← (evalNat n).run | return none
      let some k ← (evalNat k).run | return none
      return if n = 0 then none else some (k % n)
    | Nat =>
      (evalNat k).run
    | _ =>
      return none
  | _ =>
    if (← whnfR (← inferType i)).isConstOf ``Nat then
      (evalNat i).run
    else
      return none

open Lean Meta in
/-- A lane at a literal index: of a literal vector, that lane; of another vector at `⟨k, _⟩`,
`↑⟨k, _⟩` or `(k : Fin n)`, `xs[k]`, as specs write it. A literal's lane is a proof step: as a `dsimp`
step the kernel checks the read together with the `dsimp` steps after it, which in a module it may
not unfold (`#v[0#8, x][0] ++ 0#8` to `0#16` needs `Nat.lor`); by `rfl` it may unfold the lanes. -/
simproc ↓[mlir_operation]reduceGetElemLit (GetElem.getElem _ _ _) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ xs i _ := e | return .continue
  let i ← instantiateMVars i
  if let some (α, n, l, h, elems) := vecLit? xs then
    let some k ← litIndex? i | return .continue
    let some lane := elems[k]? | return .continue
    if (← (evalNat n).run).isNone then
      return .continue
    let kE := mkNatLit k
    let some u := (← inferType α).sortLevel!.dec | return .continue
    let get? ← mkAppM ``GetElem?.getElem? #[l, kE]
    let some' := mkApp2 (mkConst ``Option.some [u]) α lane
    let hl ← mkExpectedTypeHint (← mkEqRefl some') (← mkEq get? some')
    let pf :=
      mkAppN (mkConst ``Vector.getElem_mk_of_getElem? [u])
        #[α, n, l, h, kE, ← mkDecideProof (← mkAppM ``LT.lt #[kE, n]), lane, hl]
    return .visit { expr := lane, proof? := ← mkExpectedTypeHint pf (← mkEq e lane) }
  let finIndex :=
    i.isAppOf ``Fin.val || i.isAppOf ``Fin.mk ||
      i.isAppOfArity ``OfNat.ofNat 3 && i.appFn!.appFn!.appArg!.isAppOf ``Fin
  unless finIndex do
    return .continue
  let some k ← litIndex? i | return .continue
  let some lane ← mkVecGetElem xs k | return .continue
  return .visit { expr := lane, proof? := ← mkExpectedTypeHint (← mkEqRefl lane) (← mkEq e lane) }

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

open Lean Meta in
/-- `xs.set k x` for a literal vector `xs` (or `Vector.replicate n a`, `n` a literal) and a literal
`k`, to the literal: an `insertelement` chain to the vector it builds. -/
dsimproc [mlir_operation]reduceVectorSet (Vector.set _ _ _ _) := fun e => do
  let_expr Vector.set α n xs i x _ := e | return .continue
  let some k := (← instantiateMVars i).nat? <|> (← instantiateMVars i).rawNatLit? | return .continue
  let lanes? : Option (List Expr) ←
    match_expr xs with
    | Vector.mk _ _ arr _ =>
      pure <|
          match_expr arr with
          | List.toArray _ l => l.listLit?.map (·.2)
          | _ => none
    | Vector.replicate _ m a =>
      pure <| (m.nat? <|> m.rawNatLit?).map (List.replicate · a)
    | _ =>
      pure none
  let some lanes := lanes? | return .continue
  unless k < lanes.length do
    return .continue
  let arr ← mkAppM ``List.toArray #[← mkListLit α (lanes.set k x)]
  return .visit (mkApp4 (mkConst ``Vector.mk [← getDecLevel α]) α n arr (← mkEqRefl n))

/-! ### `bitcast` between vectors, lane by lane -/

open Lean in
/-- Whether `e` still reads the env: a lane-wise simproc waits for the reads to resolve once. -/
meta def hasEnvRead (e : Expr) : Bool :=
  (e.find? (·.isAppOf ``Env.read)).isSome

/-- `bitcastPoison` tests only the lanes `ks` overlapping lane `j`. -/
theorem Operation.bitcastPoison_eq {x : Vector (PoisonOr α) l} {w w' j : Nat} (ks : List (Fin l))
    (hks :
      ∀ i (h : i < l),
        (decide (i * w < (j + 1) * w') && decide (j * w' < (i + 1) * w)) =
          decide ((⟨i, h⟩ : Fin l) ∈ ks)) :
    Operation.bitcastPoison x w w' j = ks.any fun i => x[i].isPoison := by
  unfold Operation.bitcastPoison
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨hp, h1⟩, h2⟩
    have := hks i.1 i.2
    simp only [h1, h2, decide_true, Bool.and_self, Fin.eta] at this
    exact ⟨i, of_decide_eq_true this.symm, hp⟩
  · rintro ⟨i, hi, hp⟩
    have := hks i.1 i.2
    simp only [Fin.eta, hi, decide_true, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨i, ⟨hp, this.1⟩, this.2⟩

open Lean Meta in
/-- `bitcastPoison x w w' j` for literal sizes and `j`: the test of the lanes overlapping lane `j`,
`x[k].isPoison || …`. Unfolded, it is an `∃ i : Fin l` that `simp` cannot decide. -/
simproc [mlir_operation]reduceBitcastPoison (Operation.bitcastPoison _ _ _ _) := fun e => do
  let_expr Operation.bitcastPoison α lE x wE w'E jE := e | return .continue
  let some l ← (evalNat lE).run | return .continue
  let some w ← (evalNat wE).run | return .continue
  let some w' ← (evalNat w'E).run | return .continue
  let some j ← litIndex? jE | return .continue
  -- once `x`'s reads are resolved: else each lane's reads resolve on their own
  if hasEnvRead x then
    return .continue
  let ks := (List.range l).filter fun i => i * w < (j + 1) * w' && j * w' < (i + 1) * w
  let finTy := mkApp (mkConst ``Fin) lE
  let ksE ←
    mkListLit finTy
        (←
          ks.mapM fun i => do
              return mkApp3 (mkConst ``Fin.mk) lE (mkNatLit i)
                  (← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, lE])))
  let lem := mkAppN (mkConst ``Operation.bitcastPoison_eq) #[α, lE, x, wE, w'E, mkNatLit j, ksE]
  let hks ← mkDecideProof (← inferType lem).bindingDomain!
  let pf := mkApp lem hks
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit { expr := rhs, proof? := ← mkExpectedTypeHint pf (← mkEq e rhs) }

open Lean Meta in
/-- A `bitcast` between vectors of literal sizes, to its lanes `poisonIf (bitcastPoison x w w' k)
(.value (bits.extractLsb' (k * w') w'))`: before the unfolded `Vector.ofFn` is simplified with a
symbolic lane, which cannot decide the poison tests. -/
simproc ↓[mlir_operation]reduceBitcast (Operation.bitcast _ _) := fun e => do
  let_expr Operation.bitcast t t' _ x := e | return .continue
  let_expr Ty.vec lE wE := ← whnfD t | return .continue
  let_expr Ty.vec l'E w'E := ← whnfD t' | return .continue
  let some l' ← (evalNat l'E).run | return .continue
  let some w' ← (evalNat w'E).run | return .continue
  -- built directly: `mkAppM` would unify `x`'s type, `⟦t⟧`, with a `Vector` at every use
  let bv := mkApp (mkConst ``BitVec) wE
  let bv' := mkApp (mkConst ``BitVec) w'E
  let laneTy := mkApp (mkConst ``PoisonOr) bv'
  let getValue :=
    mkApp2 (mkConst ``PoisonOr.getValue) bv (← synthInstance (mkApp (mkConst ``Inhabited [1]) bv))
  let bits :=
    mkApp3 (mkConst ``BitVec.packLanes) wE lE
      (mkAppN (mkConst ``Vector.map [0, 0]) #[mkApp (mkConst ``PoisonOr) bv, bv, lE, getValue, x])
  let lanes :=
    (List.range l').map fun k =>
      let test := mkAppN (mkConst ``Operation.bitcastPoison) #[bv, lE, x, wE, w'E, mkNatLit k]
      let value :=
        mkApp2 (mkConst ``PoisonOr.value) bv'
          (mkApp4 (mkConst ``BitVec.extractLsb') (mkNatMul wE lE) (mkNatLit (k * w')) w'E bits)
      mkApp3 (mkConst ``Operation.poisonIf) bv' test value
  let arr ← mkAppM ``List.toArray #[← mkListLit laneTy lanes]
  let r := mkApp4 (mkConst ``Vector.mk [← getDecLevel laneTy]) laneTy l'E arr (← mkEqRefl l'E)
  return .visit { expr := r, proof? := ← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r) }

/-- No lane of values is poison. -/
@[mlir_operation]
theorem Operation.bitcastPoison_map_value (v : Vector α l) :
    Operation.bitcastPoison (v.map PoisonOr.value) w w' j = false := by
  simp [Operation.bitcastPoison]

@[mlir_operation]
theorem Operation.bitcastPoison_wrap (v : Vector (BitVec w₀) l) :
    Operation.bitcastPoison (Ty.wrap (t := .vec l w₀) v) w w' j = false := by
  rw [Ty.wrap_vec, Operation.bitcastPoison_map_value]

/-- Values read back: `bitcast`'s bits. -/
@[mlir_operation]
theorem map_getValue_map_value [Inhabited α] (v : Vector α n) :
    (v.map PoisonOr.value).map PoisonOr.getValue = v := by
  ext i hi
  simp

@[mlir_operation]
theorem map_getValue_wrap (v : Vector (BitVec w) n) :
    (Ty.wrap (t := .vec n w) v).map PoisonOr.getValue = v := by
  rw [Ty.wrap_vec, map_getValue_map_value]

/-- A slice of `x` as its upper and lower slices. -/
theorem BitVec.extractLsb'_add (x : BitVec n) (s a b : Nat) :
    x.extractLsb' s (a + b) = x.extractLsb' (s + b) a ++ x.extractLsb' s b :=
  (BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl).symm

open Lean Meta in
/-- `(packLanes v).extractLsb' s w` for literal `s` and `w` within the `we`-bit lanes `v`: lane
`v[s / we]` (or its slice), or for whole lanes `k + m - 1 … k`, `v[k + m - 1] ++ … ++ v[k]`. -/
meta def extractPackLanes : Simp.Simproc := fun e => do
  let_expr BitVec.extractLsb' _ sE lenE x := e | return .continue
  let_expr BitVec.packLanes weE kE v := x | return .continue
  let some we ← (evalNat weE).run | return .continue
  let some k ← (evalNat kE).run | return .continue
  let some s ← litIndex? sE | return .continue
  let some len ← litIndex? lenE | return .continue
  if we = 0 || len = 0 || hasEnvRead v then
    return .continue
  let extract (s len : Nat) : MetaM Expr :=
    mkAppM ``BitVec.extractLsb' #[mkNatLit s, mkNatLit len, x]
  -- `(packLanes v).extractLsb' (i * we) we = v[i]`
  let lane (i : Nat) : MetaM (Option (Expr × Expr)) := do
    let some r ← mkVecGetElem v i | return none
    let pf ←
      mkAppM ``BitVec.extractLsb'_packLanes
          #[v, mkNatLit i, ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, kE])]
    return some (r, ← mkExpectedTypeHint pf (← mkEq (← extract (i * we) we) r))
  let i := s / we
  let off := s % we
  if i < k && off + len ≤ we then
    if off = 0 && len = we then
      let some (r, pf) ← lane i | return .continue
      return .visit { expr := r, proof? := pf }
    let some vi ← mkVecGetElem v i | return .continue
    let r ← mkAppM ``BitVec.extractLsb' #[mkNatLit off, lenE, vi]
    let pf ←
      mkAppM ``BitVec.extractLsb'_packLanes_of_lt
          #[v, ← mkDecideProof (← mkAppM ``LT.lt #[← mkAppM ``HDiv.hDiv #[sE, weE], kE]),
            ←
              mkDecideProof
                  (←
                    mkAppM ``LE.le
                        #[← mkAppM ``HAdd.hAdd #[← mkAppM ``HMod.hMod #[sE, weE], lenE], weE])]
    return .visit { expr := r, proof? := ← mkExpectedTypeHint pf (← mkEq e r) }
  -- whole lanes `i … i + m - 1`: from the top lane down, each `x.extractLsb' (t * we) (a + we)`
  -- split into the lanes above and lane `t`
  let m := len / we
  unless off = 0 && len % we = 0 && i + m ≤ k do
    return .continue
  let some (r₀, pf₀) ← lane (i + m - 1) | return .continue
  let mut r := r₀
  let mut pf := pf₀
  for d in [1:m] do
    let t := i + m - 1 - d
    let some (lo, pfLo) ← lane t | return .continue
    let split ← mkAppM ``BitVec.extractLsb'_add #[x, mkNatLit (t * we), mkNatLit (d * we), weE]
    let some (_, _, mid) := (← inferType split).eq? | return .continue
    let app := mid.appFn!.appFn!
    let pf' ← mkEqTrans split (← mkCongr (← mkCongrArg app pf) pfLo)
    r := mkApp2 app r lo
    pf ← mkExpectedTypeHint pf' (← mkEq (← extract (t * we) ((d + 1) * we)) r)
  return .visit { expr := r, proof? := ← mkExpectedTypeHint pf (← mkEq e r) }

/-- `extractPackLanes`, before `extractLsb'_eq_self` takes all of `packLanes v`. -/
simproc ↓[mlir_operation]reduceExtractPackLanes (BitVec.extractLsb' _ _ _) := extractPackLanes

/-- `extractPackLanes`, once `v`'s reads are resolved. -/
simproc [mlir_operation]reduceExtractPackLanes' (BitVec.extractLsb' _ _ _) := extractPackLanes

attribute [mlir_operation] List.any_cons List.any_nil Bool.or_false Bool.false_or
  PoisonOr.isPoison_value PoisonOr.isPoison_poison PoisonOr.getValue_value

/-- `zipWith` as an `ofFn`, for `expandOfFn` to split into lanes. -/
@[mlir_operation]
theorem zipWith_eq_ofFn {f : α → β → γ} {as : Vector α n} {bs : Vector β n} :
    Vector.zipWith f as bs = Vector.ofFn fun i => f as[i] bs[i] := by
  ext; simp

open Lean Meta in
/-- A vector operation's `zipWith` as its lanes `#v[f as[0] bs[0], …]`, as `expandOfFn` splits an
`ofFn`: pass it with the lanes' facts (an `add nsw`'s no-overflow) where `zipWith_eq_ofFn` is off. -/
simproc_decl expandZipWith (Vector.zipWith _ _ _) := fun e => do
  let lem ← mkConstWithFreshMVarLevels ``zipWith_eq_ofFn
  let (ms, _, ty) ← forallMetaTelescopeReducing (← inferType lem)
  let some (_, lhs, rhs) := ty.eq? | return .continue
  unless ← isDefEq lhs e do
    return .continue
  let pf ← instantiateMVars (mkAppN lem ms)
  let rhs ← instantiateMVars rhs
  let some lanes ← ofFnLanes? rhs | return .continue
  return .visit { expr := lanes, proof? := mkExpectedPropHint pf (← mkEq e lanes) }

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
  let_expr Vector.mk α _ arr _ := e | return .continue
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
