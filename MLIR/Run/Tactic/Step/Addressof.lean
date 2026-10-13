module

public meta import MLIR.Run.Tactic.Step.Pure
public meta import MLIR.Semantics.GlobalInitializer
public import MLIR.Run.Memory

namespace MLIR

open Lean Elab Tactic Meta

public meta section

/-- `step_pure` for an `addressof` of a global `@g`: its block's start `x`, from the fact
`hg : S.mem.Globals G` (`G` listing `⟨"g", t⟩`) and `S.WF`; the state unchanged. Facts: `hglobal_x`
(its table entry), `hx_off`; a constant's `hx_live` (its bytes), `hx_fits` (its defined bits, each
run from a byte), `hread_x` (its bits, as `Ty.flatBits` for a plain value, else a literal),
`hdefined_x`, and `hq_ne_x` for each pointer `q` known writable; a mutable one's `hx_bounds` and
`hwritable_x`. The term, a `value_eq` lemma `∀ s, t.value s = .value (v, s)` or `t`, is optional:
else `t`'s value is read off its block. -/
syntax (name := stepAddressof) "step_addressof" (ppSpace colGt term:max)? (stepNames)?
  (stepConsuming)? : tactic

/-- The value `g`'s initializer computes, read off its block (each register its instruction's
`compute` of the registers it reads), with `∀ s, g.value s = .value (x, s)` for the kernel to check
by running the block: the instructions are not evaluated. -/
def globalValue (g : Expr) : MetaM (Expr × Expr) := do
  let some c := g.getAppFn.constName? | throwError "`step_addressof`: {g} is not a global"
  let some entry := (← getEnv).find? (c ++ `entry) |>.bind (·.value?)
    | throwError "`step_addressof`: no initializer block `{c ++ `entry}`"
  -- a long block's instructions are shared by `have`s
  let entry ← zetaReduce entry
  let_expr BasicBlock.mk _ _ _ _ body exit := entry
    | throwError "`step_addressof`: {c ++ `entry} is no block literal"
  let index (i : Expr) : MetaM Nat := do
    let some k ← Tactic.kernelNat? (mkApp2 (mkConst ``Fin.val) (← inferType i).appArg! i)
      | throwError "`step_addressof`: register {i} is no literal"
    return k
  let regIndex (r : Expr) : MetaM Nat := do
    let_expr Reg.val _ _ i _ := r | throwError "`step_addressof`: {r} is no value register"
    index i
  let dstIndex (d : Expr) : MetaM Nat := do
    let_expr Dst.mk _ _ i _ := d | throwError "`step_addressof`: {d} is no register"
    index i
  let mut vals : Std.HashMap Nat Expr := {}
  let mut instrs := body
  while instrs.isAppOfArity ``List.cons 3 do
    let i := instrs.getArg! 1
    instrs := instrs.getArg! 2
    let read (r : Expr) : MetaM Expr := do
      let some v := vals[← regIndex r]? | throwError "`step_addressof`: {r} read before written"
      return v
    match_expr i with
    | Instr.const _ τ v d => vals := vals.insert (← dstIndex d) (← mkAppOptM ``Ty.wrap #[τ, v])
    | Instr.poison _ τ d => vals := vals.insert (← dstIndex d) (mkApp (mkConst ``Ty.poisoned) τ)
    | Instr.unop _ t₁ t op d a =>
      vals := vals.insert (← dstIndex d) (mkApp4 (mkConst ``UnOp.compute) t₁ t op (← read a))
    | Instr.binop _ t₁ t₂ t op d a b =>
      vals :=
        vals.insert (← dstIndex d)
          (mkApp6 (mkConst ``BinOp.compute) t₁ t₂ t op (← read a) (← read b))
    | _ => throwError "`step_addressof`: an initializer instruction{indentExpr i}"
  let_expr Exit.ret _ _ _ _ rs := exit | throwError "`step_addressof`: the initializer's exit"
  let_expr Regs.cons _ _ _ r _ := rs | throwError "`step_addressof`: the initializer's exit"
  let some x := vals[← regIndex r]? | throwError "`step_addressof`: the returned register"
  let hv ←
    withLocalDeclD `s (mkConst ``GlobalState) fun s => do
      let lhs ← mkAppM ``GlobalInitializer.value #[g, s]
      let rhs ← mkAppM ``PoisonOr.value #[← mkAppM ``Prod.mk #[x, s]]
      mkLambdaFVars #[s] (← Tactic.kernelRfl lhs rhs)
  return (x, hv)

/-- A string literal's string. -/
def strLit? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

/-- The entry `⟨sym, t⟩` of the globals list `G` and a proof of `⟨sym, t⟩ ∈ G`, through its
appends, conses and `Func.globals` projections. -/
partial def findGlobal? (G : Expr) (sym : String) : MetaM (Option (Expr × Expr)) := do
  let G' ← whnfR G
  match_expr G' with
  | List.cons _ a l =>
    if let some s := strLit? (← whnfR (← mkAppM ``Global.sym #[a])) then
      if s == sym then
        return some (a, ← mkAppOptM ``List.mem_cons_self #[none, a, l])
    let some (e, h) ← findGlobal? l sym | return none
    return some (e, ← mkAppM ``List.mem_cons_of_mem #[a, h])
  | HAppend.hAppend _ _ _ _ l₁ l₂ =>
    if let some (e, h)← findGlobal? l₁ sym then
      return some (e, ← mkAppM ``List.mem_append_left #[l₂, h])
    let some (e, h) ← findGlobal? l₂ sym | return none
    return some (e, ← mkAppM ``List.mem_append_right #[l₁, h])
  | List.append _ l₁ l₂ =>
    if let some (e, h)← findGlobal? l₁ sym then
      return some (e, ← mkAppM ``List.mem_append_left #[l₂, h])
    let some (e, h) ← findGlobal? l₂ sym | return none
    return some (e, ← mkAppM ``List.mem_append_right #[l₁, h])
  | _ =>
    if G' == G then
      return none
    findGlobal? G' sym

/-- A globals list entry's initializer as the list spells it (`half`, not its unfolding). -/
def entryInit (entry : Expr) : MetaM Expr :=
  if entry.isAppOfArity ``Global.mk 2 then pure entry.appArg! else mkAppM ``Global.init #[entry]

/-- The runs of set bits in the `n`-bit `d`, each from a byte boundary: `(start bit, length)`. -/
def definedRuns (d n : Nat) : Array (Nat × Nat) :=
  Id.run do
    let mut runs := #[]
    let mut a := 0
    while a < n do
      if d.testBit a && a % 8 == 0 then
        let mut b := a
        while b < n && d.testBit b do
          b := b + 1
        runs := runs.push (a, b - a)
        a := b
      else
        a := a + 1
    return runs

/-- The global facts about `x` (`hx : x = ⟨b, 0⟩`) in `S`, its table entry `hglobal` from the
globals list's `entry`: see `step_addressof`. -/
def addGlobalFacts (g : MVarId) (S x hx hglobal entry : Expr) (hv? : Option Expr) : MetaM MVarId :=
  g.withContext do
    let xName ← x.fvarId!.getUserName
    let name (s : String) : Name := .mkSimple (s.replace "x" xName.toString)
    let mem ← mkAppM ``GlobalState.mem #[S]
    let wfTy ← mkAppM ``GlobalState.WF #[S]
    let some hwf ←
      withReducible
          (findLocalDeclWithType? wfTy) | throwError "`step_addressof`: no hypothesis `{wfTy}`"
    let hwf := mkFVar hwf
    let some (_, _, P) := (← inferType hx).consumeMData.eq? | throwError "`step_addressof`: {hx}"
    -- facts about `P`, stated about `x` along `hx`
    let toX (pf : Expr) : MetaM Expr := do
      let ty ← inferType pf
      let motive ← Tactic.motiveOver ty P (mkConst ``Pointer)
      mkEqNDRec motive pf (← mkEqSymm hx)
    let tt ← entryInit entry
    let gt ← whnfR (← mkAppM ``GlobalInitializer.t #[tt])
    let gt ← reduce gt
    let some w ←
      Tactic.kernelNat?
          (mkApp (mkConst ``Ty.width)
            gt) | throwError "`step_addressof`: the width of{indentExpr gt}\nis not a literal"
    let n := (w + 7) / 8
    let (wE, nE) := (mkNatLit w, mkNatLit n)
    let img ← mkAppM ``GlobalInitializer.image #[tt]
    let hn ←
      mkEqTrans (← mkAppOptM ``GlobalInitializer.image_bytes #[tt])
          (←
            Tactic.kernelRfl
                (←
                  mkAppM ``HDiv.hDiv
                      #[← mkAppM ``HAdd.hAdd #[mkApp (mkConst ``Ty.width) gt, mkNatLit 7],
                        mkNatLit 8])
                nE)
    let hn := mkExpectedPropHint hn (← mkEq (← mkAppM ``GlobalImage.bytes #[img]) nE)
    let constant? ← Tactic.kernelWhnf (← mkAppM ``GlobalInitializer.constant #[tt])
    let constant := constant?.isConstOf ``Bool.true
    let hc ←
      mkEqTrans (← mkAppOptM ``GlobalInitializer.image_constant #[tt])
          (← Tactic.kernelRfl (← mkAppM ``GlobalInitializer.constant #[tt]) (toExpr constant))
    let mut hyps : Array Hypothesis := #[]
    let bv := P.appFn!.appArg!
    -- a fact about the block's start, as `P` spells it, its widths `8 * n` as literals, then
    -- about `x`
    let add (hyps : Array Hypothesis) (n : Name) (pf : Expr) : MetaM (Array Hypothesis) := do
      let ty ← instantiateMVars (← inferType pf)
      let ty :=
        ty.replace fun e =>
          if e.isAppOfArity ``Pointer.mk 2 && e.appFn!.appArg! == bv then some P
          else
            if e.isAppOfArity ``HMul.hMul 6 then
              match (e.getArg! 4).nat?, (e.getArg! 5).nat? with
              | some a, some b => some (mkNatLit (a * b))
              | _, _ => none
            else none
      let pf ← toX (mkExpectedPropHint pf ty)
      return hyps.push { userName := n, type := ← inferType pf, value := pf }
    -- the entry's block as `P`'s
    let some (_, l, _) := (← inferType hglobal).eq? | throwError "`step_addressof`: entry"
    let hglobalP :=
      mkExpectedPropHint hglobal
        (← mkEq l (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[← mkAppM ``Pointer.id #[P], img]]))
    hyps ← add hyps (name "hglobal_x") hglobalP
    hyps ←
      add hyps (name "hx_off")
          (mkExpectedPropHint (← mkEqRefl P.appArg!)
            (← mkEq (← mkAppM ``Pointer.offset #[P]) P.appArg!))
    if !constant then
      hyps ←
        add hyps (name "hx_bounds")
            (← mkAppM ``GlobalState.WF.mutable_inBounds #[hwf, hglobal, hc, hn])
      hyps ←
        add hyps (name "hwritable_x")
            (← mkAppM ``GlobalState.WF.mutable_writable #[hwf, hglobal, hc])
      let (_, g) ← g.assertHypotheses hyps
      return g
    let hblk ← mkAppM ``GlobalState.WF.const_block #[hwf, hglobal, hc]
    let hlive ← mkAppM ``GlobalImage.live #[hblk, hn]
    hyps ← add hyps (name "hx_live") hlive
    -- the value and its bits
    let (v, hv) ←
      match hv? with
      | some hv =>
        do
          let ty ← inferType hv
          let some v ←
            forallTelescope ty fun _ body => do
                let some (_, _, rhs) := body.eq? | return none
                return some rhs.appArg!.appFn!.appArg!
            | throwError "`step_addressof`: {hv} is not `∀ s, g.value s = .value (x, s)`"
          pure (v, hv)
      | none =>
        globalValue tt
    let hw ← Tactic.kernelRfl (mkApp (mkConst ``Ty.width) gt) wE
    let hw :=
      mkExpectedPropHint hw
        (← mkEq (mkApp (mkConst ``Ty.width) (← mkAppM ``GlobalInitializer.t #[tt])) wE)
    -- `f a = f b` from a pair equation `h : a = b`, `f` a projection, reduced on a literal pair `b`
    -- (unifying the unreduced one evaluates a wide `BitVec.ofNat`)
    let proj (f : Name) (h : Expr) : MetaM Expr := do
      let some (ty, l, r) := (← inferType h).eq? | throwError "`step_addressof`: {h}"
      let fn ←
        withLocalDeclD `q ty fun q => do
            mkLambdaFVars #[q] (← mkAppM f #[q])
      let r ←
        if r.isAppOfArity ``Prod.mk 4 then
          pure (r.getArg! (if f == ``Prod.fst then 2 else 3))
        else
          mkAppM f #[r]
      return mkExpectedPropHint (← mkCongrArg fn h) (← mkEq (← mkAppM f #[l]) r)
    let isFalse (p : Expr) : MetaM (Option Expr) := do
      Tactic.kernelDecide? (← mkEq p (mkConst ``Bool.false))
    -- a plain value of a type without pointers and padding: its raw bits, all defined
    let plain? ←
      do
        if v.isAppOfArity ``Ty.wrap 2 then
          if let some hp← isFalse (mkApp (mkConst ``Ty.hasPtr) gt) then
            if let some hpad← isFalse (mkApp (mkConst ``Ty.hasPadding) gt) then
              pure (some (v.appArg!, hp, hpad))
            else
              pure none
          else
            pure none
        else
          pure none
    let (hB, hD, D) ←
      match plain? with
      | some (r, hp, hpad) =>
        do
          let hf ← mkAppOptM ``GlobalInitializer.flattenDef_wrap #[tt, wE, r, hp, hpad, hw]
          pure (← proj ``Prod.fst hf, ← proj ``Prod.snd hf, none)
      | none =>
        do
          let lit (f : Name) : MetaM (Nat × Expr) := do
            let e := mkApp2 (mkConst ``Ty.flattenNat) gt (mkApp2 (mkConst f) gt v)
            let some k ←
              Tactic.kernelNat?
                  e | throwError "`step_addressof`: the initializer's bits are no literal"
            return (k, ← Tactic.kernelRfl e (mkNatLit k))
          let (b, hb) ← lit ``Ty.valueOrZero
          let (d, hd) ← lit ``Ty.definedness
          let hx ←
            mkAppOptM ``Ty.flattenDef_eq_ofNat #[gt, v, wE, mkNatLit b, mkNatLit d, hw, hb, hd]
          pure (← proj ``Prod.fst hx, ← proj ``Prod.snd hx, some d)
    let hread ← mkAppM ``GlobalInitializer.readAt #[hblk, hv, hw, hB]
    hyps ← add hyps (name "hread_x") hread
    let hdef ← mkAppM ``GlobalInitializer.definedAt #[hblk, hv, hw, hD]
    hyps ← add hyps (name "hdefined_x") hdef
    -- the known runs, `Live` at the value's width
    let hle ← mkDecideProof (← mkAppM ``LE.le #[wE, ← mkAppM ``HMul.hMul #[mkNatLit 8, nE]])
    let hliveW ← mkAppM ``Live.mono #[hle, hlive]
    let runs :=
      match D with
      | some d => definedRuns d w
      | none => #[(0, w)]
    for (a, len) in runs do
      let Dv ←
        match D with
        | some d =>
          pure (mkApp2 (mkConst ``BitVec.ofNat) wE (mkNatLit d))
        | none =>
          mkAppM ``BitVec.allOnes #[wE]
      let lenE := mkNatLit len
      if a == 0 then
        let hDTy ←
          mkEq (← mkAppM ``BitVec.extractLsb' #[mkNatLit 0, lenE, Dv])
              (← mkAppM ``BitVec.allOnes #[lenE])
        let some hD' ←
          Tactic.kernelDecide? hDTy | throwError "`step_addressof`: the defined run at bit {a}"
        let hlw ← mkDecideProof (← mkAppM ``LE.le #[lenE, wE])
        let pf ← mkAppM ``Fits.of_definedAt_self #[hliveW, hdef, hlw, hD']
        hyps ← add hyps (name "hx_fits") pf
      else
        let off := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit (a / 8))
        let start ← mkAppM ``HMul.hMul #[← mkAppM ``BitVec.toNat #[off], mkNatLit 8]
        let hDTy ←
          mkEq (← mkAppM ``BitVec.extractLsb' #[start, lenE, Dv])
              (← mkAppM ``BitVec.allOnes #[lenE])
        let some hD' ←
          Tactic.kernelDecide? hDTy | throwError "`step_addressof`: the defined run at bit {a}"
        let hov ←
          mkDecideProof
              (mkNot
                (←
                  mkEq (← mkAppM ``BitVec.uaddOverflow #[← mkAppM ``Pointer.offset #[P], off])
                      (mkConst ``Bool.true)))
        let hlw ← mkDecideProof (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[start, lenE], wE])
        let pf ← mkAppM ``Fits.of_definedAt #[hliveW, hdef, hov, hlw, hD']
        hyps ← add hyps (name s!"hx_fits_{a / 8}") pf
    -- the pointers known writable are not into the global's read-only block
    let hro ← mkAppM ``GlobalImage.block_writable #[hc]
    let blk ← mkAppM ``Pointer.id #[P]
    let mut seen : Array Expr := #[]
    for (pf, ty) in ← Tactic.splitConjunctedFacts do
      let some (q, hw) ←
        (do
            if ty.isAppOfArity ``Writable 2 && ty.getArg! 0 == mem then
              return some (ty.getArg! 1, pf)
            let some (1, m, q, _) := Tactic.memPred? ty | return none
            unless m == mem do
              return none
            return some (q, ← mkAppM ``Room.writable #[pf])) | continue
      let q := Tactic.stripAdds q
      unless q.isFVar && q != x && !seen.contains q do
        continue
      seen := seen.push q
      let hw ←
        if q == (← inferType hw).getArg! 1 then
          pure hw
        else
          mkAppM ``Writable.of_id_eq #[hw, ← mkEqRefl (← mkAppM ``Pointer.id #[q])]
      let ne ← mkAppM ``Writable.ne_of_readOnly #[hw, hblk, hro]
      let ne := mkExpectedPropHint ne (← mkAppM ``Ne #[← mkAppM ``Pointer.id #[q], blk])
      hyps ← add hyps (.mkSimple s!"h{← q.fvarId!.getUserName}_ne_{xName}") ne
    let (_, g) ← g.assertHypotheses hyps
    return g

@[tactic stepAddressof]
def evalStepAddressof : Tactic := fun stx =>
  Tactic.atStepDepth do
    let args := StepArgs.parse mkNullNode stx[2] stx[3] mkNullNode (named := true)
    -- the pointer's equation is cleared after: an inaccessible name, never `hg`'s
    let args := { args with hyp := .named (mkIdent (← mkFreshUserName `hx)) }
    Tactic.ensureStateEq
    -- the instruction's global and state
    let (sym, S) ←
      withMainContext do
          let saved ← saveState
          let ⟨stepGoal, _⟩ ← rewriteStep (← getMainGoal) ``BasicBlock.runBodyFrom_step_of_run
          let some (_, lhs, _) := (← instantiateMVars (← stepGoal.getType)).eq?
            | throwError "`step_addressof`: no run goal"
          let instr ← whnfR lhs.appFn!.appArg!
          let S := lhs.appArg!
          saved.restore
          let_expr Instr.addressof _ symE _ := instr
            | throwError "`step_addressof`: not an `addressof`:{indentExpr instr}"
          let some sym := strLit? symE | throwError "`step_addressof`: the symbol {symE}"
          return (sym, S)
    -- the value lemma or global, before the step names a local like it
    let hv? ←
      if stx[1].isNone then
        pure none
      else
        some <$> withMainContext (Term.elabTerm stx[1][0] none >>= instantiateMVars)
    let hv? ←
      withMainContext <|
          hv?.mapM fun h => do
            if (← whnfR (← inferType h)).isConstOf ``GlobalInitializer then
              return (← globalValue h).2
            return h
    withMainContext do
        let mem ← mkAppM ``GlobalState.mem #[S]
        -- the globals fact and the entry
        let mut found : Option (Expr × Expr) := none
        for d in ← getLCtx do
          if d.isImplementationDetail then
            continue
          let ty ← instantiateMVars d.type
          let_expr MemoryState.Globals m G := ty | continue
          unless
            ←
              withTransparency .default
                  (isDefEq (← mkAppM ``MemoryState.globals #[m])
                    (← mkAppM ``MemoryState.globals #[mem])) do
            continue
          if let some (e, hmem)← findGlobal? G sym then
            found := some (← mkAppM ``MemoryState.Globals.globals_eq #[d.toExpr, hmem], e)
            break
        let some (hglobal, entry) := found
          | throwError "`step_addressof`: no fact `S.mem.Globals G` with `@{sym}` in `G`"
        -- about `S`, the symbol as the instruction spells it
        let symE := mkStrLit sym
        let img ← mkAppM ``GlobalInitializer.image #[← entryInit entry]
        let blk ← mkAppM ``MemoryState.globalBlock #[mem, symE]
        let hglobal :=
          mkExpectedPropHint hglobal
            (←
              mkEq (← mkAppM ``MemoryState.globals #[mem, symE])
                  (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[blk, img]]))
        -- the block as a local `b` with its entry `hb`, which no step's simplification changes
        let entryTy (b : Expr) : MetaM Expr := do
          mkEq (← mkAppM ``MemoryState.globals #[mem, symE])
              (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[b, img]])
        let (fvs, g) ← generalizeOpaque (← getMainGoal) blk `b #[⟨`hb, entryTy, hglobal⟩]
        replaceMainGoal [g]
        let (bv, hb) := (mkFVar fvs[0]!, mkFVar fvs[1]!)
        withMainContext do
            -- the step: `addressof` gives the block's start
            let ⟨stepGoal, main⟩ ← rewriteStep (← getMainGoal) ``BasicBlock.runBodyFrom_step_of_run
            let lem ← mkConstWithFreshMVarLevels ``run_addressof
            let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType lem)
            unless ← isDefEq ms.back! hb <&&> isDefEq concl (← stepGoal.getType) do
              throwError
                "`step_addressof`: `run_addressof` does not close{indentExpr (← stepGoal.getType)}"
            stepGoal.assign (← instantiateMVars (mkAppN lem ms))
            replaceMainGoal [main]
        finishStep args
        withMainContext do
            -- the named pointer `hx : x = ⟨b, 0⟩`; none when it is dead
            let eqs ← Tactic.localEqs
            let some e :=
              eqs.findRev? fun e =>
                let rhs := e.rhs.consumeMData
                e.lhs.isFVar && rhs.isAppOfArity ``Pointer.mk 2 && rhs.appFn!.appArg! == bv
              | replaceMainGoal [← (← (← getMainGoal).tryClear hb.fvarId!).tryClear bv.fvarId!]
            let g ← addGlobalFacts (← getMainGoal) S e.lhs e.decl.toExpr hb entry hv?
            -- the pointer opaque, its facts saying what it is; its block's local gone
            let g ← (← (← g.tryClear e.decl.fvarId).tryClear hb.fvarId!).tryClear bv.fvarId!
            replaceMainGoal [g]

end

end MLIR
