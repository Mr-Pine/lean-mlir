import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_selectznz
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_cmovznz_u64

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The five scratch cells the region allocates, all `i64`. Indexed by `Nat`,
not `Fin`, because `GlobalState.allocaChain` is. -/
def cw (_ : Nat) : Nat :=
  64

/-- The five cells, as the chain's pointers: consecutive block ids from the
entry counter, each at offset 0. -/
def cellPtr (s : GlobalState) : Fin 5 → Pointer := fun i => s.chainPtr cw i.val

open Lean Elab Tactic in
/-- `peel_gep_at i, p` steps a `getelementptr` by the constant `i` off a
five-limb element at `p`, rewriting its result to the *expression*
`p.withOffset (8 * i)`.

`peel_gep_limb` binds a `let` for that pointer instead. Anything the walk binds
is out of scope where the walk's conclusion is used, so the walk here binds
nothing: it proves one equation whose final state is already named. -/
elab "peel_gep_at " i:num ", " p:term : tactic => do
  let n ← nextStepIndex (← getMainGoal)
  let nLit := Syntax.mkNumLit (toString n)
  let vBase := mkIdent (Name.mkSimple "v")
  let v := mkIdent (Name.mkSimple ("v" ++ toString n))
  let hv := mkIdent (Name.mkSimple ("hv" ++ toString n))
  let off := Syntax.mkNumLit (toString (i.getNat * 8))
  evalTactic (← `(tactic| denote_step_all $vBase $nLit))
  evalTactic (← `(tactic| denote_eval $vBase $nLit $nLit))
  evalTactic (← `(tactic| have vValue : $v = .value (($p).withOffset (($off) : BitVec 64)) := by
    simp [$hv:ident, gep, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton,
      LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, simp_sllvm]))
  evalTactic (← `(tactic| subst vValue))
  evalTactic (← `(tactic| clear $hv))

/-! ### The walk, in two halves

Each step is a `_facts` half that only builds context and a `_peel` half that
only rewrites the goal, as `to_bytes` splits its kernel calls. Here the reason
is scope: the peels prove one equation whose right-hand side is `m₄`, so every
name that state is built from -- the call results, the blocks their values are
read out of -- has to exist before the peels run. -/

open Lean Elab Tactic in
/-- `cmov_facts k` names what the `k`-th `cmovznz` needs and what it leaves:
the two operand limbs' blocks, the call's result state `u<k>` with its run
equation and splice equivalence, and then `hwf<k>`/`hxu<k>`/`hyu<k>`/`hcf<k>`/
`fb<k>` carried across it. The state entering step `k` is `u` at `k = 0` and
`u<k-1>` after that, with its facts named in the same shape. -/
elab "cmov_facts " k:num : tactic => do
  let n := k.getNat
  let sfx := subscript n
  let psfx := if n == 0 then "" else subscript (n - 1)
  let nm (stem s : String) := mkIdent (Name.mkSimple (stem ++ s))
  let st₀ := mkIdent (Name.mkSimple "s");
  let cnd := mkIdent (Name.mkSimple "c")
  let hcell := mkIdent (Name.mkSimple "hcell");
  let hcellne := mkIdent (Name.mkSimple "hcellne")
  let hnx := mkIdent (Name.mkSimple "hnx");
  let hny := mkIdent (Name.mkSimple "hny")
  let xId := mkIdent (Name.mkSimple "x");
  let yId := mkIdent (Name.mkSimple "y")
  let st := nm "u" psfx;
  let wf := nm "hwf" psfx;
  let fb := nm "fb" psfx
  let hx := nm "hxu" psfx;
  let hy := nm "hyu" psfx;
  let cf := nm "hcf" psfx
  let st' := nm "u" sfx;
  let wf' := nm "hwf" sfx;
  let fb' := nm "fb" sfx
  let hx' := nm "hxu" sfx;
  let hy' := nm "hyu" sfx;
  let cf' := nm "hcf" sfx
  let hrun := nm "hrun" sfx;
  let heq := nm "heq" sfx;
  let hlive := nm "hlive" sfx
  let kLit := Syntax.mkNumLit (toString n)
  let off := Syntax.mkNumLit (toString (n * 8))
  let rem := Syntax.mkNumLit (toString ((5 - n) * 64))
  let mut vals := #[]
  for (base, hbase) in [("x", hx), ("y", hy)] do
    let p := mkIdent (Name.mkSimple base)
    let blk := nm (base ++ "blk") sfx
    let hblk := nm ("h" ++ base ++ "blk") sfx
    let hlen := nm ("h" ++ base ++ "len") sfx
    let ptr ←
      if n == 0 then
        `($p)
      else
        `(($p).withOffset (($off) : BitVec 64))
    let fits ←
      if n == 0 then
        pure hbase
      else
        do
          let ho := nm ("h" ++ base ++ "o") sfx
          evalTactic
              (←
                `(tactic|
                    have $ho:ident : Fits ($st).mem $ptr $rem := by
                      simpa using remainingFits ($st).mem $p $hbase ($off) (by simp)))
          pure ho
    evalTactic (← `(tactic| obtain ⟨$blk:ident, $hblk:ident, $hlen:ident⟩ := id $fits))
    let val ← `(($blk).bytes.extractLsb' ($ptr).offsetInBits 64)
    -- the limb as a read of the *entry* state: the calls run before any store,
    -- so the operands are still the caller's, even if `r` aliases one of them
    let hn := if base == "x" then hnx else hny
    evalTactic
        (←
          `(tactic|
              have $(nm ("h" ++ base ++ "val") sfx):ident :
                readWord? $ptr 64 ($st₀).mem = some $val := by
                rw [readWord?_of_live?_eq (p := $ptr) (($fb) ($p).id $hn).symm]
                simp only [readWord?, MemoryState.live?, $hblk:ident]
                rfl))
    vals := vals.push val
  evalTactic
      (←
        `(tactic|
            obtain ⟨$st':ident, $hrun:ident, $heq:ident⟩ :=
              fiat_25519_cmovznz_u64_conforms (cellPtr $st₀ $kLit) $cnd $(vals[0]!) $(vals[1]!) $st
                $wf ($cf $kLit)))
  -- what the call put in cell `k`, and the earlier cells carried across it
  evalTactic
      (←
        `(tactic|
            have $(nm "hcval" sfx):ident :
              readWord? (cellPtr $st₀ $kLit) 64 ($st').mem =
                some (if $cnd = 0 then $(vals[0]!) else $(vals[1]!)) := by
              rw [readWord?_of_live?_eq (p := cellPtr $st₀ $kLit)
                  (($heq).live (cellPtr $st₀ $kLit).id).symm]
              exact readWord?_splice_self _ ($cf $kLit)))
  for j in [0:n] do
    let jLit := Syntax.mkNumLit (toString j)
    let hj := nm "hcval" (subscript j)
    evalTactic
        (←
          `(tactic|
              replace $hj:ident :=
                (readWord?_of_live?_eq (p := cellPtr $st₀ $jLit)
                      (($heq).live (cellPtr $st₀ $jLit).id).symm).trans
                  ((readWord?_splice_ne ($hcellne $kLit $jLit (by decide))).trans $hj)))
  evalTactic
      (←
        `(tactic|
            have $hlive:ident :
              ∀ b : BlockId, (cellPtr $st₀ $kLit).id ≠ b → ($st').mem.live? b = ($st).mem.live? b :=
              fun b hb => (($heq).live b).symm.trans (live?_splice_ne hb)))
  evalTactic (← `(tactic| have $wf':ident : ($st').WF := GlobalState.WF.of_equiv ($wf).splice $heq))
  evalTactic
      (←
        `(tactic|
            have $hx':ident : Fits ($st').mem $xId (5 * 64) :=
              fits_of_live?_eq ($hlive ($xId).id ($hcell $kLit ($xId).id $hnx)) $hx))
  evalTactic
      (←
        `(tactic|
            have $hy':ident : Fits ($st').mem $yId (5 * 64) :=
              fits_of_live?_eq ($hlive ($yId).id ($hcell $kLit ($yId).id $hny)) $hy))
  evalTactic
      (←
        `(tactic|
            have $cf':ident : ∀ j : Fin 5, Fits ($st').mem (cellPtr $st₀ j) 64 := by
              intro j
              by_cases hj : j = $kLit
              · subst hj
                exact fits_equiv $heq (by simpa using fits_splice ($cf $kLit))
              · exact
                  fits_of_live?_eq ($hlive (cellPtr $st₀ j).id ($hcellne $kLit j (Ne.symm hj)))
                    ($cf j)))
  evalTactic
      (←
        `(tactic|
            have $fb':ident : FrameBelow ($st₀).alloc.nextFreeBlock $st₀ $st' := fun b hb =>
              ($hlive b ($hcell $kLit b hb)).trans ($fb b hb)))
  evalTactic (← `(tactic| clear $hlive $fb $wf $hx $hy $cf))

open Lean Elab Tactic in
/-- `cmov_peel k` runs what `cmov_facts k` prepared: the two operand loads,
each behind a `getelementptr` once `k > 0`, and the call. -/
elab "cmov_peel " k:num : tactic => do
  let n := k.getNat
  let sfx := subscript n
  let psfx := if n == 0 then "" else subscript (n - 1)
  let nm (stem s : String) := mkIdent (Name.mkSimple (stem ++ s))
  let st := nm "u" psfx
  let off := Syntax.mkNumLit (toString (n * 8))
  let kLit := Syntax.mkNumLit (toString n)
  for base in ["x", "y"] do
    let p := mkIdent (Name.mkSimple base)
    let ptr ← if n == 0 then `($p) else do
      evalTactic (← `(tactic| peel_gep_at $kLit, $p))
      `(($p).withOffset (($off) : BitVec 64))
    evalTactic (← `(tactic| peel_load (.bitvec (.concrete 64)),
      $(nm (base ++ "blk") sfx), $ptr, $(nm ("h" ++ base ++ "blk") sfx), $st))
  evalTactic (← `(tactic| peel_call $(nm "hrun" sfx)))
  -- the step's scaffolding: the blocks' hypotheses, the gep's `Fits`, and the
  -- call's splice equivalence, all consumed by `cmov_facts`
  evalTactic (← `(tactic| clear $(nm "hrun" sfx) $(nm "heq" sfx) $(nm "hxblk" sfx)
    $(nm "hxlen" sfx) $(nm "hyblk" sfx) $(nm "hylen" sfx)))
  if n != 0 then
    evalTactic (← `(tactic| clear $(nm "hxo" sfx) $(nm "hyo" sfx)))
    -- with its run equation gone the state the step started in is dead too
    evalTactic (← `(tactic| try clear $(nm "u" psfx)))

open Lean Elab Tactic in
/-- `store_facts k` names the `k`-th write-back: the block cell `k` was spliced
into, the pointer the store targets, and the state `m<k>` it reaches, with the
out-parameter's and the cells' `Fits` carried into it. The state entering step
`k` is `u₄` at `k = 0` and `m<k-1>` after that. -/
elab "store_facts " k:num : tactic => do
  let n := k.getNat
  let sfx := subscript n
  let nm (stem s : String) := mkIdent (Name.mkSimple (stem ++ s))
  let st₀ := mkIdent (Name.mkSimple "s");
  let rp := mkIdent (Name.mkSimple "r")
  let st := if n == 0 then mkIdent (Name.mkSimple "u₄") else nm "m" (subscript (n - 1))
  let hr := if n == 0 then mkIdent (Name.mkSimple "hrm") else nm "hrm" (subscript (n - 1))
  let hc := if n == 0 then mkIdent (Name.mkSimple "hcf₄") else nm "hcm" (subscript (n - 1))
  let st' := nm "m" sfx;
  let hst' := nm "hm" sfx
  let hr' := nm "hrm" sfx;
  let hc' := nm "hcm" sfx
  let blk := nm "cblk" sfx;
  let hblk := nm "hcblk" sfx;
  let hlen := nm "hclen" sfx
  let cnd := mkIdent (Name.mkSimple "c");
  let hcell := mkIdent (Name.mkSimple "hcell")
  let hnr := mkIdent (Name.mkSimple "hnr")
  let kLit := Syntax.mkNumLit (toString n)
  let off := Syntax.mkNumLit (toString (n * 8))
  let rem := Syntax.mkNumLit (toString ((5 - n) * 64))
  -- the operand limbs this cell was selected from, as the call named them
  let opPtr (base : String) : MetaM Term := do
    let p := mkIdent (Name.mkSimple base)
    if n == 0 then
      `($p)
    else
      `(($p).withOffset (($off) : BitVec 64))
  let xv ←
    do
      let p ← opPtr "x";
      `(($(nm "xblk" sfx)).bytes.extractLsb' ($p).offsetInBits 64)
  let yv ←
    do
      let p ← opPtr "y";
      `(($(nm "yblk" sfx)).bytes.extractLsb' ($p).offsetInBits 64)
  evalTactic (← `(tactic| obtain ⟨$blk:ident, $hblk:ident, $hlen:ident⟩ := id ($hc $kLit)))
  let ptr ←
    if n == 0 then
      `($rp)
    else
      `(($rp).withOffset (($off) : BitVec 64))
  if n != 0 then
    evalTactic
        (←
          `(tactic|
              have $(nm "hro" sfx):ident : Fits ($st).mem $ptr $rem := by
                simpa using remainingFits ($st).mem $rp $hr ($off) (by simp)))
  let val ← `(($blk).bytes.extractLsb' (cellPtr $st₀ $kLit).offsetInBits 64)
  evalTactic
      (←
        `(tactic|
            obtain ⟨$st':ident, $hst':ident⟩ :
              ∃ t : GlobalState, t = { $st with mem := ($st).mem.splice $ptr $val } := ⟨_, rfl⟩))
  -- the value the store writes is what the call left in the cell
  evalTactic
      (←
        `(tactic|
            have $(nm "hval" sfx):ident :
              ($blk).bytes.extractLsb' (cellPtr $st₀ $kLit).offsetInBits 64 =
                (if $cnd = 0 then $xv else $yv) := by
              have hread :
                readWord? (cellPtr $st₀ $kLit) 64 ($st).mem =
                  some (($blk).bytes.extractLsb' (cellPtr $st₀ $kLit).offsetInBits 64) := by
                simp only [readWord?, MemoryState.live?, $hblk:ident]
                rfl
              exact Option.some.inj (hread.symm.trans $(nm "hcval" sfx))))
  for j in [n + 1:5] do
    let jLit := Syntax.mkNumLit (toString j)
    let hj := nm "hcval" (subscript j)
    evalTactic
        (←
          `(tactic|
              replace $hj:ident :=
                (readWord?_of_live?_eq (p := cellPtr $st₀ $jLit) (m' := ($st').mem)
                      (show
                        ($st').mem.live? (cellPtr $st₀ $jLit).id =
                          ($st).mem.live? (cellPtr $st₀ $jLit).id
                        by
                        simp only [$hst':ident]
                        exact live?_splice_ne (Ne.symm ($hcell $jLit ($rp).id $hnr)))).trans
                  $hj))
  evalTactic
      (←
        `(tactic|
            have $hr':ident : Fits ($st').mem $rp (5 * 64) := by
              rw [$hst':ident]; exact fits_splice $hr))
  evalTactic
      (←
        `(tactic|
            have $hc':ident : ∀ j : Fin 5, Fits ($st').mem (cellPtr $st₀ j) 64 := by
              intro j; rw [$hst':ident]; exact fits_splice ($hc j)))
  if n != 0 then
    evalTactic (← `(tactic| clear $hr $hc))

open Lean Elab Tactic in
/-- `store_peel k` runs what `store_facts k` prepared: the cell load, the
out-parameter's `getelementptr` once `k > 0`, and the store, folded back to
`m<k>`. -/
elab "store_peel " k:num : tactic => do
  let n := k.getNat
  let sfx := subscript n
  let nm (stem s : String) := mkIdent (Name.mkSimple (stem ++ s))
  let st₀ := mkIdent (Name.mkSimple "s"); let rp := mkIdent (Name.mkSimple "r")
  let st := if n == 0 then mkIdent (Name.mkSimple "u₄") else nm "m" (subscript (n - 1))
  let hr := if n == 0 then mkIdent (Name.mkSimple "hrm") else nm "hrm" (subscript (n - 1))
  let kLit := Syntax.mkNumLit (toString n)
  let off := Syntax.mkNumLit (toString (n * 8))
  let blk := nm "cblk" sfx
  evalTactic (← `(tactic| peel_load (.bitvec (.concrete 64)), $blk, (cellPtr $st₀ $kLit),
    $(nm "hcblk" sfx), $st))
  let (ptr, fits) ← if n == 0 then do pure (← `($rp), hr) else do
    evalTactic (← `(tactic| peel_gep_at $kLit, $rp))
    pure (← `(($rp).withOffset (($off) : BitVec 64)), nm "hro" sfx)
  let val ← `(($blk).bytes.extractLsb' (cellPtr $st₀ $kLit).offsetInBits 64)
  evalTactic (← `(tactic| peel_store $val, $ptr, $fits, $st))
  evalTactic (← `(tactic| rw [← $(nm "hm" sfx):ident]))
  evalTactic (← `(tactic| clear $(nm "hcblk" sfx) $(nm "hclen" sfx) $(nm "hcval" sfx)))
  if n != 0 then evalTactic (← `(tactic| clear $(nm "hro" sfx)))

theorem fiat_25519_selectznz_conforms (r : Pointer) (c : BitVec 8) (x y : Pointer) (s : GlobalState)
    (hs : s.WF) (hr : IsFieldElemPtr s.mem r) (hx : IsFieldElemPtr s.mem x)
    (hy : IsFieldElemPtr s.mem y) : fiat_25519_selectznz_spec r c x y s hr hx hy := by
  simp only [fiat_25519_selectznz_spec, Cfg.denote]
  constructor
  case left =>
    -- the splice reads back the limbs it packed, whichever operand was chosen
    have key :
      ∀ (q : Pointer) (hq : IsFieldElemPtr s.mem q),
        readFieldElem (m := s.mem.splice r (packLimbs fun i => (readLimb i hq : BitVec 64)))
            (isFieldElemPtr_splice hr) =
          readFieldElem hq := by
      intro q hq
      rw [readFieldElem_eq_of (readFieldElem?_splice _ hr.left), readFieldElem_eq_decode hq]
      congr 1
      funext i
      simp only [extractLsb'_packLimbs, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (readLimb_lt i hq)
    rw [key]
    split <;> rfl
  -- Strip the call wrapper first: what is left is the body's own run, and the
  -- caller's view of the state it ends in, up to the frame the call pops.
  refine run_runFunction' _ ?_
  -- The frame, and everything the walk needs about it, while it is still
  -- transparent: `s.allocaChain cw 5` unfolds into the five `HashMap` inserts,
  -- so left exposed it makes defeq walk the buckets on every `live?` query --
  -- ~600k reductions apiece. Below, the state is opaque.
  have hnx : x.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hx.left
  have hny : y.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hy.left
  have hnr : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr.left
  have fb : FrameBelow s.alloc.nextFreeBlock s (s.allocaChain cw 5) :=
    FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 5
  have hwf : (s.allocaChain cw 5).WF := GlobalState.WF.allocaChain hs 5
  have hcf : ∀ k : Fin 5, Fits (s.allocaChain cw 5).mem (cellPtr s k) 64 := fun k =>
    GlobalState.fits_chainPtr k.isLt
  have hxu : Fits (s.allocaChain cw 5).mem x (5 * 64) := fits_of_live?_eq (fb x.id hnx) hx.left
  have hyu : Fits (s.allocaChain cw 5).mem y (5 * 64) := fits_of_live?_eq (fb y.id hny) hy.left
  set u : GlobalState := s.allocaChain cw 5 with hu
  clear_value u
  -- The cells are the blocks the frame allocated, so they miss everything the
  -- caller holds, and they are consecutive, so they miss each other.
  have hcell :
    ∀ (k : Fin 5) (b : BlockId), b.id < s.alloc.nextFreeBlock → (cellPtr s k).id ≠ b := by
    intro k b hb h
    have hid : (cellPtr s k).id.id = b.id := congrArg BlockId.id h
    simp only [cellPtr, GlobalState.chainPtr_id] at hid
    omega
  have hcellne : ∀ j k : Fin 5, j ≠ k → (cellPtr s j).id ≠ (cellPtr s k).id := by
    intro j k hjk h
    have hid : (cellPtr s j).id.id = (cellPtr s k).id.id := congrArg BlockId.id h
    simp only [cellPtr, GlobalState.chainPtr_id] at hid
    exact hjk (Fin.val_injective (by omega))
  -- %0-%5: the alloca count, the five scratch cells folded to `cellPtr s k` and
  -- sealed as `u`, and the `lifetime.start` markers, which move nothing.
  denote_step_all v 0
  eval_consts v 0 0
  peel_alloca_chain s, cw, 5
  fold_cells s, cw, cellPtr, 5
  rw [← hu]
  iterate 5 peel_lifetime
  -- %6-%23: the five limbwise selects, each step's facts beside its peel
  cmov_facts 0
  cmov_peel 0
  cmov_facts 1
  cmov_peel 1
  cmov_facts 2
  cmov_peel 2
  cmov_facts 3
  cmov_peel 3
  cmov_facts 4
  cmov_peel 4
  -- %24-%32: the five cells written back into the out-parameter
  have hrm : Fits u₄.mem r (5 * 64) := fits_of_live?_eq (fb₄ r.id hnr) hr.left
  store_facts 0
  store_peel 0
  store_facts 1
  store_peel 1
  store_facts 2
  store_peel 2
  store_facts 3
  store_peel 3
  store_facts 4
  store_peel 4
  -- Everything the walk consumed. What the two clauses below need is the store
  -- chain `hm<k>`/`hval<k>`, the operands' limbs `hxval<k>`/`hyval<k>`, and the
  -- frame `fb₄`.
  clear hwf₄ hxu₄ hyu₄ hcf₄ hrm₄ hcm₄ hcell hcellne hnx hny hu u
  -- the `lifetime.end` markers and the return
  iterate 5 peel_lifetime
  simp only [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]
  -- The walk ended at `m₄`; the rest is the two clauses about it.
  refine ⟨m₄, rfl, popFrame_equiv_splice hs hnr ?frame ?val⟩
  case frame =>
    -- every store went to `r`'s block, and the frame state agrees with `s`
    -- below the entry counter
    intro b hb hbr
    have hne :
      ∀ (m : MemoryState) (o : BitVec 64) (v : BitVec 64),
        (m.splice (r.withOffset o) v).live? b = m.live? b :=
      fun _ _ _ => live?_splice_ne (Ne.symm hbr)
    have hne0 : ∀ (m : MemoryState) (v : BitVec 64), (m.splice r v).live? b = m.live? b :=
      fun _ _ => live?_splice_ne (Ne.symm hbr)
    simp only [hm₄, hm₃, hm₂, hm₁, hm₀, hne, hne0]
    exact fb₄ b hb
  case val =>
    -- Every cell holds the selected operand's limb, read from the entry state,
    -- so the five stores wrote the packed limbs of `if c = 0 then x else y`.
    have hoff :
      ∀ (p : Pointer) (o : BitVec 64),
        p.offset.toNat + 5 * 8 ≤ 2 ^ 64 →
          o.toNat ≤ 32 → (p.withOffset o).offsetInBits = p.offsetInBits + 8 * o.toNat :=
      fun _ _ hp ho => withOffset_offsetInBits (by omega)
    have hsel :
      ∀ (k : Fin 5) (qx qy : Pointer) (vx vy : BitVec 64),
        qx.id = x.id →
          qx.offsetInBits = x.offsetInBits + 64 * k.toNat →
          qy.id = y.id →
          qy.offsetInBits = y.offsetInBits + 64 * k.toNat →
          readWord? qx 64 s.mem = some vx →
          readWord? qy 64 s.mem = some vy →
          (if c = 0 then vx else vy) =
            ((readLimb (p := if c = 0 then x else y) (m := s.mem) k (by grind only) : ℕ) :
              BitVec 64) := by
      intro k qx qy vx vy hidx hoffx hidy hoffy hvx hvy
      by_cases hc : c = 0
      · simp only [if_pos hc]
        exact (readLimb_eq_of_readWord? hx hidx hoffx hvx).symm
      · simp only [if_neg hc]
        exact (readLimb_eq_of_readWord? hy hidy hoffy hvy).symm
    have e₀ := hsel 0 x y _ _ rfl (by simp) rfl (by simp) hxval₀ hyval₀
    have e₁ :=
      hsel 1 (x.withOffset 8) (y.withOffset 8) _ _ rfl
        (by
          rw [hoff x 8 hx.right (by decide)]; simp)
        rfl
        (by
          rw [hoff y 8 hy.right (by decide)]; simp)
        hxval₁ hyval₁
    have e₂ :=
      hsel 2 (x.withOffset 16) (y.withOffset 16) _ _ rfl
        (by
          rw [hoff x 16 hx.right (by decide)]; simp)
        rfl
        (by
          rw [hoff y 16 hy.right (by decide)]; simp)
        hxval₂ hyval₂
    have e₃ :=
      hsel 3 (x.withOffset 24) (y.withOffset 24) _ _ rfl
        (by
          rw [hoff x 24 hx.right (by decide)]; simp)
        rfl
        (by
          rw [hoff y 24 hy.right (by decide)]; simp)
        hxval₃ hyval₃
    have e₄ :=
      hsel 4 (x.withOffset 32) (y.withOffset 32) _ _ rfl
        (by
          rw [hoff x 32 hx.right (by decide)]; simp)
        rfl
        (by
          rw [hoff y 32 hy.right (by decide)]; simp)
        hxval₄ hyval₄
    -- the five stores are one write of the packed word, and `r` is the
    -- caller's block throughout
    have h5 :=
      (splice5_equiv (s := u₄) (cblk₀.bytes.extractLsb' (cellPtr s 0).offsetInBits 64)
            (cblk₁.bytes.extractLsb' (cellPtr s 1).offsetInBits 64)
            (cblk₂.bytes.extractLsb' (cellPtr s 2).offsetInBits 64)
            (cblk₃.bytes.extractLsb' (cellPtr s 3).offsetInBits 64)
            (cblk₄.bytes.extractLsb' (cellPtr s 4).offsetInBits 64) ⟨hrm, hr.right⟩).live
        r.id
    simp only [hm₄, hm₃, hm₂, hm₁, hm₀]
    rw [h5, live?_splice_congr (fb₄ r.id hnr)]
    rw [hval₀, hval₁, hval₂, hval₃, hval₄, e₀, e₁, e₂, e₃, e₄, packLimbs]

end Firedancer.Ref
