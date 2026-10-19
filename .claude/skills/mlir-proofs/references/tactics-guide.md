# RIR tactics: user guide

The tactics in the order a proof uses them, each with a minimal example from the existing proofs
(named by file) and the mistakes that cost the most time. Exact behaviour, names and failure messages are in
`tactics.md`.

## The shape of every proof

```lean
public theorem f.call_eq (…) (s : GlobalState) (hwf : s.WF) (…preconditions…) :
    f.call (f.args (.value p) …) s = .value (rets, s') := by
  func_init            -- call → run of the entry block, state S, env E
  block_init           -- the entry block's body
  step_…               -- one tactic per instruction, in order
  finish_block         -- the exit: a return, or one goal per jump target
  …                    -- per jump: block_init … finish_block, or run_from
  <close the final equation>
```

Read the instructions next to the proof: the infoview's **Instructions** panel shows the one the
next step runs, and the lift (`Mlir/f.lean`) has them all.

## 1. `func_init`

Always first, on `f.call args s = R`. Give the theorem `hwf : s.WF` and every `Fits`/`Room`/
`LimbsFit` fact the steps will need; they arrive about `S`.

```lean
-- fd_f25519_add.lean
  func_init
  have hr₀ : S₀.mem.LimbsFit r := hS ▸ hr   -- a fact about the entry state, for the end
  block_init
```

Mistakes:
- A final state the frame-free check cannot see as WF (a new `storeX` without a `mlir_mem` WF
  lemma) silently takes the framed path, and the proof ends with an `eraseFrom` to remove. Add
  the WF lemma (`GlobalState.WF_storeLimbs`) instead.
- The hypotheses arrive about `S` and move with it from step to step, while the target speaks
  about the entry state `S₀`. Copy what the end of the proof needs about `S₀` before the first
  step (`hr₀` above).

## 2. `block_init`

At the start of every block: after `func_init`, after each jump of `finish_block`, and at the
start of a loop or pattern lemma. Nothing to choose.

## 3. `step_pure`

Constants, arithmetic, compares, `gep`, casts, vector ops (and, effectful, `lifetime.*` and
`assume`: §7). Name the values a reader
should see, after the C source's variables, and keep the others inline; `opaque` stops a step from
unfolding the unnamed values it reads:

```lean
-- fiat_25519_carry.lean
  step_load with x1
  step_pure opaque -- lshr
  step_pure -- gep
  step_load
  step_pure with x2 -- add
  …
  -- x6 = ((x1 & UINT64_C(0x7ffffffffffff)) + ((x5 >> 51) * UINT8_C(0x13)));
  step_pure opaque
  step_pure opaque
  step_pure
  step_pure with x6
```

Flagged operations need their no-overflow fact as a simp lemma; the step resolves the overflow
test only if `simp` can:

```lean
-- fd_curve25519_scalar_wnaf.lean
  step_pure [saddOverflow_ofNat64_one (i := i) (by omega),
    uaddOverflow_ofNat64_one (i := i) (by omega), ← BitVec.ofNat_add]
```

or, when the fact holds for all inputs, as a `@[simp]` lemma (`shift_mask_uaddOverflow` in
`fiat_25519_carry.lean`, by `bv_decide`).

Mistakes:
- `with x` on a value that a later lemma must see expanded (an overflow lemma over `x >>> 51`):
  the step sees only `x`. Use `with transparent x`, or pass `[hx]` to the later step.
- `with x` on a value that is then stored: `hS` mentions `x`, `hx` mentions the old state, and
  `subst_vars` at the end cannot eliminate them. Use `with transparent x` for stored values,
  handles and branch plumbing.
- Inlining everything: the goals grow with every step and the proof slows down. Name the C
  variables.

## 4. `step_load`, `step_store`

```lean
-- fiat_25519_add.lean: five loads of each input, the sums, five stores
  step_load
  step_load
  step_pure
  iterate 4
    step_pure
    step_load
    step_pure
    step_load
    step_pure
  step_store
  iterate 4
    step_pure
    step_store
  finish_block
```

A load needs `Fits` (the bits known), a store only `Room` (live, in bounds); both come from the
facts: `LimbsFit` conjunctions are split, `p.add k` inside a 320-bit fact is found, and a `Fits`
fact gives `Room`. After the stores, `hread_out`, `hread_out_8`, … hold the stored limbs and
`hfits_out`, `hfits_out_8`, … the stored ranges, so an output given only `Room` can be loaded back.

Mistakes:
- "operand … is not known to be `.value _`": the pointer or value is still an `if … then .poison`
  (a `gep` whose no-wrap was not shown, a flagged operation). Fix the step that produced it.
- Leaving dead facts in the state: each one is carried through every later step. Consume a fact
  on the step that uses it last (here: the read facts of two loaded inputs; the loaded values are
  named, so the facts say nothing new):

```lean
-- Avx512/fd_r43x6_pow22523_2.lean
    ( step_load with $a:ident consuming $(h a)
      step_load with $b:ident consuming $(h b)
      step_call using fd_r43x6_repsqr_mul2.call_eq))
```

## 5. `step_memcpy`, `step_memmove`, `step_memset`

```lean
-- fd_sha512_init.lean
  step_pure
  step_memset
  finish_block
  simp [hS]
  rfl
```

`step_memcpy` needs the two ranges disjoint: give the theorem `p.id ≠ q.id` (or a `Nodup` list of
ids) when they are not distinct slots; `Room` of the destination, `Fits` of the source, or only
`Room` of it (its definedness copied; the known sub-ranges stay known) (`memset`: `Room`).
`step_memmove` takes the same facts but disjointness. A literal length is a numeral count
(`n := 40`), and `mem_fact` compares widths and literal offsets as literals, so facts in any
spelling (`Fits S.mem p 320`, an object predicate's conjunct at `p.add 40#64`) serve; there is no
`simp_all` fallback: a missing fact is a `mem_fact` error naming it.

## 6. `step_call`

The callee's `call_eq` theorem, and its premises from the context:

```lean
-- fd_f25519_add.lean
  step_call using fiat_25519_add.call_eq
  step_call using fiat_25519_carry.call_eq
  finish_block
  subst_vars
  simp [MemoryState.readLimbs_storeLimbs_self hr₀, MemoryState.storeLimbs_storeLimbs_self hr₀.1]
```

A callee bound as a parameter (`mlir_def … (frombytes : FromBytes) … with @f := frombytes`) is
called through its spec hypothesis: `step_call using hspec.1`.

An unbound library call steps with the framework's lemma, its result named and resolved by the
result's lemmas:

```lean
-- Tests/Syntax/LibCalls.lean: bcmp(p, q, 32) == 0
  step_call using Operation.bcmp_eq with r
  step_pure [hr, Operation.bcmpResult_self]
```

Mistakes:
- A premise the context cannot show by `mem_fact` or `simp [mlir_mem, *]`: state it with `have`
  before the step (`have hzero_limbs := MemoryState.LimbsFit.of_fits hzero_fits hzero_off`).
- A fact that does not survive the call shows up as an extra goal before the main one: register a
  `mlir_transport` lemma for the callee's result state (`MemoryState.LimbsFit.storeLimbs`). A
  framed callee's state is a constructor, `{ alloc := ⟨s.alloc.nextFreeBlock + k⟩, mem := … }`:
  `S.WF` carries only through a lemma of that shape (`GlobalState.WF.storePoint_mk`).
- Large spec terms in the state: name the callee's result right after the call (`name_limbs x`,
  a project tactic: `conventions.md`).

## 7. `step_alloca`, `step_addressof`, `erase_frame`

```lean
-- copy_via_tmp.lean
  func_init
  block_init
  step_alloca
  have hv0_limbs := MemoryState.LimbsFit.of_fits hv0_fits hv0_off
  step_pure
  step_call using fd_f25519_set.call_eq
  step_call using fd_f25519_set.call_eq
  step_pure
  finish_block
  subst_vars
  simp [mlir_frame, ← GlobalState.allocaPtr_eq_slot, *]
```

```lean
-- fd_ed25519_point_set_zero.lean: hg : s.mem.Globals fd_ed25519_point_set_zero.globals
  step_addressof fd_f25519_zero.value_eq with zero
  step_addressof fd_f25519_one.value_eq with one
  …
```

A global's block is the program's, placed before any call (`hg`, one hypothesis per theorem:
`s.mem.Globals f.globals`, the list `mlir_def` builds of `f`'s globals and its `Func` callees');
`addressof` allocates nothing. A constant's block is read-only: `Fits`/`Live` facts, no `Room`;
a callee storing through a pointer needs it writable (`Room`, or `Fits` and `Writable`).

A function with an `alloca` is framed: its final state has
`alloc := ⟨s.alloc.nextFreeBlock + k⟩` and the proof ends with `erase_frame` (or
`simp [mlir_frame, …]`). A slot is undefined until stored to: `step_alloca` gives `hv0_room`, not
a `Fits`; a callee writing it takes `Room` for its output. An `alloca` with lifetime markers is
dead until its `lifetime.start`:

```lean
-- Tests/Syntax/Lifetime.lean: alloca, lifetime.start, store, load, lifetime.end
  step_pure
  step_alloca -- hv1_bounds : InBounds S.mem v1 64
  step_pure   -- lifetime.start: hroom_v1 : Room S.mem v1 64
  step_store  -- hfits_v1 : Fits S.mem v1 64
  step_load with v
  step_lifetime -- lifetime.end: v1's Room and Fits dropped
  finish_block
  subst hS
  erase_frame
```

The final state keeps the markers (`(… .lifetimeStart x).storeAt x v).lifetimeEnd x`) until
`erase_frame` drops them with the frame's blocks.

Mistakes:
- No `hwf : s.WF`: `step_alloca` stops ("no hypothesis `S.WF`").
- A pointer with no `Fits`/`Room`/`InBounds` fact (a `LimbsFit` conjunct counts) gets no
  `h<q>_ne`, and later reads through it cannot pass the slot's stores: give it one before the
  `alloca`.
- A fact about a slot that a lifetime marker cannot carry (an object predicate over it) is
  dropped at the marker; restate it after the stores (`Fits` from `hfits_<x>` facts, `Fits.append`).
- A slot's lifetime ending is no reason to `clear_facts` it: the marker drops what it cannot
  carry. Clearing a dead temporary's facts still saves the later steps carrying them.
- `step_load` failing on a slot right after `step_alloca` or `lifetime.start`: the load reads
  undefined bits (poison in LLVM), so the code reads before it writes, or the store was not
  stepped yet.
- `assume c`: give `step_assume` the facts that make `c` simplify to `1`; an `assume` the facts
  cannot decide is UB in the cases they leave out.

## 8. `finish_block` and branches

```lean
-- fd_f25519_is_zero.lean: a switch on the first limb
  step_load
  finish_block <;> block_init
  case isFalse.isFalse =>
    finish_block
    …
```

Keep each branch's condition (`have hbr0 := hbr`) before the next `finish_block` reuses the name.
Close impossible branches from `hbr` at once:

```lean
-- sum_limbs.lean
    finish_block
    · simp [BitVec.toNat_eq] at hbr
      omega
```

## 9. Loops: `run_from`

A loop is a lemma about the header block, by induction on the iterations left, in continuation
form; the main proof applies it with `run_from`.

```lean
-- sum_limbs.lean
theorem sum_limbs.loop (a : Pointer) (s : GlobalState) (ha : s.mem.LimbsFit a)
    (hend : a.offset.toNat + 40 < 2 ^ 64) (K) :
    ∀ n k (acc : BitVec 64) (E : ⟪sum_limbs.Γ⟫), k + n = 5 →
      (∀ E' : ⟪sum_limbs.Γ⟫, E'.args = E.args →
        sum_limbs.runFrom (E'[%4 := .value (loopSpec (limb s.mem a) k n acc)]) 3 s = K) →
      sum_limbs.runFrom (E[%1 := .value 5#64, %2 := .value (BitVec.ofNat 64 k),
        %3 := .value (a.add (BitVec.ofNat 64 (8 * k))), %4 := .value acc]) 1 s = K := by
  intro n
  induction n with
  | zero =>
    intro k acc E hk hK
    obtain rfl : k = 5 := by omega
    block_init
    step_pure
    finish_block
    run_from using hK          -- the exit: the continuation
    rfl
  | succ n ih =>
    …
    finish_block
    run_from using ih (k + 1) (acc + limb s.mem a k)   -- the back edge
    · exact (BitVec.ofNat_add k 1).symm
    · rw [Nat.mul_succ, BitVec.ofNat_add]
    · rfl
    run_from using hK
    rfl

-- in sum_limbs.call_eq
  finish_block
  run_from using sum_limbs.loop a _ ha hend _ 5 0 0
  block_init
  finish_block
```

The env in the lemma lists exactly the registers live at the header (`E[%1 := …, %2 := …]` over a
free `E`); `run_from` matches it against the goal's env and leaves what it cannot read off as
goals (above: `BitVec.ofNat` arithmetic).

Mistakes:
- The warning "the lemma does not apply to the state `S`, so `S` is substituted": the lemma is
  stated over a state term that differs from `S`'s; restate it over a free `S` (or over the shape
  the steps leave, `{ S with mem := … }`), or ignore it when `S` must be substituted (an
  induction hypothesis about a fixed state).
- Listing a dead register in the header's env: the goal's sealed env no longer has it, so its
  read goal cannot close. List only live registers.
- A `local macro` for a repeated loop body placed between theorems: it waits for every proof
  above it. Define all proof macros before the first theorem.

## 10. Repeated instruction runs: `step_pattern`

When the same instruction sequence recurs (an inlined helper), state it once as a list of
instructions over register variables and prove a pattern lemma; each site is one step:

```lean
-- Avx512/FoldUnsigned.lean
theorem runBodyFrom_foldRun {blk : BasicBlock Γ tRets bp} {E : ⟪Γ⟫} {pos : Nat}
    {x m s p k a b c r : Dst Γ V} {rest : List (Instr Γ)} {X : Vector (BitVec 64) 8}
    {S : GlobalState} {g : ⟪Γ⟫ × GlobalState → PoisonOr β} {K : PoisonOr β}
    (hbody : blk.body.drop pos = foldRun x m s p k a b c r ++ rest)
    (hR : E ⊨ [x := X, m := foldMask, s := foldShifts, k := foldK])
    (hd : [x.i, s.i, k.i, a.i, b.i, c.i].Nodup)
    (hK : ∀ va vb vc : ⟦V⟧,
        (blk.runBodyFrom E[a := va, b := vb, c := vc, r := Ty.wrap (fold X)] (pos + 4) S >>= g) = K) :
    (blk.runBodyFrom E pos S >>= g) = K := by
  step_pure with transparent va
  …

-- Avx512/fd_r43x6_pow22523_2.lean
  step_pattern using runBodyFrom_foldRun with z2a
```

Mistakes:
- Constants the pattern reads (`m := foldMask`) must be in the env as the same literal: keep their
  `step_pure`s inline, or label the constant `@[mlir_const]`. A pattern that builds such a
  constant (`vecRun`) steps `inline` for the same reason: named `vN`, reads of it give `vN`.
- A `Nodup` premise over registers the site does not keep apart fails by `decide`: the pattern
  does not fit that site.
- `with x` names a value the pattern computes; values the continuation binds (`∀ A' E', …`) are
  named by `with a e`, in order, and stay folded (their equations among the binders too). An
  anonymous fact the continuation binds is named after the value it equates (`ha`) or its
  predicate (`htablePhase`).
- A continuation that binds a state (`∀ S', P S' → (blk.runBodyFrom E' pos' S' >>= g) = K`) gives a
  fresh state: by its equation among the binders (`S' = t`) as after a step, else bare, the old
  state's facts dropped and the continuation's kept about the new `S`.
- In a macro, annotate antiquotations after `step_pattern using lem` (`$t:num`, `with $a:ident`):
  a bare `$t` also matches the `inline`/`named`/`transparent` keywords and misparses.

**Unrolled loops.** A loop the compiler unrolls (a Zig `inline for`, an unrolled C loop) is one
long block. Steps read the instruction off a body fact the steps carry (hidden, made at a concrete
block's first step), so a step costs the same at any position and `finish_block` works at any
length; still, prove one iteration as a pattern and step each with it
(`Zig/Sha512_round.lean`: 75 of 80 rounds one 26-instruction pattern). Finding the template:
- Cut the block at an instruction each iteration has once (the load of its word), write each run
  with registers relative to its start, and group equal runs. LLVM interleaves iterations: pick
  the cut whose runs read only registers written before them.
- What varies is a parameter: a constant's register (`k : Dst Γ (.bv 64)`), a `gepConst` offset
  (`off : Nat`). The first and last iterations often differ (scheduling, the stores after the
  loop): keep their steps, or give them their own patterns.
- A memory read in the run: the read and its fit are premises (`hfit : Fits S.mem (Wp.add
  (BitVec.ofNat 64 off)) 64`, `hload : S.mem.readAt (Wp.add (BitVec.ofNat 64 off)) 64 = Wt`),
  closed at the site from the context (`have hw := hW t (by decide)` before the step).
- The conclusion relates the run to the spec's step (`Sha512.round #v[A, …] Kt Wt = #v[A', A, …]`),
  so the site chains iterations by rewriting.

Any position works: the pattern reads the instructions at the position off the block, as a step
reads one, and takes the registers' type proofs from them. State registers past the first few
hundred as `rir_reg% X.hty k`, not `%k`, which decides `Γ.ty k` by unfolding `Γ` to it.

## 11. After the last block

The goal is `.value (rets, S) = .value (rets', s')` with `hS` in context. In order of preference:

1. `simp [hS]` (or `rw [hS]`) and `rfl`, when the spec is written in the steps' shape;
2. `subst_vars` then `simp [read/store lemmas, *]`;
3. `rw [hS, spec]; congr` and lane/limb goals by `simp [*]` or `bv_decide`.

Framed functions add `erase_frame` (or `simp [mlir_frame, *]`). `clear_reads` (a project tactic)
before `subst_vars` keeps `subst` from rewriting values by their read facts.
