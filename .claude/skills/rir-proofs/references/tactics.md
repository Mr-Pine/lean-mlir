# RIR tactics: technical reference

Source: `MLIR/Run/Tactic/**`. Import `MLIR.Run.Tactic`. For when to use what, see `tactics-guide.md`.

## The proof state the tactics maintain

A function proof runs through three goal shapes:

| Shape | Produced by |
| --- | --- |
| `f.call args s = R` | the theorem statement |
| `f.runFrom E k S = K`, or `(f.runFrom E k S >>= g) = K` for a framed function | `func_init`, a jump in `finish_block`, `step_loop`'s continuation |
| `(do let x ← blk.runBodyFrom E pos S; …) = K` | `block_init`, every step |

Between steps the context has this shape (example after three steps of `fiat_25519_add`):

```
S₀ : GlobalState                          -- the entry state
S : GlobalState                           -- the current state
hS : S = { alloc := S₀.alloc, mem := S₀.mem.storeAt out (…) }   -- always over S₀
hwf : S.WF                                -- facts about the state are about S
hout : S.mem.LimbsFit out
hread_out : S.mem.readAt out 64 = …       -- what the stores wrote, read back
E₀ E : ⟪fiat_25519_add.Γ⟫
hArgs : E.args = (fiat_25519_add.args (.value out) (.value x) (.value y)).get
hE : E = E₀[%7 := .value (…), %23 := .value (out.add 8#64)]    -- live writes only
a : BitVec 64
ha : a = S₀.mem.readAt y 64               -- a named value
```

- **Env sealing.** After every step `E` is a fresh local with `hE : E = E₀[…]` holding only the
  writes some later instruction reads (in this block or a block reachable from it) and no later
  write in the chain overwrites. Dead writes move into the new root `E₀`, and a value nothing else
  mentions is cleared with its equation.
  Before the first step the args fact is `hEargs`; from then on it is `hArgs`.
- **State sealing.** Every effectful step leaves one state local `S` with `hS : S = <term over
  S₀>` (the previous state is substituted away). Facts about the old `S` are restated about the
  new one, by the context's facts, the `mlir_transport` lemmas (their `≠`/disjointness premises
  also by `mem_fact`'s searches) and the context's implications; one that cannot be carried
  becomes a **new goal before the main goal**, named after the fact (a consumed one is cleared
  instead; an equation, like `hm : S.mem.eraseFrom b = m`, stays about the previous state, where
  it holds, and the sealing substitutes that state's term into it).
- **Folded values.** A value named with `with x` (or `named`) is *tagged*: later steps, the state
  and `finish_block` keep `x` and never unfold `hx`. Default names (a load's `vN`) and
  `transparent` names are untagged and unfold into later values.

### Resolving a step's value

Every step simplifies the value it writes (or the operation it runs) in passes:

1. argument reads `E.read %argk`, by `hArgs` (before the env is first sealed, by the args fact of
   its write chain's root: a block lemma's `hArgs : E.args = …`);
2. register reads, through `hE` chains (`readThroughWrites`: one definitional step per run of
   writes, the written values never walked) and local read facts `E.read r = v` (also as
   `E ⊨ [r := v, …]` conjunctions);
3. the `mlir_env` and `mlir_operation` simp sets, the default simp set (unless `only`), the
   step's simp args, and the equations of the locals the value mentions (the state `S`, unnamed
   values), except tagged names and stack slots; with `opaque`, only the state's;
4. vector lanes `#v[.value x, …]` to `Ty.wrap #v[x, …]`; literal vectors equal to an `mlir_const`
   constant become that constant.

Simprocs in these passes: `gepValue` (`gep (.value off) (.value p)` to `.value (p.add off)` when
`p.offset + off` provably does not wrap: by the offsets' facts, a no-overflow fact
`¬p.offset.uaddOverflow c` for a literal `c ≥ off`, or `omega` with the offsets' values
(`x.offset = 0`) in, a `% 2 ^ 64` it shows is below the modulus dropped first: a symbolic index
from a block's start or a bounded multiple `192 * k` with `k < 8` needs no lemma), and the memory
simprocs (a read `S.mem.readAt p w` by a read fact, through `hS`'s stores by the `mlir_read`
lemmas, or inside a wider known read). Side conditions are discharged by `decide`, then from the
facts (`mem_fact`'s search; `Fits` and `WF` below `alloca`s and new blocks built layer by layer
from the entry state's facts, so reads below a frame resolve without read facts of the inputs).

Vector simprocs (`mlir_operation`, which every pass runs; elsewhere `simp [mlir_operation]`): a
literal `#v[…]`'s lane at a literal index is that lane, and any vector's lane at `⟨k, _⟩`,
`↑⟨k, _⟩` or `(k : Fin n)` is `v[k]`; `shufflevector` with a literal mask and `bitcast` between
vectors step straight to their lanes. A `shufflevector` by a mask with locals (a pattern's parameter
`m`) stays folded, for a lemma `Operation.shufflevector m (Ty.wrap x) y = …` as a simp arg; one by
another closed mask unfolds to its `ofFn` after its operands. A bitcast lane is `poisonIf (bitcastPoison x w w' k) …`: the
test reduces to the overlapping lanes' `x[i].isPoison` once `x`'s reads resolve, and
`(packLanes v).extractLsb' s w` at a literal `s` to `v[i]`, its slice, or
`v[i + m - 1] ++ … ++ v[i]`. No `Fin.exists_fin_succ` or byte lemmas are needed; `expandOfFn` still
splits the other `Vector.ofFn` lanes, `expandZipWith` a vector operation's `zipWith` where
`zipWith_eq_ofFn` is erased (pass the lanes' no-overflow facts with it). Lemmas over a vector
operation (`Vector.zipWith (Operation.and (w := 64)) (Ty.wrap x) (Ty.wrap y) = Ty.wrap (f x y)`)
fire as simp args or `local mlir_operation` lemmas. A lane at a literal `k` gets its bound by
`decide` (`x[0]'h` with another proof too, so `simp only [reduceGetElemLit]` before `bv_decide`
gives it one atom); `x[3]` written in a proof takes its bound by `decide`, never by searching the
context.

## Step options

Every step takes some of these, in this order:

```
step_xxx [opaque] [only] [simp args] [names] [consuming h₁ h₂ …]
```

| Option | Meaning |
| --- | --- |
| `[h, lem, ← lem']` | extra simp lemmas for resolving the value (as for `simp`) |
| `only` | drop the default simp set; `mlir_env`/`mlir_operation` still run |
| `opaque` | don't unfold unnamed locals the value reads (`step_pure` only) |
| `inline` | keep the value in the env; no local |
| `named` | name it `vN` (`N` = destination register), equation `hvN`, tagged |
| `named transparent` | `vN`/`hvN`, untagged |
| `with x` | name it `x`, equation `hx`, tagged |
| `with x h` | name it `x`, equation `h` |
| `with transparent x` | name it `x`, untagged |
| `consuming h₁ …` | clear these facts after the step: carried only if two transport lemmas do it, never a goal; a name may be the step's own read-back |

Defaults: `step_pure`, `step_call` inline; `step_load`, `step_alloca`, `step_addressof`,
`step_pattern` name `vN` untagged. A value that is already a local is never renamed. Only the
`x` of `.value x` / `Ty.wrap x` is named, so `x : BitVec 64`, not a `PoisonOr`.

## Tactics

### `func_init`

`f.call args s = R` → `f.runFrom E ⟨0, _⟩ S = R'`.

- Tries the frame-free form first: `Func.call_eq_of_run_eq` needs `R`'s state to be WF by
  `simp [mlir_mem, *]` and its `alloc` to be `s.alloc` by `rfl`. Otherwise it rewrites with
  `Func.call_eq_run_bind` (framed): the goal keeps a bind `>>= fun p => .value (p.1, { p.2 with
  mem := p.2.mem.eraseFrom S₀.alloc.nextFreeBlock })`, closed at the end by `erase_frame`.
- Leaves `S₀ S`, `hS : S = S₀`, every hypothesis about `s` restated about `S` (`hwf : S.WF`, …),
  `R` restated about `S₀`, `E₀ E`, `hE : E = E₀`, `hEargs : E.args = (f.args …).get`; framed
  also `hwf₀ : S₀.WF` and each `h : Fits S.mem p w` as `h₀` about `S₀` (an object predicate's
  top-level `Fits` conjuncts as `h₀`, `h₀_1`, …: `QuadFit`'s three): `erase_frame` needs `hwf₀`,
  and reads through `hS` below the frame's `alloca`s and globals need the `Fits`.
- Fails with "`func_init` expects a goal `f.call args s = _`" on any other goal.

### `block_init`

`f.runFrom E k S = K` (or `… >>= g = K`) → `(do let x ← (f.blocks k).runBodyFrom E 0 S; …) = K`.
Unfolds reducible definitions at the env's head and at its write chain's root, so a loop
header's `abbrev hdr … E i := E[…]` exposes its writes. Use after `func_init`, after each jump,
and at the start of a loop or pattern lemma about a block.

### `step_pure [opaque] [only] [args] [names]`

One pure instruction (constant, arithmetic, compare, `select`, `gep`, casts, vector ops,
`lifetime.start/end`). Fails at the instruction goal (`rfl` after `dsimp [mlir_instr]`) when the
instruction is effectful. A `gep` whose no-wrap cannot be shown stays `Operation.gep …`; a flagged
operation (`add nsw`, `shl nuw`, …) whose overflow test does not simplify stays an
`if … then .poison else …` (pass the no-overflow lemma as a simp arg).

### `step_load [only] [args] [names] [consuming …]`

`%k = load p`. Needs `p` as `.value q` (else: "operand … is not known to be `.value _`; it may
be poison") and `Fits S.mem q w` by `mem_fact`, else `simp_all`. The loaded value is
`S₀.mem.readAt q w` as the memory simprocs resolve it (a stored value, or a read of `S₀`).

### `step_store [only] [args] [consuming …]`

`store v, p`. Needs `p` and `v` as `.value _`, `Fits S.mem q w`, and `v`'s bits by
`dsimp; try simp; rfl` (fails when the value is still an `if`/poison). New facts:
`hread_<p> : S.mem.readAt p w = v` for a local pointer `p`, `hread_<p>_<k>` for `p.add k#64`,
else `hread`; of several read-backs at one pointer (an object's and its first field's) the last
keeps the name, the others take their read's (`hread_r_readAt`). A stored value that is itself a
read with a fact (a callee's `s.mem.readQuad a`) is read back too. Read facts of the old state
that the store misses are carried; one it overwrites, or may overwrite (no `mlir_read` lemma's side
conditions hold: possible aliasing), is dropped; `set_option trace.rir true` names each dropped
fact.

### `step_memcpy [only] [args] [consuming …]` / `step_memset …`

`memcpy(dst, src, len)`: `len.toNat = n` by `rfl`, `Range.Disjoint` of the two ranges, `Fits` of
both, each by `mem_fact` else `simp_all`; the new memory stores `S.mem.readAt src (8 * n)` at
`dst`. `memset(dst, val, len)`: `Fits` of `dst`; the new memory stores `val.replicate n`.

### `step_call using thm [only] [args] [names] [consuming …]`

`%r = call @f(args)`. `thm` (a constant or a term: `fd_f25519_set.call_eq`, `hspec.1`) must
conclude `f.call args s = .value (rets, s')`; it is applied with `apply`, and each premise is
closed by `mem_fact`, else `simp [mlir_mem, *]`. Results are written with `writeMany`, unfolded
into single writes; a `void` call writes nothing. The new state `s'` is sealed like a store's, so
facts must transport through the shape `s'` has (register `mlir_transport` lemmas for it, or
have an implication `hpost : ∀ s, s.WF → (post s).WF` in context).

### `step_alloca [names] [consuming …]`

`%k = alloca n`. Needs `S.WF`. Before allocating, every local pointer `q` with a `Fits S.mem q w`
fact (a conjunct of one counts) gets `h<q>_ne : q.id ≠ S.allocaPtr.id`. After: the slot `x`
(default `vN`) with tagged `hx : x = b.slot k`, `h<x>_fits : Fits S.mem x (8 * n)`,
`h<x>_off : x.offset = 0` (`hv6_fits`, `hv6_off` for `%6`); facts that mentioned `allocaPtr`
are restated about `x` and named `<fact>_<x>`. Slots of one state are told apart by index
(`GlobalState.slot_id_ne`).

### `step_addressof hv [names] [consuming …]`

`%k = llvm.mlir.addressof @g`. `hv : ∀ s, g.value s = .value (Ty.wrap r, s)` (proved by
`GlobalInitializer.compute_value _ _ ⟨_, by with_unfolding_all rfl⟩`). Like `step_alloca`, and
the new block holds `r`'s bits: `hread_<x> : S.mem.readAt x w = Ty.flatBits …`.

### `step_pattern using h [names]`

Steps a run of instructions with a pattern lemma proved once over registers. `h` concludes
`(blk.runBodyFrom E pos S >>= g) = K` and has:

- a body fact `blk.body.drop pos = pat … ++ rest`: closed by unfolding, or inside another pattern
  lemma's proof (an abstract block) by its body fact, carried past the pattern; it fixes the
  registers, and fails ("the body at the position is not the pattern of …") when the instructions
  differ;
- reads `E.read r = v` (or `E ⊨ […]`, also as an `abbrev Holds E … := E ⊨ […]`): closed through
  the env's writes, locals' equations unfolded if needed, an outer pattern's registers by the step
  passes ("no value for the read …; add a fact `h : E.read %k = _`" when none);
- decidable side conditions (`[r₁.i, …].Nodup`, flags `C = 0 ∨ C = 1`): from the facts, else
  `decide` ("side condition false or undecidable");
- a continuation `∀ …, (blk.runBodyFrom E' pos' S >>= g) = K`: entered; its last write is named
  per `[names]` (an abstract register's after its variable: `vy` for `y`), the pattern's dead
  intermediates are cleared, and a pattern that stores has its new state sealed.

A pointer operand may be any register `p : Reg Γ .ptr` (an argument at one site, a value at
another), with `hp : E.read p = .value P`: its reads pass writes of other types, and a write of a
pointer register `q` given a premise `p ≠ .val q.i q.h` (`decide` closes it at the site).

Pass implicit arguments the goal does not fix by name: `step_pattern using lem (B := 0x100000#64)`.
`[names]` follow the arguments: `step_pattern using lem 1 0 2 3 inline` (`inline`/`named` end them).

### `step_loop using h`

Closes `f.runFrom E k S = K` (or `… >>= g = K`) with a loop lemma, a block lemma, an induction
hypothesis or a continuation hypothesis `hK`. `h`'s env is a write chain over a free base: the base
becomes `E`, each write a goal `E.read r = v`. Then:

- reads are closed through `E`'s writes, the rest of them by `rfl`; what is left, and `h`'s other
  premises, by `with_reducible assumption`, `omega`, `mem_fact`, or `simp [*, mlir_env, gepValue]`
  (a premise about a run is only tried by `assumption`); what remains stays open;
- a continuation premise `∀ E', E'.args = … → runFrom … = K` is entered as the **last** goal: `E₀`
  and `hArgs₀` introduced (binders between them, a state `S'`, under their own names), the env
  sealed, the state simplified and named `S` as after a step.

If `h` does not apply to the state `S` as is, `S` is substituted by its definition and the lemma
retried, with a warning (none when `h` is about a fixed state, e.g. an induction hypothesis).

### `finish_block [only] [args]`

At the end of a block's body ("`finish_block`: instructions left at position N" otherwise).

- `return`: resolves the returned registers; the goal becomes `.value (vals, S) = K` (framed: the
  erase bind still around it).
- `br`/`cond_br`/`switch`: resolves the condition and the jump's arguments; a literal condition,
  or one a local `c` or `¬c` (`a ≠ b`) decides, takes its branch; otherwise one goal per target.
  A `cond_br` gives `isTrue` (`hbr : c`) and `isFalse` (`hbr : ¬c`); a `switch` is an `if` chain,
  so its goals are `isTrue`, `isFalse.isTrue`, …, and the default `isFalse.….isFalse` gets every
  negation as `hbr0`, `hbr1`, …. Each goal is `f.runFrom E k S = K` with the target's parameters
  written into a sealed `E`.

### `erase_frame`

Closes or simplifies the end of a framed proof: `simp` with the `mlir_erase` lemmas (writes into
blocks from the frame's counter on are dropped, `eraseFrom` moves past writes below it), side
goals `n ≤ _` by `assumption` or `slot_bound`; then `GlobalState.WF.eraseFrom`. Run it after
`subst hS` / `simp [hS]`, when the goal is the final state equation.

### `slot_bound`

`n ≤ x.id.id` and similar counter bounds: unfolds `allocaPtr`, `slot`, `alloca` and the named
slots' equations (`hx : x = b.slot k`), then `omega`.

### `mem_fact`

Closes a side condition from the context: a local up to reducible unfolding; `decide` on closed
facts after replacing pointer offsets by their facts (`x.offset = 0`); `Fits` (same pointer and
width, a wider literal width by `Fits.mono`, `q.add off` inside `q` by `Fits.add_of_le`, through
`storeAt`); `Range.Disjoint` (distinct ids, else offsets by `omega`); `≠` of block ids (facts,
either way round, `List.Nodup` literals, distinct slots, `decide`); then the `mlir_transport`
lemmas two deep from the facts as they are (an object fact's projections), then, with `S`
substituted by `hS`, 64 deep; a lemma's `≠`/disjointness premises also by the searches above.
"`mem_fact`: not from the facts" when all fail.

### `env_reads`

Closes `E.read r = v` or `E ⊨ [r := v, …]` through `E`'s writes, as `step_loop` closes its read
premises; what remains by `rfl`, else left open.

### Internal tactics

`extract_state`, `extract_env` (parts of `func_init`), `seal`, `seal_env` (the sealing after a
step), `expect_values`, `addressof_value`, `step_impure … => tac` (a step closed by your own
tactic; the specific steps above are instances). Use them only to debug a step.

## Attributes

| Attribute | Kind | Used by | Register |
| --- | --- | --- | --- |
| `mlir_mem` | simp set | `func_init` (WF), `step_call` premises | unfolding of fit predicates (`LimbsFit`), WF through writes |
| `mlir_state` | simp set | state sealing (also on `hS` once substituted) | reads of your own read functions through your writes; a write merged with the one below it (`(m.storeAt p u).storeAt (p.add k) y = …`) |
| `mlir_frame` | simp set | `simp [mlir_frame, *]` at the end of a framed proof | `eraseFrom` past writes, reads through `alloca` |
| `mlir_erase` | simp set | `erase_frame` | `eraseFrom` past a write; a write into an erased block dropped |
| `mlir_env`, `mlir_operation`, `mlir_instr`, `mlir_effect` | simp sets | value resolution | framework only |
| `mlir_transport` | label | carrying facts to a new state | `h : P s → P s'` for each fact predicate and state shape |
| `mlir_read` | label | read facts after writes, reads through `hS` | `read (write m q x) p = x` (back) and `= read m p` (past), with side conditions |
| `mlir_fresh` | label | a new block's `Fits` after an allocating step | `Fits m p w` for an allocating write `m` |
| `mlir_const` | label | value resolution | a constant whose literal value should print as its name |

A read lemma's left side must be `read (write …) …` with both heads constants: the tactics index
the lemmas by those two heads.

## Debugging aids

- The infoview shows an **Instructions** panel with the instruction at the goal's position and
  the next one.
- `set_option pp.deepTerms false` / `pp.oneline true` keep big goals readable.
