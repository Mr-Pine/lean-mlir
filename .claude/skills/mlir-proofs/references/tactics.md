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

- **Body facts.** A step on a concrete block reads its instruction off a hidden local
  `blk.body.drop pos = x :: xs` (made at the block's first step, carried one instruction on per
  step, as an abstract block's visible `hbody`), so the kernel's check of a step does not walk the
  body: a step costs the same at any position.
- **Deep states (`set_option rir.stateDepth n`, default `0`: off).** Before a `step_call` whose
  state term is deeper than `n`, `S` becomes a bare base (`hS✝ : … = S`), the call's state built on
  it; reads stop at the base. `finish_block` at a `return` substitutes the bases back (and resolves
  the values' reads of them), so the end state is over `S₀`. For long chains of calls over a
  growing frame (Agave `decompress`, `sqrt_ratio_i`: `64`).

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

A flag's overflow test on literals (`(0#64).saddOverflow 1#64`, `umulOverflow`, …) evaluates
(default simprocs), so an `nsw`/`nuw` operation on constants needs no lemma.

Simprocs in these passes: `gepDynValue` (a dynamic `gep` by a value index: without `nusw` its
unsigned reading `gep f (byteOff + i.toNat * stride)`, `gep f i` for byte strides; with `nusw` the
unsigned `gep { nuw := true } …` where the offset is provably below `2 ^ 63` (from the facts or the
step's simp arguments: pass a bound such as `hlt : i.toNat * 8 < 2 ^ 63`), else, when that `gep`
is poison, `gepSigned` of the signed index, which `gepSignedValue` resolves from the offsets'
facts: a `gep` back by a negative index; unresolved, left for a later pass), `gepValue` (`gep f
(.value off) (.value p)` to `.value (p.add off)`: at once without flags; for `nuw`/`nusw` when
`p.offset + off` provably does not wrap (for `nusw` also `off.toNat < 2 ^ 63`, by `decide` for a
literal): by the offsets' facts, a no-overflow fact `¬p.offset.uaddOverflow c` for a literal
`c ≥ off`, or `omega` with the offsets' values (`x.offset = 0`) in, a `% 2 ^ 64` it shows is below
the modulus dropped first: a symbolic index from a block's start or a bounded multiple `192 * k`
with `k < 8` needs no lemma), and the memory simprocs (a read `S.mem.readAt p w` by a read fact,
through `hS`'s stores by the `mlir_read` lemmas, or inside a wider known read). Side conditions are discharged by `decide`, then from the
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
| `with x` | name it `x`, equation `hx`, tagged (an error if `hx` names another fact; an earlier `x`'s may be shadowed) |
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
  also `hwf₀ : S₀.WF` and each `h : Fits S.mem p w` (or `Room`, `InBounds`) as `h₀` about `S₀`
  (an object predicate's top-level such conjuncts as `h₀`, `h₀_1`, …: `QuadFit`'s three):
  `erase_frame` needs `hwf₀`, and reads through `hS` below the frame's `alloca`s and globals need
  them.
- Fails with "`func_init` expects a goal `f.call args s = _`" on any other goal.

### `block_init`

`f.runFrom E k S = K` (or `… >>= g = K`) → `(do let x ← (f.blocks k).runBodyFrom E 0 S; …) = K`.
Unfolds reducible definitions at the env's head and at its write chain's root, so a loop
header's `abbrev hdr … E i := E[…]` exposes its writes. Use after `func_init`, after each jump,
and at the start of a loop or pattern lemma about a block.

### `step_pure [opaque] [only] [args] [names]`

One pure instruction (constant, arithmetic, compare, `select`, `gep`, casts, vector ops). On a
`lifetime.start`/`lifetime.end` it steps as `step_lifetime`, on an `assume` as `step_assume`; a
`ptrtoaddr`/`ptrtoint` reads the state's unconstrained block addresses, its value
`S.mem.addr q.id + q.offset` (truncated or extended), the state unchanged (`run_ptrtoaddr`). Fails
at the instruction goal (`rfl` after `dsimp [mlir_instr]`) when the instruction is effectful. A `gep` whose no-wrap cannot be shown stays `Operation.gep …`; a flagged
operation (`add nsw`, `shl nuw`, …) whose overflow test does not simplify stays an
`if … then .poison else …` (pass the no-overflow lemma as a simp arg).

### `step_load [only] [args] [names] [consuming …]`

`%k = load p`. Needs `p` as `.value q` (else: "operand … is not known to be `.value _`; it may
be poison") and `Fits S.mem q w` (the `w` bits known: live, in bounds, defined) by `mem_fact`,
else `simp_all`. The loaded value is `S₀.mem.readAt q w` as the memory simprocs resolve it (a
stored value, or a read of `S₀`). A load of bits not known to be defined (an uninitialized slot,
a dead object, a struct's padding) is poison: no `Fits`, the step fails. A load of a pointer
(`run_loadPtr`) needs `InBounds S.mem q 64`; its value is `S.mem.loadPtr q`, the pointer stored at
`q` while its 64 bits stay undefined (a store over any of them, `lifetime.start`, drops it), by a
read fact `hread_<q> : S.mem.loadPtr q = .value p` (`step_store`'s, or the theorem's).

### `step_store [only] [args] [consuming …]`

`store v, p`. Needs `p` and `v` as `.value _`, `Room S.mem q w` (live, in bounds: a `Fits` fact
gives it), `v`'s bits by `dsimp; try simp; rfl` (fails when the value is still an `if`/poison),
and its type without padding by `decide` (`run_store`; a padded struct or a value with poison
leaves stores partly undefined bits, `run_storeDef`, which no step takes). A pointer
(`run_storePtr`, `Room S.mem q 64`) stores undefined bits and records the pointer:
`hread_<q> : S.mem.loadPtr q = .value p`. New facts:
`hfits_<p> : Fits S.mem p w` (the stored bits are known; named as the read-backs) unless a `Fits`
fact says it already;
`hread_<p> : S.mem.readAt p w = v` for a local pointer `p`, `hread_<p>_<k>` for `p.add k#64`,
else `hread`; of several read-backs at one pointer (an object's and its first field's) the last
keeps the name, the others take their read's (`hread_r_readAt`). A stored value that is itself a
read with a fact (a callee's `s.mem.readQuad a`) is read back too. Read facts of the old state
that the store misses are carried; one it overwrites, or may overwrite (no `mlir_read` lemma's side
conditions hold: possible aliasing), is dropped; `set_option trace.rir true` names each dropped
fact.

### `step_memcpy [only] [args] [consuming …]` / `step_memmove …` / `step_memset …`

`memcpy(dst, src, len)`: `len.toNat = n` by `rfl` (`n` a numeral for a literal `len`), `Range.Disjoint`
of the two ranges, `Room` of `dst` and `Fits` of `src`, each by `mem_fact` (no fallback); the new
memory stores
`S.mem.readAt src (8 * n)` at `dst` (`run_memcpy`). A source only partly known (`Room`, with
`Fits` of sub-ranges: a flag and an undefined tail) is copied with its definedness (`run_memcpyDef`,
`S.mem.storeDef dst (S.mem.readAt src _) (S.mem.definedAt src _)`): each `Fits` fact of `src` or
`src.add k` gives `hfits_<dst>(_k)` of the copy, and its reads are the source's
(`readAt_storeDef_readAt_add`). `memmove`: the same without `Range.Disjoint` (`run_memmove`,
`run_memmoveDef`).
`memset(dst, val, len)`: `Room` of `dst`; the new memory stores `val.replicate n`. A volatile one
steps as the plain one.

### `step_lifetime [only] [args]`

`lifetime.start p` / `lifetime.end p` (also by `step_pure`). The new memory is
`S.mem.lifetimeStart q` / `S.mem.lifetimeEnd q` (a poison `p`: unchanged). After a start the
object is live and undefined: `hroom_<q> : Room S.mem q w` from its `InBounds`/`Room` fact; after an
end, dead. Facts mentioning `q` (or the slot it names) that the marker does not carry two lemmas
deep (its `Fits`, `Room`, object predicates) are dropped, traced by `trace.rir`, without a deep
search; read facts are carried (the bits stay). Other objects' facts carry with `q.id ≠ _`
(`step_alloca`'s `h<q>_ne`, distinct slots, the blocks' order); one that does not carry is dropped,
not a goal. An operand the env does not hold is an error ("its pointer operand is not known").

### `step_assume [only] [args]`

`assume c` (also by `step_pure`): `c` must resolve, with the simp arguments, to `.value 1#1`
(`run_assume`); the state is unchanged.

### `step_call using thm [only] [args] [names] [consuming …]`

`%r = call @f(args)`. `thm` (a constant or a term: `fd_f25519_set.call_eq`, `hspec.1`) must
conclude `f.call args s = .value (rets, s')`; it is applied with `apply`, and each premise is
closed by `mem_fact`, else `simp [mlir_mem, *]`. Results are written with `writeMany`, unfolded
into single writes; a `void` call writes nothing. The new state `s'` is sealed like a store's, so
facts must transport through the shape `s'` has (register `mlir_transport` lemmas for it, or
have an implication `hpost : ∀ s, s.WF → (post s).WF` in context).

An unbound call of a library function steps with its lemma: `Operation.bcmp_eq` and
`Operation.memcmp_eq` (`Fits` of both ranges; the result is `bcmpResult`/`memcmpResult` of
`S.mem.unspec`, `0` iff the bytes are equal: `bcmpResult_eq_zero_iff`, `bcmpResult_self`),
`Operation.explicitBzero_eq`, `Operation.explicitBzeroChk_eq` (`Room`; zeros stored).

### `step_alloca [names] [consuming …]`

`%k = alloca n`. Needs `S.WF`. Before allocating, every local pointer `q` with a `Fits`, `Room`
or `InBounds` fact about `S.mem` (a conjunct of one counts) gets `h<q>_ne : q.id ≠ S.allocaPtr.id`.
After: the slot `x` (default `vN`) with tagged `hx : x = b.slot k`, `h<x>_room : Room S.mem x
(8 * n)` (its bits undefined: no `Fits` until stored), or for an `alloca` with lifetime markers
(`alloca … true`, dead until `lifetime.start`) `h<x>_bounds : InBounds S.mem x (8 * n)`, and
`h<x>_off : x.offset = 0` (`hv6_room`, `hv6_off` for `%6`); facts that mentioned `allocaPtr`
are restated about `x` and named `<fact>_<x>`. Slots of one state are told apart by index
(`GlobalState.slot_id_ne`).

### `step_addressof hv [names] [consuming …]`

`%k = llvm.mlir.addressof @g`. Every pointer with a memory fact, named slots included, gets
`h<q>_ne` first, so the earlier globals' facts carry past this block's masked store. `hv : ∀ s, g.value s = .value (Ty.wrap r, s)` (proved by
`GlobalInitializer.compute_value _ _ ⟨_, by with_unfolding_all rfl⟩`), `g`'s type without
pointers and padding (by the kernel). Like `step_alloca`, and the new block holds `r`'s bits:
`h<x>_room` for its bytes, `h<x>_fits : Fits S.mem x w`, `hread_<x> : S.mem.readAt x w = Ty.flatBits
…`. A global with `undef` members (or pointer members, which a folded initializer holds undefined)
has `hv : ∀ s, g.value s = .value (v, s)` for its value `v` with poison leaves
(`(.value 7, .poison)`), or `hv` is the global `g` itself: its value is read off its block and `hv`
left to the kernel. The block stores `v`'s bits masked by their definedness, both literals the
kernel evaluates (`run_addressof_def`, `Ty.flattenDef_eq_ofNat`: seconds for a 21504-bit table);
`h<x>_room`, `h<x>_fits(_k) : Fits S.mem (x.add k) w` for each run of defined bits from a byte (the
mask's bits checked by the kernel, no `exponentiation.threshold`), `hread_<x>` of all the bits.

### `step_pattern using h [names]`

Steps a run of instructions with a pattern lemma proved once over registers. `h` concludes
`(blk.runBodyFrom E pos S >>= g) = K` and has:

- a body fact `blk.body.drop pos = pat … ++ rest`: from the body fact the steps carry (a concrete
  block's, or inside another pattern lemma's proof an abstract block's), carried past the pattern;
  it fixes the registers, and fails ("the body at the position is not the pattern of …") when the
  instructions differ;
- reads `E.read r = v` (or `E ⊨ […]`, also as an `abbrev Holds E … := E ⊨ […]`): closed through
  the env's writes, locals' equations unfolded if needed, an outer pattern's registers by the step
  passes ("no value for the read …; add a fact `h : E.read %k = _`" when none);
- decidable side conditions (`[r₁.i, …].Nodup`, flags `C = 0 ∨ C = 1`): from the facts, else
  `decide` ("side condition false or undecidable");
- a continuation `∀ …, (blk.runBodyFrom E' pos' S >>= g) = K`: entered; its last write is named
  per `[names]` (an abstract register's after its variable: `vy` for `y`), the pattern's dead
  intermediates are cleared, and a pattern that stores has its new state sealed. Values it binds
  (`∀ A' E' : BitVec 64, …`) are named by `with a e`, in order, folded; anonymous facts it binds
  after the value they equate (`ha`) or their predicate (`htablePhase`). A state it binds is the new
  state: by its equation among the binders (`S' = t`), else bare (the old state's facts dropped,
  the continuation's about `S`).

A pointer operand may be any register `p : Reg Γ .ptr` (an argument at one site, a value at
another), with `hp : E.read p = .value P`: its reads pass writes of other types, and a write of a
pointer register `q` given a premise `p ≠ .val q.i q.h` (`decide` closes it at the site).

Pass implicit arguments the goal does not fix by name: `step_pattern using lem (B := 0x100000#64)`.
`[names]` follow the arguments: `step_pattern using lem 1 0 2 3 inline` (`inline`/`named` end them).

### `step_loop using h`

Closes `f.runFrom E k S = K` (or `… >>= g = K`) with a loop lemma, a block lemma, an induction
hypothesis or a continuation hypothesis `hK`. `h`'s env is a write chain over a free base: the base
becomes `E`, each write a goal `E.read r = v`. Then:

- reads, also behind an abbreviation (`abbrev Regs E := E ⊨ […]`), are closed through `E`'s
  writes, the rest of them by `rfl`; what is left, and `h`'s other
  premises, by `with_reducible assumption`, `omega`, `mem_fact`, or `simp [*, mlir_env, gepValue]`
  (a premise about a run is only tried by `assumption`); what remains stays open;
- a continuation premise `∀ E', E'.args = … → runFrom … = K` is entered as the **last** goal: `E₀`
  and `hArgs₀` introduced (binders between them, a state `S'`, under their own names), the env
  sealed, the state simplified and named `S` as after a step.

If `h` does not apply to the state `S` as is, `S` is substituted by its definition and the lemma
retried, with a warning (none when `h` is about a fixed state, e.g. an induction hypothesis). A
lemma stated under a bind (`(runFrom … >>= g) = K`) also closes a bare run, `g` being `pure`; its
`by` arguments are elaborated before the continuation is entered.

### `finish_block [only] [args]`

At the end of a block's body ("`finish_block`: instructions left at position N" otherwise), by the
body fact the steps carry (`blk.body.drop pos = []`), at any length.

- `return`: resolves the returned registers; the goal becomes `.value (vals, S) = K` (framed: the
  erase bind still around it).
- `br`/`cond_br`/`switch`: resolves the condition and the jump's arguments; a literal condition,
  or one a local `c` or `¬c` (`a ≠ b`) decides, takes its branch; otherwise one goal per target.
  A `cond_br` gives `isTrue` (`hbr : c`) and `isFalse` (`hbr : ¬c`); a `switch` is an `if` chain,
  so its goals are `isTrue`, `isFalse.isTrue`, …, and the default `isFalse.….isFalse` gets every
  negation as `hbr0`, `hbr1`, …. Each goal is `f.runFrom E k S = K` with the target's parameters
  written into a sealed `E`.

### `folded h₁ …`

The equations `hᵢ : x = e` (premises, `have`s) stay folded as a `with x`'s do: later steps keep `x`
and never rewrite by `hᵢ`. Untagged equations of locals are otherwise unfolded into the values that
mention them.

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
facts after replacing pointer offsets by their facts (`x.offset = 0`); `InBounds`, `Room`, `Fits`,
their widths first as literals (`8 * (40#64).toNat` as `320`) and literal offsets in one spelling
(a fact of that kind or a stronger one, `Fits → Room → InBounds`: same pointer and width, a wider
literal width by `.mono`, `q.add off` inside `q` by `.add_of_le` (a variable `off`, `2 * j` with
`j < 256`, by `omega` from the facts), through `alloca` (a new block's own bounds and room),
`addBlock`, `storeAt` (`Fits` of the stored range, or a range inside it, from `Room`), `storeDef`
(`Fits` where its mask is set or a copy's source is known), lifetime markers, an abbreviated state
(`withT … S`), an object's write `f m …` by its `P.f` transport lemma (`InBounds.storeVec`));
`Range.Disjoint` (distinct ids, else offsets by `omega`); `≠` of block ids (facts, either way
round, `List.Nodup` literals, distinct slots, the blocks' order by `omega` from bounds like
`r.id.id < b`, `b ≤ z.id.id`, a slot's number, a pointer into a `WF` state below its slots,
`decide`); a relation of naturals by `decide`, else `omega` from the facts; then the `mlir_transport`
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
| `mlir_fresh` | label | a step's new facts: a new block's `Room`/`InBounds`, a store's `Fits`, a started object's `Room` | a fact about a write `m` (its first `MemoryState` argument): `Fits m p w`, or an object's (`(m.storeLimbs p l).LimbsFit p` from `m.LimbsRoom p`); tried at each write of the new memory (an abbreviation's too) and carried up through the later ones, so one lemma covers a callee's several outputs; skipped where the old memory's fact carries; a premise with an open width is matched against the facts. An object's fact takes the name of the fact its premise was (`hx_limbs`) and supersedes it, else `h<pred>_<x>` |
| `mlir_const` | label | value resolution | a constant whose literal value should print as its name |

A read lemma's left side must be `read (write …) …` with both heads constants: the tactics index
the lemmas by those two heads.

## Debugging aids

- The infoview shows an **Instructions** panel with the instruction at the goal's position and
  the next one.
- `set_option pp.deepTerms false` / `pp.oneline true` keep big goals readable.
