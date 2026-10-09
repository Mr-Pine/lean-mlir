# lean-mlir limitations, as measured against Firedancer ed25519

Findings from an evaluation of lean-mlir's support for memory operations, calls
and loops, carried out on 2026-08-18 against the `lean-mlir-firedancer-main`
branch (`0fa9bf201`) and `firedancer` at `src/ballet/ed25519`.

Every claim below was reproduced; the reproduction is given inline. Toolchain:
`clang-18`, `mlir-translate-18`, `mlir-opt-19`, Lean toolchain
`leanprover/lean4:nightly-2025-12-01`.

Sections are ordered by how much they cost the ed25519 equivalence proof, not
by severity in the abstract.

**Update (2026-08-24).** Control flow: 5.1/5.3 are now fixed for *forward*
CFGs (`SSA/Projects/SLLVM/Cfg/`), and 3.3 for the single-dynamic-index gep,
in the course of taking the verbatim
`build/native/gcc/mlir/ref/region/fd_f25519_is_zero.mlir` -- 11 blocks,
switch, cond_br chains, a φ, `// pred:` comments and all -- through to a
denoted, `#guard`-tested `Cfg` (`Ref/Mlir/fd_f25519_is_zero.lean`). Later the
same day: CFG-layer *calls* (4.1, `BlockCom.call`), struct-field geps (3.3)
and aggregate allocas (3.4), which together lift the entire ref call graph
under `fd_ed25519_point_is_zero` verbatim -- six regions, one of them
multi-block, bound with `with @f := …` and `#guard`-tested end to end.
Loops stay open; details in each section.

**Update (2026-08-19).** The items marked **FIXED** below have since been
addressed, in the course of taking the *verbatim*
`build/native/gcc/mlir/avx512/region/fd_r43x6_quad_sqr_fast.mlir` -- pointers,
stores and all -- through to a proof. See
`Avx512/Mlir/fd_r43x6_quad_sqr_fast_mem.lean` and
`Avx512/Proof/fd_r43x6_quad_sqr_fast_mem.lean`. The original text of each item
is kept, with the resolution appended, so the measurements stay readable as a
record of what was true on 2026-08-18.

---

## 1. Summary table

| # | Limitation | Layer | Blocks the ed25519 proof? |
|---|---|---|---|
| [2.1](#21-store-never-overwrites) | ~~`store` never overwrites~~ **FIXED** | SLLVM semantics | No |
| [2.2](#22-store-at-a-non-zero-offset-is-discarded) | ~~`store` at non-zero offset is discarded~~ **FIXED** | SLLVM semantics | No |
| [3.1](#31-the-llvm-dialect-has-no-memory-operations) | LLVM dialect has no memory ops | LLVM dialect | Yes, at point layer |
| [3.2](#32-sllvm-op-names-and-operand-order-do-not-match-mlir) | SLLVM op names/operand order ≠ MLIR — **`load`/`store` FIXED**, `alloca` still diverges | SLLVM parser | Only via `alloca`/gep |
| [3.3](#33-no-getelementptr) | ~~No `getelementptr`~~ **FIXED** (dynamic-leading + constant-trailing indices) | SLLVM | Trailing dynamic index only |
| [3.4](#34-alloca-accepts-only-integer-element-types) | `alloca` integer element types only — aggregates **FIXED** | SLLVM | `alloca ptr` only |
| [3.5](#35-loadstore-are-scalar-only) | ~~`load`/`store` are scalar-only~~ **FIXED** | SLLVM | No |
| [3.6](#36-loadpure--storepure--mem-are-unreachable-from-syntax) | `loadPure`/`storePure`/`!mem` unreachable | SLLVM parser | No (blocks future rewrites) |
| [3.7](#37-no-memory-lemmas-proof-automation-stalls) | ~~No memory lemmas; automation stalls~~ **FIXED** | SLLVM | No |
| [3.8](#38-peepholerewrite-cannot-express-a-memory-rewrite) | `PeepholeRewrite` requires pure lhs/rhs | Framework | No (blocks future rewrites) |
| [3.9](#39-memory-refinement-is-degenerate) | Memory refinement is equality (degenerate) | SLLVM | No (limits what is provable) |
| [4.1](#41-calls-are-not-modelled) | Calls are not modelled — CFG-layer calls **FIXED** (`BlockCom.call`) | Framework | `Com`-caller → `Cfg`-callee only |
| [5.1](#51-com-has-no-control-flow) | `Com` has no control flow — CFG layer **FIXED**, back-edges included (nontermination = UB) | Framework | No |
| [5.2](#52-scf-can-only-wrap-a-toy-dialect) | `Scf` only wraps a toy `ℤ` dialect | Scf | Yes, for any loop |
| [5.3](#53-regions-cannot-be-parsed) | ~~Regions cannot be parsed from MLIR~~ **FIXED** for multi-block regions | Parser | Loops only (via 5.1) |
| [6.1](#61-nswnuw-are-reserved-tokens-in-the-edsl) | ~~`nsw`/`nuw` reserved tokens in the EDSL~~ **FIXED** | Parser | No |
| [6.2](#62-the-printer-emits-syntax-its-own-parser-rejects) | Printer output is not re-parseable | Printer | Minor |
| [6.5](#65-llvmicmp-in-generic-form-is-not-accepted) | ~~Generic-form `llvm.icmp` rejected~~ **FIXED** | SLLVM parser | No |
| [6.3](#63-llvmptr-is-not-accepted-as-a-type) | ~~`!llvm.ptr` not accepted~~ **FIXED** | SLLVM parser | No |
| [3.11](#311-peeling-is-quadratic-in-the-number-of-instructions) | Peeling is quadratic in instruction count | Proof automation | No, but it caps region size |
| [7.1](#71-vpermi2var-has-no-operation) | `vpermi2var` has no op | LLVM dialect | Yes — 3/13 avx512 regions today |
| [7.2](#72-extractelement-has-no-operation) | ~~`extractelement` has no op~~ **FIXED** | LLVM dialect | No |
| [8.1](#81-mlir-translate-rejects-inline-asm) | `mlir-translate` rejects inline asm | MLIR toolchain | Yes — blocks ref point layer entirely |
| [8.2](#82-mlir-sroa-and-mem2reg-cannot-promote-the-point-locals) | MLIR `--sroa`/`--mem2reg` are a no-op here | MLIR toolchain | Closes a workaround |
| [8.3](#83-lifting-cfg-to-scf-does-not-apply-to-the-llvm-dialect) | `--lift-cf-to-scf` doesn't see `llvm` branches | MLIR toolchain | Closes a workaround |

---

## 2. Correctness defects

These produce wrong answers rather than errors, so they are listed first.

### 2.1 `store` never overwrites

[`Dialect/Semantics/MemorySemantics.lean:76`](../SLLVM/Dialect/Semantics/MemorySemantics.lean#L76)
writes the new value into the block with `|||` and no mask of the destination
range, so a store can only ever set bits:

```lean
let bytes := block.bytes ||| (x.zeroExtend _ >>> p.offsetInBits)
```

Reproduction — `*p = 7; *p = 2; return *p` evaluates to `7`:

```lean
def overwrite : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p  = "ptr.alloca"() <{elem_type = i64}> : () -> (!ptr)
    %c7 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> (i64)
    %c2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> (i64)
    "ptr.store"(%p, %c7) : (!ptr, i64) -> ()
    "ptr.store"(%p, %c2) : (!ptr, i64) -> ()
    %v  = "ptr.load"(%p) : (!ptr) -> (i64)
    "llvm.return"(%v) : (i64) -> ()
}]
-- #eval  ⇒  some 7#64     (correct: 2)
```

End-to-end: `sum_of_squares(a,b) { acc=0; acc+=a*a; acc+=b*b; return acc; }`,
hand-inlined into SLLVM, gives `11` for `(3,1)` where the compiled C program
gives `10`. It happens to agree on `(3,4)` and `(5,2)` — the defect only shows
when the new value has a zero bit where the old had a one, which is why it has
survived.

The intended operation is a masked splice of the range `[8·offset, 8·offset+w)`.

**FIXED.** `store` now goes through `SLLVM.spliceBits`, which masks the
destination range out before placing the value into it. The reproduction above
is a `#guard` in [`SLLVM/Tests/Memory.lean`](../SLLVM/Tests/Memory.lean) and
now gives `2`.

### 2.2 `store` at a non-zero offset is discarded

Same line: `>>>` should be `<<<`. `load` reads via
`block.bytes.extractLsb' p.offsetInBits w`, i.e. from `offsetInBits` upwards, so
`store` must shift *left* to place the value. As written, the value is shifted
off the bottom of the block.

Reproduction — write `0xAB` at byte offset 1 of an 8-byte block, then read the
block:

```lean
    %p8  = "ptr.add"(%p, %one) : (!ptr, i64) -> (!ptr)
    "ptr.store"(%p8, %ab) : (!ptr, i8) -> ()
    %v   = "ptr.load"(%p) : (!ptr) -> (i64)
-- #eval  ⇒  some 0#64      (correct: 0xAB00 = 43776)
```

**FIXED** together with 2.1; `spliceBits` shifts left. The reproduction is a
`#guard` in [`SLLVM/Tests/Memory.lean`](../SLLVM/Tests/Memory.lean) and now
gives `0xAB00`. A third `#guard` there checks the masking directly: writing a
zero byte next to a run of ones clears exactly one byte.

---

## 3. Memory operations

### 3.1 The LLVM dialect has no memory operations

`llvm.alloca`, `llvm.load`, `llvm.store`, `llvm.getelementptr` all reach the
`unsupportedOp` fallback in
[`LLVM/Syntax/EDSL.lean`](../../../LeanMLIR/LeanMLIR/Dialects/LLVM/Syntax/EDSL.lean).
Memory is modelled only in the separate **SLLVM** dialect.

```
$ lake exe opt square_region.mlir
uncaught exception: Error parsing …: Unsupported operation 'llvm.alloca'
```

Scale: of the 1464 vendored files in `test/LLVMDialect/InstCombine/`, 441
contain a memory op, 711 contain a call, and 964 (66%) contain at least one of
the two.

### 3.2 SLLVM op names and operand order do not match MLIR

SLLVM models memory but under names that no MLIR tool emits
([`SLLVM/Dialect/Syntax/Parser.lean:148-157`](../SLLVM/Dialect/Syntax/Parser.lean#L148)):

| `mlir-translate --import-llvm` emits | SLLVM requires |
|---|---|
| `llvm.alloca %c1 x i64` | `ptr.alloca` with an `elem_type` attribute and **no count operand** |
| `llvm.store (value, ptr)` | `ptr.store (ptr, value)` — **operands swapped** |
| `llvm.load` | `ptr.load` |
| `llvm.getelementptr` | *(nothing — see 3.3)* |
| `!llvm.ptr` | `!ptr` |

This is deliberate, not drift: the dialect header states SLLVM "will become a
formalization of the `ptr + arith + scf` MLIR dialects". But the names do not
match MLIR's `ptr` dialect either — when they were written (Sept 2025, #1719)
that dialect registered only the `!ptr.ptr` type and `#ptr.spec` attribute and
had **zero operations**, verified against MLIR 19:

```
$ mlir-opt --show-dialects | grep ptr     → ptr    (registered)
$ echo '%v = "ptr.load"(%p) : ...' | mlir-opt
   error: unregistered operation 'ptr.load' found in dialect ('ptr')
```

Upstream has since converged on `ptr.ptradd` (not `ptr.add`),
`!ptr.ptr<#ptr.generic_space>` (not `!ptr`), value-first `ptr.store` operands,
and no `ptr.alloca` at all.

**Partially fixed.** The parser now additionally accepts `llvm.load` and
`llvm.store` under those names, with MLIR's `(value, ptr)` operand order
swapped back to the dialect's `(ptr, value)` on the way in, and accepts
`!llvm.ptr` as well as `!ptr` (see 6.3). The `alignment`, `tbaa` and
`nontemporal` attributes are accepted and ignored — this model has neither
alignment constraints nor alias-metadata semantics — while a non-zero
`ordering` is rejected, since atomics are not modelled. `alloca` and
`getelementptr` still have no MLIR-spelled front end.

### 3.3 No `getelementptr`

There is no gep operation in either dialect. Any structure or array access must
be hand-lowered to `ptr.add` with manually computed byte offsets.

Measured cost on the ed25519 point layer (`fd_curve25519.c` at `-O2`): **1054**
geps on the ref side, **271** on the avx512 side.

**Partially fixed (2026-08-24).** `SLLVMOp.gep elemSizeBytes` covers the one
shape the ref field layer emits: a single *dynamic* index with an integer
element type (`rawConstantIndices = array<i32: -2147483648>`), denoting
`ptradd` by `elemSizeBytes · i` (`SLLVM.gep`; tests in
`SLLVM/Tests/Gep.lean`, including the verbatim attribute dict). `inbounds` is
accepted and ignored: an out-of-bounds gep that LLVM makes poison stays an
ordinary pointer here, so the model is *more defined* than LLVM at this point
-- trivially inbounds in the lifted artifacts, but a soundness assumption the
proof layer must restate.

**Extended, same day: struct-field geps.** `SLLVMOp.gep` is now
`(strideBytes, offsetBytes)`: one leading dynamic index scaled by the element
type's padded size, then *constant* trailing indices accumulated into a byte
offset by walking the type -- struct fields with alignment padding, array
strides. The element types themselves (`!llvm.struct<"…", (…)>`,
`!llvm.array<n x t>`) reach the AST as verbatim text (the payload nests
types Lean's tokenizer cannot split, so the grammar captures it raw, like
`vector<…>`) and are decoded by `parseAggTy`/`AggTy.sizeAlign` in the SLLVM
parser -- default data layout, packed structs rejected.
`fd_ed25519_point_is_zero`'s field accesses (`{X, Y, T, Z}`, offsets
40/120) parse and compute correctly (`Tests/Gep.lean`,
`Ref/Mlir/PointIsZeroTest.lean`). Still open: a *trailing* dynamic index
(`a[i].f[j]` with `j` dynamic) and non-default data layouts.

**Extended, 2026-08-27: vector fields.** `parseAggTy` knew `iN`, `ptr`,
`array<n x t>` and `struct<…>` -- the shapes the *ref* point struct is built
from. The avx512 point struct is three `vector<8xi64>` fields, and the
decoder returned `none` on the `v`:

```
llvm.getelementptr: cannot decode `elem_type =
  !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>`
```

`AggTy.vector` now covers it, with the builtin vector's own layout rather than
its element's: unpadded, and aligned to the size rounded up to a power of two.
That is what puts field 1 at byte offset 64 and agrees with the `alignment =
64` the artifact's stores carry. Note the spelling difference the parser has
to absorb -- MLIR writes `vector<8xi64>` with no spaces, against
`array<5 x i64>` with them. Test: `vectorStructGep` in `Tests/Gep.lean`.

**Fixed, same day: two dynamic index operands.** `fd_f25519_set` is
the first ref region to need it. GCC spells `x->limb[k]` (`x : fd_f25519_t`, i.e. `struct { uint64_t limb[5]; }`)
as

```
%6 = "llvm.getelementptr"(%arg1, %0, %1) <{elem_type = !llvm.array<5 x i64>,
  inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}>
  : (!llvm.ptr, i64, i64) -> !llvm.ptr
```

-- *two* sentinels, so both indices are SSA operands, even though `%0` is the
constant `0` and `%1 … %4` the constants `1 … 4`. `SLLVMOp.gep` is
`(ptr, i64) -> ptr`: one dynamic index, then constants folded into a byte
offset. So the arm rejects it before it can look at the operands:

```
Expected exactly 2 argument(s), but found 3
```

Nothing in the parse arm can fix this on its own -- `mkExpr` sees one operation
at a time and cannot follow `%0` to its defining constant. But the shape *is*
degenerate: with a leading index of `0` the gep is exactly the supported
`gep(%p, %1) elem_type = i64`. So `foldGepZeroIndex` (an AST pre-pass in the
style of `bindCallees`, wired into all `[sllvm…]`/`[sllvm_cfg…]` elaborators)
collects each region's entry-block zero constants and rewrites a matching gep of
`array<n x t>`: drop the leading operand and one sentinel, step `elem_type` to
`t`. A leading operand that is not a visible zero, or a non-array element type,
is left for the parse arm to reject as before (`twoDynGep` in `Tests/Gep.lean`;
the positive shape is `zeroLeadGep`). `fd_f25519_set` and
`fd_ed25519_point_from` lift.

Still open: a genuinely dynamic leading index (`p[i].f`), and a *trailing*
dynamic index -- neither appears in the artifacts.

### 3.4 `alloca` accepts only integer element types

```
"ptr.alloca"() <{elem_type = !ptr}>              → Expected value of attribute
"ptr.alloca"() <{elem_type = !llvm.array<2 x i64>}>   `elem_type` to be an integer type
```

Consequences: `alloca ptr` (which `-O0` emits to spill pointer parameters) and
`alloca [2 x i64]` are both inexpressible, so unoptimised IR is out of reach —
mem2reg must run first. On the ed25519 ref side the point locals are
`fd_f25519_t r1[1] … r8[1]`, i.e. aggregate allocas (9 per `point_add_with_opts`),
so the ref point layer cannot be expressed at all.

**Partially fixed (2026-08-24).** `llvm.alloca` with a decodable aggregate
`elem_type` (`!llvm.struct<…>` / `!llvm.array<…>`, via the same
`parseAggTy`/`sizeAlign` machinery as 3.3) allocates a block of the
aggregate's padded size -- memory is flat bytes, so the layout is all an
aggregate alloca needs. `fd_f25519_eq`'s `fd_f25519_t r[1]` local (the shape
of all 9 point-op locals) works; `alloca ptr` remains open.

### 3.5 `load`/`store` are scalar-only

The signatures in [`SLLVM/Dialect/Basic.lean:138-142`](../SLLVM/Dialect/Basic.lean#L138)
are over `bitvec w`:

```lean
| .load w   => (ptr) -[.impure]-> bitvec w
| .store w  => (ptr, bitvec w) -[.impure]-> []
```

There is no vector-typed load/store and no bitcast operation to route around it,
so `load <8 x i64>` — the *only* load shape in the avx512 point operations —
cannot be expressed.

**FIXED.** The four memory operations now carry an `LLVM.Ty` rather than a
width, and the flat in-memory encoding is
`LLVM.Ty.flattenBV`/`LLVM.Ty.unflatten` (lane `0` in the low bits, as LLVM lays
a vector out), with `LLVM.Ty.Defined` deciding whether there is anything to
store — a vector with a poison lane raises UB, exactly as a poison scalar does.
No `bitcast` was added, so a lifted region stays byte-identical to the compiler
artifact.

### 3.6 `loadPure` / `storePure` / `!mem` are unreachable from syntax

The memory-SSA operations are fully defined and denoted
([`Basic.lean:139,141`](../SLLVM/Dialect/Basic.lean#L139),
[`MemorySemantics.lean:53,86`](../SLLVM/Dialect/Semantics/MemorySemantics.lean#L53))
but have no front-end:

- `mkTy` ([`Parser.lean:28`](../SLLVM/Dialect/Syntax/Parser.lean#L28)) knows
  `!ptr` only — `!mem` gives `Unsupported type: MLIR.AST.MLIRType.undefined "mem"`
- the parser has no case for either op name
- the printer maps them to the same names as the impure ops
  ([`Basic.lean:232-238`](../SLLVM/Dialect/Basic.lean#L232))

This matters because they are the intended fix for 3.8.

### 3.7 No memory lemmas; proof automation stalls

There are **zero** theorems anywhere in the repository mentioning
`load`/`store`/`alloca`. The only SLLVM tests are printer round-trips
(`SLLVM/Tests/Print.lean`).

`simp only [Com.denote, simp_denote, simp_sllvm]` fully normalises the
arithmetic path but gets stuck on `SLLVM.alloca` / `SLLVM.store` / `SLLVM.load`,
leaving a raw `StateT GlobalState PoisonOr` do-block with `Std.HashMap`
operations exposed. Compare the arithmetic path, where
`simp_alive_case_bash <;> bv_decide` closes goals automatically.

**FIXED** for straight-line code.
[`SLLVM/Dialect/Semantics/MemoryLemmas.lean`](../SLLVM/Dialect/Semantics/MemoryLemmas.lean)
adds `Fits` (the pointer addresses a live block with room), `MemoryState.splice`
(the state after a successful store), and success-form `run` lemmas for `store`,
`load`, load-after-store at the same and at a different block, and the
`MemorySSAM → EffectM` lift. `EffectM.lean` gained the `MemorySSAM` `run`
lemmas that let `simp` see through a `do`-block of memory operations at all.

A second stall, not recorded above, also had to be closed: a region ending in a
store is `.impure` *throughout*, so its arithmetic instructions are
impure-typed expressions with pure operations, and
`Firedancer/MLIR/DenoteStep.lean`'s stepper — which is what makes a
115-instruction derivation tractable — only knew how to step a pure `Com`. It
now falls back to `Com.denote_var_pureOp_single` when the expression is
impure-typed but its operation is pure, and `simp_denote` gained
`Expr.op_toPure`/`args`/`regArgs` (the analogue of the `castPureToEff`
projections it already carried) so that everything downstream of the stepper
works unchanged.

### 3.8 `PeepholeRewrite` cannot express a memory rewrite

[`Transforms/Rewrite/Rewrite.lean:135`](../../../LeanMLIR/LeanMLIR/Transforms/Rewrite/Rewrite.lean#L135)
requires `.pure` lhs and rhs:

```lean
structure PeepholeRewrite (Γ : List d.Ty) (ts : List d.Ty) where
  lhs : Com d (.ofList Γ) .pure ts
  rhs : Com d (.ofList Γ) .pure ts
  correct : lhs.denote = rhs.denote
```

Memory operations are `.impure`, so store-to-load forwarding, dead-store
elimination and friends are **not expressible** in the framework's flagship
verified-rewriting theorem. Confirmed as a type error:

```
Type mismatch: lhs has type Com SLLVM … EffectKind.impure …
               but is expected to have type Com SLLVM … EffectKind.pure …
```

Rewrites can still be *applied into* an impure target; only the pattern must be
pure.

### 3.9 Memory refinement is degenerate

`MemoryState` refinement is pointwise equality of the whole map and
`AllocState` refinement is equality
([`Memory.lean:64-75`](../SLLVM/Dialect/Semantics/Memory.lean#L64)); `Ptr`
refinement is equality rather than poison-refinement
([`Refinement.lean:13`](../SLLVM/Dialect/Refinement.lean#L13)). So allocation
count is observable and "the optimised program leaves different garbage in a
dead stack slot" is not a valid refinement.

### 3.10 A callee's allocas survive its return

*(Added 2026-08-20, while lifting `fd_r43x6_ge_is_eq`.)* `SLLVM.alloca` hands
out fresh blocks and nothing ever frees one. Since calls are now modelled — a
call denotes as its callee's region applied in the *caller's* memory state —
this is no longer just a single-function simplification: in a real execution
the callee's allocas die at its `llvm.return`, while here the memory state a
call returns still contains them, live. The lifetime intrinsics parse
(`SLLVMOp.lifetime`) but denote to nothing. Consequences:

- Addresses are never reused, so a *dangling* load — through a callee-local
  pointer that escaped the call, or after a real stack slot has died — gets
  the stale value where LLVM says UB and a real stack holds reused junk. The
  model is **more defined** than LLVM there: a proof about a program that
  dangles would not transfer to the machine. The lifted kernels pass pointers
  *into* callees (out-parameters) and never the other way, so this costs
  nothing today, but it is a soundness *assumption about the artifacts*, not
  a theorem.
- Allocation is observable (see 3.9), so "the callee's frame is gone
  afterwards" is not representable even as a refinement.

The natural fix is for a call to deallocate on return the blocks its region
allocated (and `lifetime.end` likewise), turning an escaped-pointer access
into the UB it really is; it only makes sense together with a non-degenerate
memory refinement (3.9).

**FIXED** for the call half, same day. Block ids come from a monotonic
counter and `alloca` is the only allocator, so "the callee's frame" is
recoverable with no per-block bookkeeping: the impure-call denotation
snapshots `nextFreeBlock` on entry and on return marks dead every block at or
past it (`MemoryState.killFrom`) -- dead, not removed, so an escaped pointer
takes the freed-already UB path on use. `Tests/Call.lean` pins the three
behaviours: a callee using its own slot internally is unaffected, a caller
block written through an out-parameter survives (it predates the snapshot),
and loading through a returned frame pointer is UB. `denoteOp_call` split
into a pure lemma (unchanged shape) and `denoteOp_call_impure` (region
application, then frame-kill), with `getElem?_killFrom_of_lt`/`_of_le` in
`MemoryLemmas.lean` for stepping caller loads past a call. The lifetime
intrinsics stay denotationally inert on purpose: with a monotonic counter
there is no slot reuse for them to advise on, and the semantic event they
approximate -- the frame dying -- now happens at the return itself.
Later the same week the boundary became `SLLVM.runFunction` (snapshot, body,
`killFrom`, *and* counter restore), so a call pops its frame rather than
leaking counter values, and `GlobalState.Equiv` (`≈`: same counter, same
live blocks; `MemoryState.live?`) with `GlobalState.killFrom_equiv` states
"this function leaves the stack as it found it" -- the shape the
`fd_r43x6_ge_is_eq` corollary wants. What remains open here is heap
allocation: a future `alloc` must not be frame-
killed, which is the point where blocks need a stack/heap kind bit.

### 3.11 Peeling is quadratic in the number of instructions

`denote_step_all` names each instruction's value and records
`hv<i> : v<i> = e.denoteOp1 V`, where `V` is the valuation the walk has built
so far -- a `Ctxt.Valuation.cons` spine one cell deep per instruction already
peeled. Evaluating that hypothesis means running `simp_peephole`, i.e. the
whole `simp_denote` set, over a term that *contains* the spine, so one
evaluation costs O(instructions peeled) and a straight-line region costs
O(instructions²).

Measured on `fiat_25519_to_bytes` (168 instructions, 32 of them byte stores),
2026-09-04, `-Dtrace.profiler`:

| where | spine depth | calls | total |
|---|---|---|---|
| `limb_peel`'s `denote_eval` | ~70 | 4 | 1.7 s (0.43 s each) |
| `store_bytes`' byte-gep `denote_eval` | 100-170 | 31 | 54 s (1.75 s each) |

The per-call cost tracks the depth, not the instruction: all 31 byte geps are
the same two-operand `getelementptr` and fire the same 21 lemmas. Naming those
21 lemmas instead of `simp_denote`, and running them in one pass rather than
`simp_peephole`'s three, takes the 54 s to 43 s -- the rest is the traversal
itself, which no simp-set change reaches.

Not blocking: `fiat_25519_to_bytes` elaborates in 134 s. It does put a ceiling
on region size, and it is why the byte-store chain dominates the proof.

The fix is to stop the spine appearing in what is simplified -- seal the
valuation behind an fvar per step, with the lookups a step actually needs
threaded forward as hypotheses (`(cons x V) v.succ = V v`, one rewrite per
step) rather than re-resolved from scratch. That is a change to
`Firedancer/MLIR/DenoteStep.lean`, not to any proof.

### 3.12 A callee's write chain is unfolded by every type ascription

A conformance lemma hands the caller `w ≈ { s with mem := m }`, where `m` is
the callee's write chain -- for `fd_ed25519_point_from`, four splices of
`packLimbs`. The caller then wants that block's facts at `w`: `IsByteBufPtr
w.mem buf`, `readBuf`, `IsPointPtr`. Every such step is an equation whose two
sides are `w.mem.live? q` and `({ s with mem := m }).mem.live? q`, and
*ascribing* the step's type -- writing the `have`'s type out, or feeding it to
a lemma whose corresponding argument is already fixed -- makes the elaborator
compare them by `whnf` rather than by projection. Measured on
`fd_ed25519_point_frombytes_2x`, 2026-09-07: one such transport of
`IsByteBufPtr` costs >150 000 heartbeats, against ~4 000 for the same
transport of `IsPointPtr` written without the ascription.

The workaround is to state the transport lemma over `{ s with mem := m }`
itself, so `m` unifies as a whole and the projection never has to reduce:
`isByteBufPtr_of_equiv`, `isPointPtr_of_equiv`, `readBuf_of_equiv`,
`live?_of_equiv_mem`. With those the walk runs in 4.9 s; without them it does
not fit in the default heartbeat budget at all.

Two smaller instances of the same shape, same file:

* `pointOutMem` (the four coordinate stores) is a `def`, not an `abbrev`.
  Reducible, every unifier that meets it walks the splices; the proofs pay for
  it at each `live?`. `limbSum` in `Ref/Spec/Bias.lean` is a `def` for the
  same reason.
* `refine popFrame_equiv_block hs hn ?fm ?fn ?val` with the side conditions
  left as placeholders costs more than the same proof with each named as an
  ascribed `have` first -- the placeholders elaborate against a metavariable,
  and the memory term is walked twice over.

Not blocking, and not a soundness issue: it is a rule about how the proofs
have to be *written*. It is listed here because nothing in the error message
points at it -- the failure is a heartbeat timeout on a line that looks
trivial.

---

## 4. Calls

### 4.1 Calls are not modelled

`Com` is a straight-line let-chain
([`Framework/Basic.lean:166`](../../../LeanMLIR/LeanMLIR/Framework/Basic.lean#L166))
with no symbol table and no multi-function module. Calls are architecturally
absent, not merely unimplemented.

`llvm.call` is accepted **only** as a keyhole for two AVX-512 IFMA intrinsics
([`Parser.lean:233-241`](../SLLVM/Dialect/Syntax/Parser.lean#L233), same in
[`EDSL.lean:238`](../../../LeanMLIR/LeanMLIR/Dialects/LLVM/Syntax/EDSL.lean#L238)):

```
$ lake exe opt sos_region.mlir
uncaught exception: … Unsupported operation 'llvm.call to square'
```

**Workaround: inlining.** Re-extracting the Firedancer avx512 probes without
`-fno-inline` removes every call:

| region | with `-fno-inline` | inlined |
|---|---|---|
| `fd_mlir_r43x6_mul` | 10 ops + 1 call ✗ | 218 ops, 0 calls ✓ |
| `fd_mlir_r43x6_sqr` | 10 ops + 1 call ✗ | 168 ops, 0 calls ✓ |

Compositionality is not lost: [`Framework/Zipper.lean`](../../../LeanMLIR/LeanMLIR/Framework/Zipper.lean)
splits a `Com` into `Lets ++ Com` with `denote_toCom`, so a lemma about a proven
prefix can be reused inside an inlined region. It is manual plumbing, not a call
abstraction.

**Worked through once, on `fd_long_if`.** `fd_r43x6_is_nonzero` calls it, so
the region does not parse; but the *callee* parses verbatim
([`Avx512/Mlir/fd_long_if.lean`](Avx512/Mlir/fd_long_if.lean)) and is proven
([`Avx512/Proof/fd_long_if.lean`](Avx512/Proof/fd_long_if.lean)). That is what
inlining costs in practice: the callee is lifted and specified on its own, and
`denote_fd_long_if` then says what the spliced-in instructions mean, so the
caller's proof rewrites rather than re-derives.

Note what `-fno-inline` handed us here. `fd_long_if(c,t,f)` is `c ? t : f`, but
the emitted region takes only the condition: the function is `static`, so LLVM
sees every call to it in the translation unit, IPSCCP replaces a parameter that
holds the same constant at all of them with that constant, and dead-argument
elimination drops it. The specification is therefore of `c ? 19 : 0`, not of
`fd_long_if` — which is the right thing to prove, since that is the program
that exists.

Measured on `clang-18 -O2 -fno-inline` rather than assumed: call sites passing
different constants keep all three parameters, call sites agreeing specialise
however many there are, and the folding is per parameter. So the shape is
stable as the extraction grows — every expansion of
`fd_r43x6_mod_nearly_reduced_limbs` passes the same `19L` and `0L`, so adding
`fd_r43x6_mod` or `fd_r43x6_pack` probes would not change this region.

**Update (2026-08-24): the CFG layer has real calls.** `Com` is unchanged
(a call's callee still travels as the `Expr`'s region, `Com`-shaped, so a
multi-block callee cannot ride in a `Com` caller). But inside a `Cfg` block,
every `llvm.call` becomes a `BlockCom.call` node whose callee is itself an
inlined `Cfg` -- a straight-line callee is just the one-block case -- bound
with the same `with @f := …` surface (`[sllvm_cfg| … with …]`), spliced
transitively by `bindCallees` (which now also descends into tail blocks),
built recursively by `mkCfg` (fuel-bounded, like region nesting), and
denoting through the same `runFunction` frame-kill boundary as
`SLLVMOp.call`. The whole ref chain
`fd_ed25519_point_is_zero → {fd_f25519_is_zero, fd_f25519_eq} →
fd_f25519_sub → {fiat_25519_sub, fiat_25519_carry}` -- one multi-block
callee entered from two call sites, an aggregate alloca, aliased
out-parameters, depth-4 nesting -- lifts verbatim and computes correctly
(`Ref/Mlir/fd_ed25519_point_is_zero.lean`, `Ref/Mlir/PointIsZeroTest.lean`,
`SLLVM/Tests/Cfg.lean`). Still true: no symbol table -- callees travel with
the call site -- and a `Com` caller still cannot call a `Cfg` callee (lift
the caller to a one-block `Cfg` instead, as `point_is_zero` does).

### 4.2 Globals were not modelled

```
$ lake env lean Ref/Mlir/Field/fd_f25519_sqrt_ratio.lean
error: Unsupported operation 'llvm.mlir.addressof'
```

`ref.mlir:9,17,25` declares three: `@fd_f25519_sqrtm1`, `@fd_f25519_one`,
`@fd_f25519_d`, all `constant, internal, alignment = 16, unnamed_addr = 0`.
Two regions take an address -- `fd_f25519_sqrt_ratio` and
`fd_ed25519_point_frombytes` -- and every use is a read-only source operand
passed to `fd_f25519_{mul,sub,add}` / `fd_ed25519_point_from`.

**Fixed (2026-09-03).** Unlike callees, globals *do* get a symbol table:
`GlobalState` gains `globals : Std.HashMap String Pointer` and
`llvm.mlir.addressof` reads the address out of it (`SLLVM.addressof`). That is
what makes every `addressof` of a symbol, at any call depth, name the same
block -- a per-region pointer parameter cannot, without threading the pointer
through every call site, and would silently hand a callee a different block.
One address per global is also what makes a *mutable* global sound: a write
through one `addressof` is seen by the next (`SLLVM/Tests/Globals.lean`).

The operation reads nothing else and checks nothing, so it does not carry its
global's initialiser. A bound initialiser would be a claim nothing could check
-- the table is keyed by name -- and checking the *contents* at lookup time is
exactly what a store to a mutable global would invalidate. So what a global
holds is a hypothesis: `HoldsGlobal s name p v` (`Proof/Globals.lean`),
alongside `GlobalPtr s name p`, which is the half that survives a write.
`GlobalState.withGlobal` installs one, and is what a `#guard` or a top-level
caller starts from. The initialisers themselves lift verbatim from
`build/native/gcc/mlir/ref/region/fd_f25519_{sqrtm1,one,d}.mlir` -- headerless
regions of the aggregate shape below -- with a `#guard` pinning their limbs
against the artifact, so a spec quotes the constants rather than retyping them.

The table is **write-once**: `withGlobal` is its only writer, `runFunction`
restores it along with the frame counter, and `GlobalState.Equiv` carries
`s.globals = s'.globals`, so a region that repointed a global could not satisfy
its spec -- every conformance spec ends in `output_state ≈ s'`.

Two things are deliberately *not* derived. Disjointness of two globals, and of
a global from a caller's buffer, stay hypotheses: `unnamed_addr` licenses LLVM
to merge constants with equal initialisers, and an `@alias` points into its
aliasee, so overlap is expressible even though these three do not overlap.
`fd_f25519_sqrt_ratio` reads its global at `%28`/`%32` after writing through
`%arg0`, so its conformance theorem carries `g.id ≠ o.id`, the idiom
`fd_f25519_set_spec` already uses. And `GlobalState.WF` is untouched: a
global's liveness comes from `HoldsGlobal`, and `lt_nextFreeBlock_of_fits` then
places its block below the counter, so `killFrom` never reaches it.

Still open: `llvm.mlir.global` itself has no representation -- a module's
globals are installed by hand, not read off `ref.mlir` -- and `@alias` and
`unnamed_addr` are unmodelled.

### 4.3 Aggregates in registers

**Fixed (2026-09-03).** `mlir-translate` materialises a constant
`fd_f25519_t` as `dense<[...]> : tensor<5xi64>` at `!llvm.array<5 x i64>`,
an `undef` struct and two `insertvalue`s -- the shape of every global
initialiser, and dead code in the two regions that also carry it. Three gaps
at once: `tensor<n x t>` had no `mlir_type` production at all (only the
placeholder keywords `tensor1d`/`tensor2d`), `mkArithTy` had no case for an
aggregate, and there was no `insertvalue`.

An aggregate in a register is now LLVM's own flat layout: a `bitvec` of the
aggregate's padded size, lowest-addressed field in the low bits, decoded by the
same `parseAggTy`/`sizeAlign` machinery as `getelementptr` and `alloca`. A
`dense<…>` array constant packs its lanes into one constant and `insertvalue`
is a bit splice at the offset `constIndexOffset` computes. What the flattening
cannot express is per-field poison: `SLLVM.insertvalue` is exact when the field
covers the whole aggregate (the `undef` + one `insertvalue` idiom the artifacts
use) and deliberately conservative otherwise. Tests: `SLLVM/Tests/Aggregate.lean`,
including the verbatim initialiser stored and read back through a gep.

---

## 5. Control flow and loops

### 5.1 `Com` has no control flow

```lean
inductive Com : Ctxt d.Ty → EffectKind → List d.Ty → Type where
  | rets {Γ} {tys} {eff} (vs : HVector Γ.Var tys) : Com Γ eff tys
  | var  (e : Expr Γ eff ty) (body : Com (ty ++ Γ) eff β) : Com Γ eff β
```

No branches, no basic blocks, no φ nodes, no back-edges. `llvm.br`,
`llvm.cond_br` and `llvm.switch` are as unrepresentable as `llvm.call`.

In the InstCombine corpus: 255/1464 files contain a branch or switch, 262
contain a `^bb1` or later.

**Partially fixed (2026-08-24), for forward CFGs.** `Com` is unchanged;
`SSA/Projects/SLLVM/Cfg/` adds the layer `fd_f25519_is_zero` -- the only
region in the extraction with branches -- needs: a `Cfg` is a list of blocks
whose bodies have exactly `Com`'s cons shape (`BlockCom.var`) but end in a
`Terminator` (`ret`/`br`/`cond_br`/`switch`), with block arguments as the φ
nodes and branch operands passing them. Two restrictions, both matching the
artifact: branches only go *forward* -- a `Target` points into the list of
blocks after the current one, so a back-edge is unrepresentable and the
interpreter is structural, total, fuel-free -- and a non-entry block sees
only the entry block's definitions plus its own arguments (depth-1
dominance; verified sufficient: every cross-block reference in the artifact
is to a bb0 def or a region arg). Branching on a poison condition or
scrutinee is UB, as in LLVM. `mkCfg` (`Cfg/Transform.lean`) reuses the
straight-line per-op machinery, so gep/loads/icmp inside blocks come for
free; `[sllvm_cfg| …]` / `[sllvm_cfg_of| …]` (`Cfg/Quotation.lean`) reflect
the result into a term. `Ref/Mlir/fd_f25519_is_zero.lean` -- byte-identical
to the artifact, `// pred:` comments included -- elaborates to
`Cfg (Ctxt.ofList [ptr]) [bitvec 32]` on standard axioms only, and
`Ref/Mlir/IsZeroTest.lean` `#guard`s all 11 CFG paths plus dangling-pointer
UB. Loops remained open until 2026-09-01, blocked on exactly the predicted
decision: how nontermination enters `EffectM`. **Resolved: nontermination is
UB.** The artifacts' loop latches all carry
`#llvm.loop_annotation<mustProgress = true>` -- C's forward-progress
guarantee -- so LLVM is already licensed to assume they terminate, and a
model in which a non-terminating loop is UB is *more* faithful than one that
diverges. (This is a soundness assumption about the artifacts, like
`inbounds`: a proof about a genuinely non-terminating program would not
transfer.) With that settled, the two forwardness commitments fell together:

- `Target` now names *any* block -- a `Ctxt.Var`-shaped index
  `{ idx // all[idx]? = some ts }` into the full signature list, so
  back-edges and MLIR's out-of-order forward edges (`^bb2 → ^bb1` in
  `fd_f25519_pow22523`, backward only in print order) are the same thing and
  `resolveSucc`'s check is simply deleted. Regions lift verbatim, loop φs
  and all; there is no loop recognizer.
- The interpreter is factored into a **fueled, computable core**
  (`BlockCom.eval`/`Blocks.iterate`, one unit of fuel per block transition,
  `none` = still running; lexicographic termination on (fuel, term)) and the
  **semantics as its limit** (`Blocks.run`/`Cfg.denote`, classical -- the
  one place "does it halt" is decided; a walk with no limit is UB).
  `Cfg/Eval.lean` proves fuel monotonicity, the master theorem
  `run_denote` (the denotation *is* the limit), the one-step equation
  `Blocks.run_step` that proofs walk loops with, and `Cfg.eval_sound`, which
  transfers every fueled `#guard` result to `Cfg.denote`. `#guard`s now run
  `Cfg.eval` at a fuel bound (`Tests/Cfg.lean`: a counted loop, fuel
  exhaustion on `spin`, the out-of-order-edge shape). `Cfg.denote` is
  `noncomputable` and, for looping regions, genuinely rests on
  `Classical.choice`.

### 5.2 `Scf` can only wrap a toy dialect

Structured control flow exists in [`SSA/Projects/Scf/ScfFunctor.lean`](../Scf/ScfFunctor.lean)
as a functor `Scf d` adding `if`, `for`, `run`, `iterate` to a base dialect. The
`for` op carries the loop body as a region and denotes to `Nat.iterate`, so only
**bounded, counted** loops are expressible — no `while`, no unbounded loop, no
`break`, no early exit.

More restrictive still, `Scf d` requires `HasBool d`, `HasNat d`, `HasInt d` —
a `d.Ty` whose denotation is *definitionally* `Bool`/`ℕ`/`ℤ`. The only instances
are for `Arith`, a 6-operation toy dialect over `ℤ`
([`ScfFunctor.lean:316-318`](../Scf/ScfFunctor.lean#L316)):

```
#synth ScfFunctor.HasInt InstCombine.LLVM
  failed to synthesize ScfFunctor.HasInt InstCombine.LLVM
```

This is not fixable by adding an instance: every LLVM type denotes
`PoisonOr (BitVec w)`, never `Int`. **`Scf LLVM` and `Scf SLLVM` are not
constructible**, so a loop over a bitvector — let alone one containing a load —
cannot be written.

### 5.3 Regions cannot be parsed

[`MLIRSyntax/Transform/Utils.lean:171`](../../../LeanMLIR/LeanMLIR/MLIRSyntax/Transform/Utils.lean#L171):

```lean
-- TODO: parse regions
if h_noRegions : ¬signature.regSig.isEmpty then
  panic! "mkExprOf shouldn't be called with an operation that expects regions!"
```

There is no `[scf| …]` quotation and no `DialectParse` instance for `Scf`; every
Scf program in the repository is built by hand from constructors. So even if
5.2 were fixed, nothing produced by `mlir-translate` could reach it.

**FIXED (2026-08-24) for multi-block regions.** The AST now carries them --
`Op` gained `successors : List String` (successor *operands* stay in the
operand list, segmented by `operandSegmentSizes`, exactly as MLIR encodes
them), `Region` kept its entry-block fields and gained tail `blocks` -- and
the quotation grammar accepts repeated `^bbN(…):` headers, `[^bb1, ^bb2]`
successor lists in both generic-op rules, and the `^bb1:  // pred: ^bb0`
comments `mlir-opt` prints on block headers (a raw `ParserFn` consumes `//`
to end-of-line; the text is discarded). `mkCom` rejects a multi-block region
with a pointed error and stays whnf-reducible; `mkCfg` (5.1) is the consumer.
Region *antiquotations* and the nested-region TODO in `mkExprOf` are
unchanged.

---

## 6. Syntax and parser

### 6.1 `nsw`/`nuw` are reserved tokens in the EDSL

[`Dialects/LLVM/Syntax/Pretty/Overflow.lean:19`](../../../LeanMLIR/LeanMLIR/Dialects/LLVM/Syntax/Pretty/Overflow.lean#L19)
declares `syntax no_wrap_flag := "nsw" <|> "nuw"` so that the pretty form
(`llvm.add %a, %b overflow<nsw> : i64`, which is what the vendored corpus uses)
parses. Lean tokens are global, so `nsw` is then reserved inside the *generic*
form as well:

```
%3 = "llvm.add"(%1, %2) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> (i64)
                                                          ^
error: unexpected token 'nsw'; expected '>'
```

**This bites only in the quotation path.** `Com.parseFromFile` builds its own
parser without those tokens and reads the generic form fine. Measured on the
Firedancer extraction, which uses `mlir-opt --mlir-print-op-generic`:

| | via `Com.parseFromFile` | via `[sllvm\| …]` |
|---|---|---|
| ref regions | 25 / 25 | **6 / 25** |
| avx512 regions | 6 / 13 | 6 / 13 |

19 ref regions are blocked by this alone. Workaround: quote the flag —
`#llvm.overflow<"nsw">` parses.

**FIXED.** One character each:

```lean
syntax no_wrap_flag := &"nsw" <|> &"nuw"
```

`&"…"` is a *non-reserved* symbol: it parses the keyword where the pretty form
expects it without registering a global token, so `nsw` stays an ordinary
identifier everywhere else — including inside the generic form, where it is an
attribute value. `#llvm.overflow<nsw>` and `#llvm.overflow<nsw, nuw>` now parse
in a quotation exactly as `mlir-opt --mlir-print-op-generic` emits them.

The payoff is that a lifted region no longer has to be *rewritten* to be
quoted. `Avx512/Mlir/fd_r43x6_is_nonzero.lean` is now byte-for-byte identical
to `fd_r43x6_is_nonzero.mlir` — checked by stripping the indentation and
`diff`-ing — where before it carried 21 rewritten flags.

### 6.2 The printer emits syntax its own parser rejects

`Com.printModule` prints generic syntax with the bare flag:

```
%4 = "llvm.mul"(%2, %3)<{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> (i64)
```

which cannot be read back by 6.1. Printing is only ever checked against
`#guard_msgs` string literals, never fed back in, so no test catches it.

### 6.3 `!llvm.ptr` is not accepted as a type

```
^entry(%p: !llvm.ptr):
error: Unsupported type: MLIR.AST.MLIRType.undefined "llvm.ptr"
```

Only the SLLVM spelling `!ptr` is recognised.

**FIXED.** `mkTy` accepts `!llvm.ptr` alongside `!ptr`.

### 6.4 Multi-result operations require every result to be named

[`GenericParser.lean:954`](../../../LeanMLIR/LeanMLIR/MLIRSyntax/GenericParser.lean#L954)
rejects a result-type list longer than the result-name list. Multi-result `Com`
*is* supported since #1511; `%a, %b = "op"(…) : (…) -> (t1, t2)` parses. Note
this makes the "a lean-mlir region has exactly one result" comment in
`conformance_verification/mlir_ref.c` stale — the ref probes could return all
five limbs from one region instead of five.

### 6.5 `llvm.icmp` in generic form is not accepted

The SLLVM parser dispatches on the *op name*, expecting the predicate as a
suffix ([`Parser.lean:208-217`](../SLLVM/Dialect/Syntax/Parser.lean#L208)):

```
| "llvm.icmp.eq"  => mkExprOf <| Op.icmp .eq (← binW)
| "llvm.icmp.ult" => mkExprOf <| Op.icmp .ult (← binW)
```

But `mlir-opt --mlir-print-op-generic` — and MLIR's own `llvm.icmp` — carries
the predicate as an attribute, and the op is always named `llvm.icmp`:

```
%58 = "llvm.icmp"(%56, %13) <{predicate = 6 : i64}> : (i64, i64) -> i1
Error: Unsupported operation 'llvm.icmp'
```

`llvm.icmp.<pred>` is not syntax MLIR ever emits, so the suffixed names are
reachable only by hand-editing. Every comparison in the extraction is hit.
Measured on `fd_r43x6_is_nonzero`, whose two `icmp`s are the `ult` deciding the
conditional subtract and the `ne` against zero that *is* the answer.

**Correction.** The original text said the LLVM dialect's own `EDSL.lean` had
the same gap. It does not: `parseIcmpPredicate` has been there all along and
`[llvm( … )]` accepts the generic form. Only the SLLVM parser, which is the one
the Firedancer regions go through, was missing it.

**FIXED.** The numbering now lives in one place,
`LLVM.IntPred.ofMLIRPredicate?` next to `IntPred` itself, and both parsers use
it. That numbering is worth stating: MLIR's `ICmpPredicate` is 0-based with the
signed comparisons *before* the unsigned ones (0 `eq`, 1 `ne`, 2 `slt`, 3 `sle`,
4 `sgt`, 5 `sge`, 6 `ult`, 7 `ule`, 8 `ugt`, 9 `uge`), which is **not** LLVM
IR's `CmpInst::Predicate` ordering that `LLVM.IntPred` follows — that one starts
at 32 and puts the unsigned comparisons first. The two have to be mapped, not
cast. All ten codes were read off
`clang | mlir-translate --import-llvm | mlir-opt --mlir-print-op-generic` over a
C file containing all ten comparisons, rather than taken from documentation.

Regression tests are in [`SLLVM/Tests/Icmp.lean`](../SLLVM/Tests/Icmp.lean).
Each of the ten compares `-1` against `1` — the pair that separates the signed
reading from the unsigned one — and is cross-checked against the hand-spelled
`llvm.icmp.<pred>` name for the same predicate, so a mapping that swapped a
signed code for its unsigned partner would fail rather than merely compute a
different comparison. An out-of-range code is rejected rather than silently
mapped.

`fd_r43x6_is_nonzero` now parses every instruction of both carry chains; 4.1 is
the only operation left that lean-mlir has no answer for.

---

## 7. Missing operations

### 7.1 `vpermi2var` has no operation

lean-mlir models `vpmadd52l`/`vpmadd52h` but not `vpermi2var`:

```
Error: Unsupported operation 'x86vector.avx512.intr.vpermi2var.q.512'
```

This blocks 3 of the 13 extracted avx512 regions —
`fd_mlir_r43x6_approx_carry_propagate`, `fd_mlir_r43x6_fold_signed`,
`fd_mlir_r43x6_sub`. MLIR's `x86vector` dialect models neither IFMA nor
vpermi2var either (checked through MLIR 20), which is why the Firedancer
pipeline renames the intrinsics before import.

---

### 7.2 `extractelement` has no operation

`llvm.insertelement` and `llvm.shufflevector` are modelled
([`Dialects/LLVM/Basic.lean:137`](../../../LeanMLIR/LeanMLIR/Dialects/LLVM/Basic.lean#L137)),
but `extractelement` — their inverse — does not occur anywhere in the tree:

```
$ grep -rn "extractelement" --include=*.lean LeanMLIR/ SSA/
$ echo $?
1
```

```
Error: Unsupported operation 'llvm.extractelement'
```

This blocks every `fd_r43x6` operation that leaves the vector domain, which is
all of the scalar-limb ones: `fd_r43x6_is_nonzero`, `fd_r43x6_diagnose`,
`fd_r43x6_mod`, `fd_r43x6_pack`. They all begin with
`fd_r43x6_extract_limbs`, which the compiler lowers to six
`extractelement`s off a `<8 x i64>` (the `_mm512_extracti64x4_epi64` and
`_mm256_extract_epi64` of the macro fold away at `-O2`). The reduction to the
canonical representative lives entirely behind that boundary.

The fix mirrors `insertelement` at the eight places it is named in
`Dialects/LLVM/Basic.lean` — constructor, `sig`, `outTy`, denotation, name,
`ToString`, `opName`, the eliminator — plus one parser arm in each of
`SLLVM/Dialect/Syntax/Parser.lean` and `Dialects/LLVM/Syntax/EDSL.lean`. LLVM
semantics: an index that is poison or out of range yields poison — the lane,
not the vector, unlike `insertelement`.

**FIXED.** Done as described, plus the three `SLLVM` sites that lift an
`LLVM.Op` into the memory dialect (`match_pattern` abbrev, signature, denote).
`MOp.extractelement` carries the element type, the lane count and the index
width, so the `i32` index MLIR emits for `insertelement` and the `i64` it emits
for `extractelement` coexist in one region.

Regression tests are in [`SLLVM/Tests/Vector.lean`](../SLLVM/Tests/Vector.lean).
The one that matters is `laneOrder`: it extracts all eight lanes of
`dense<[0, 1, …, 7]>` and packs each into its own byte, which comes to
`0x0706050403020100` exactly when `extractelement`'s numbering agrees with
`dense<[…]>`'s lane for lane. A transposition there would silently permute a
field element's limbs while every arithmetic test still passed. The numbering
also matches `LLVM.Ty.extractLsb'_flattenBV_vector`, the layout the memory
model pins.

`fd_r43x6_is_nonzero` now parses past its six limb extracts; 6.5 above is what
it stops on next.

### 7.3 `llvm.intr.memset` has no operation

```
Error: Unsupported operation 'llvm.intr.memset'
```

`fd_ed25519_point_set_zero` writes the identity point as one vector store of
`dense<[0, 1, 1, 0, 0, 0, 0, 0]>` into field 0, then zeroes the remaining two
128 bytes of the struct with a single `llvm.intr.memset`. Nothing in SLLVM
could express that: memory had `load`, `store` and `alloca` and no bulk fill,
and there is no way to synthesise the equivalent 1024-bit zero constant from
the parser, which builds one `Expr` per operation and cannot introduce an
operand of its own.

**FIXED (2026-08-27).** `SLLVMOp.memset : (ptr, i8, i64) -[.impure]-> []`,
denoting to `SLLVM.memset`, which splices `len` copies of the fill byte into
the block at the pointer's offset. The written width is a *run-time* value --
`BitVec.replicate len.toNat b` -- which the model absorbs for free, since
`spliceBits` was already width-polymorphic. UB conditions are `store`'s: a
poison pointer, byte or length, a dead or unallocated block, or a range
running off the end of the block. `isVolatile` is accepted and discarded, as
alignment is everywhere else.

Tests in [`SLLVM/Tests/Memory.lean`](../SLLVM/Tests/Memory.lean):
`memsetFills` (the range is written), `memsetKeepsNeighbour` (nothing outside
it is), `memsetOutOfRange` (overrun is UB). With this and the vector-field gep
of 3.3, `fd_ed25519_point_set_zero` lifts verbatim.

What is still missing is the bulk *copy* -- `llvm.intr.memcpy` -- which the
same machinery would take, reading a range instead of replicating a byte.

### 7.4 `llvm.mlir.zero` has no operation, and there is no null pointer

```
Error: Unsupported operation 'llvm.mlir.zero'
```

`fd_ed25519_point_frombytes` returns `NULL` when the encoding names no point,
which the artifact materialises as `llvm.mlir.zero : () -> !llvm.ptr` and
passes as the block argument of the failing `cond_br`. The operation did not
parse, and there was nothing for it to denote to: `SLLVM.Ptr` is
`PoisonOr Pointer`, whose only non-`Pointer` inhabitant is poison, and null is
not poison -- C code returns it as a sentinel and the caller branches on it,
so a spec has to be able to state "the result *is* NULL".

**FIXED (2026-09-07).** `SLLVMOp.nullptr : () -> ptr`, pure, denoting to
`SLLVM.Ptr.null = .value ⟨SLLVM.nullBlock, 0⟩`. `llvm.mlir.zero` dispatches on
its result type: `!llvm.ptr` gives that, an integer type gives
`Op.const w 0`, and anything else is rejected.

`SLLVM.nullBlock` is block `0`, *reserved* -- the one id no `alloca` may hand
out and no global may be loaded at, so that null aliases nothing. `alloca`
takes `AllocState.nextFreeBlock` and never rewinds, and `GlobalState.withGlobal`
allocates the same way, so a state whose counter starts above `0` never names
it. The model does not enforce that. Until 7.5 that cost nothing -- no operation
compared pointers, so null only ever appeared as a returned value a spec
states literally. With `ptricmp` it does: a region that branches on
`p == NULL` needs `p.id ≠ SLLVM.nullBlock` as a hypothesis, which is what
`fd_ed25519_point_frombytes_2x_conforms` carries.

Tests in [`SLLVM/Tests/Null.lean`](../SLLVM/Tests/Null.lean).

### 7.5 `llvm.icmp` cannot compare pointers

```
Error: Expected type `bitvec _`, but found: !ptr
```

`fd_ed25519_point_frombytes_2x` null-checks what `fd_ed25519_point_frombytes`
hands back, which the artifact emits as `llvm.icmp eq` at `!llvm.ptr`. The
parser's `llvm.icmp` case reads the operand width with `getIntWidth`, which
refuses anything that is not a `bitvec`, and `Op.icmp` is a scalar integer
comparison.

**FIXED (2026-09-07).** `SLLVMOp.ptricmp (eq : Bool) : (ptr, ptr) -> bitvec 1`,
pure. Poison in either operand is poison out; two pointers are equal exactly
when block and offset are. The parser dispatches on the operand type, so the
integer form is untouched, and only `eq`/`ne` are accepted at `!llvm.ptr` --
the ordered predicates would need an address ordering the model does not have.

LLVM's provenance rules make pointer equality weaker than this in general
(comparing pointers into distinct objects is unspecified); every use here
compares against `null`, where it is not.

Tests in [`SLLVM/Tests/PtrIcmp.lean`](../SLLVM/Tests/PtrIcmp.lean).

### 7.6 `llvm.bitcast` has no operation

```
Error: Unsupported operation 'llvm.bitcast'
```

`fd_r43x6_unpack` re-cuts a `uint256` into six 43-bit limbs with a byte
permute, which the compiler emits as `vector<8xi64> -> vector<64xi8>`, a
64-lane `shufflevector`, and a cast back. Neither cast parsed.

**FIXED (2026-09-07).** `SLLVMOp.bitcast (src dst : LLVM.Ty) : (arith src) ->
arith dst`, pure, denoting to `SLLVM.bitcast`: the source's flat bit pattern
(`LLVM.Ty.flattenBV`, which memory already used) read back at the destination
(`LLVM.Ty.unflatten`). Poison in any lane is poison out -- a destination lane
may straddle several source lanes, so there is no finer answer. The widths
agree in any well-formed module; `BitVec.setWidth` is what makes that an
equation rather than a hypothesis.

Tests in [`SLLVM/Tests/Bitcast.lean`](../SLLVM/Tests/Bitcast.lean).

### 7.7 `llvm.select` is scalar-only

```
Error: Expected type `bitvec _`, but found: i64×8
```

`fd_r43x6_ge_decode2` chooses between two field elements with a lane-wise
`llvm.select` under a `vector<8xi1>` mask -- `fd_r43x6_if`, the branch-free
conditional the backend uses everywhere. `Op.select` is scalar, and the
parser read the arm width with `getIntWidth`.

**FIXED (2026-09-07).** `SLLVMOp.vselect (l w : Nat)`, pure, `l` lanes of `w`
bits chosen lane for lane. The parser dispatches on the arm type, so the
scalar form is untouched. Denotes to the scalar `LLVM.select` per lane, which
is where poison handling comes from: a poison *mask* lane poisons that lane
only.

Tests in [`SLLVM/Tests/Bitcast.lean`](../SLLVM/Tests/Bitcast.lean).

### 7.8 `llvm.intr.memcpy` has no operation

```
Error: Unsupported operation 'llvm.intr.memcpy'
```

The bulk copy 7.3 left open. `fd_r43x6_ge_decode2` copies each 32-byte
encoding into an aligned local before loading it as a `wv_t`.

**FIXED (2026-09-07).** `SLLVMOp.memcpy : (ptr, ptr, i64) -[.impure]-> []`,
`memset`'s machinery reading a range instead of replicating a byte. UB
conditions are `memset`'s, on both blocks. The source is read before the
destination is written, so overlapping ranges -- which LLVM leaves undefined
-- copy what was there rather than being UB; `isVolatile` is accepted and
discarded.

Tests in [`SLLVM/Tests/Memory.lean`](../SLLVM/Tests/Memory.lean):
`memcpyMoves`, `memcpyOutOfRange`.

---

## 8. MLIR toolchain limitations (not lean-mlir, but they gate the pipeline)

### 8.1 `mlir-translate` rejects inline asm

```
$ mlir-translate --import-llvm fd_curve25519_ref.ll
error: unhandled value: ptr asm "", "=r,0,~{dirflag},~{fpsr},~{flags}"
```

The ref build of `fd_curve25519.c` contains **26** inline-asm sites, from
`fd_type_pun`, `FD_COMPILER_FORGET` and `FD_ADDRESS_OF_PACKED_MEMBER` in
`src/util/fd_util_base.h`. The ref point layer therefore **cannot be imported at
all**, before any question of branches or memory. The avx512 build imports
(14 633 lines) once its two `FD_COMPILER_MFENCE` barriers are stripped.

The existing field-level harness escapes this only because the fiat-crypto
routines do not use those macros.

### 8.2 MLIR SROA and mem2reg cannot promote the point locals

Running the promotion passes on the imported module has **exactly zero effect**:

| passes | alloca | load | store | gep |
|---|---|---|---|---|
| none | 37 | 270 | 183 | 271 |
| `--sroa --mem2reg` | 37 | 270 | 183 | 271 |
| `--sroa --mem2reg --canonicalize --cse` | 37 | 270 | 183 | 271 |

The allocas escape — their addresses are passed to the outlined field-operation
calls — so no promotion pass can touch them while those calls stand.

### 8.3 Lifting CFG to SCF does not apply to the `llvm` dialect

`mlir-opt --lift-cf-to-scf` exists in MLIR 18 and 19 but operates on the `cf`
dialect, and stock MLIR has no `llvm` → `cf` conversion. On the imported module:
49 `llvm.cond_br` before, 49 after, 0 `scf.if` produced.

This closes the otherwise-appealing route of lifting branch diamonds to
`scf.if` so that lean-mlir would need only region parsing rather than branches
in `Com`.

---

## 9. Measured impact on the ed25519 equivalence proof

### 9.1 Field layer — works today

The harness in `conformance_verification/` scalarises the ref interface (limbs
by value, one limb per probe) so `-O2` + SROA leaves no memory behind, and both
fiat-crypto and `fd_r43x6.h` are straight-line by construction. Result: across
all 38 extracted regions there are **0 memory operations, 0 branches, 0 phis**.

Parse status via `Com.parseFromFile SLLVM`:

```
ref     25 / 25  OK
avx512   6 / 13  OK
         4 fail: llvm.call  (fd_mlir_r43x6_{mul,sqr} and the _fast wrappers)
         3 fail: vpermi2var (approx_carry_propagate, fold_signed, sub)
```

Lifting is genuinely verbatim: `Avx512/Mlir/fd_r43x6_sqr_fast.lean` is
**byte-identical** to `build/native/gcc/mlir/avx512/region/fd_r43x6_sqr_fast.mlir`.

**Update.** The two `_quad_` regions no longer need the extraction probe at
all. `Avx512/Mlir/fd_r43x6_quad_sqr_fast_mem.lean` is byte-identical to
`build/native/gcc/mlir/avx512/region/fd_r43x6_quad_sqr_fast.mlir` — the kernel
with its three `!llvm.ptr` out-parameters and three
`llvm.store … : (vector<8xi64>, !llvm.ptr) -> ()`. It parses, denotes, and is
proved in `Avx512/Proof/fd_r43x6_quad_sqr_fast_mem.lean`:

```
$ lake exe opt --sllvm build/native/gcc/mlir/avx512/region/fd_r43x6_quad_sqr_fast.mlir
ok: [i64×8, i64×8, i64×8, !ptr, !ptr, !ptr] -[EffectKind.impure]-> []
```

(`lake exe opt` without `--sllvm` still parses with the `LLVM` dialect, which
has no memory operations — see 3.1.)

### 9.2 Point layer — blocked

Point operations taken **as written** (option flags remain runtime parameters;
only inlining forced, which is a pipeline flag rather than a source change):

| | ops | br i1 | blocks | alloca | load | store | gep | call |
|---|---|---|---|---|---|---|---|---|
| ref `add_with_opts` | 484 | 4 | 11 | 9 | 63 | 72 | 111 | 21 |
| ref `sub_with_opts` | 484 | 4 | 11 | 9 | 63 | 72 | 111 | 21 |
| ref `partial_dbl` | 213 | 0 | 1 | 5 | 26 | 23 | 43 | 11 |
| avx512 `add_with_opts` | 664 | 1 | 4 | 0 | 12 | 3 | 10 | 180 |
| avx512 `sub_with_opts` | 48 | 1 | 4 | 1 | 3 | 5 | 4 | 3 |
| avx512 `partial_dbl` | 250 | 0 | 1 | 0 | 3 | 3 | 4 | 58 |

The two sides are markedly asymmetric. The avx512 operations touch memory in
exactly one shape — a constant field index into the 4-field point struct:

```llvm
%5 = getelementptr inbounds %struct.fd_curve25519_edwards, ptr %1, i64 0, i32 1
%6 = load <8 x i64>, ptr %5, align 64
```

No dynamic indices, no aggregate allocas. `fd_ed25519_partial_dbl` is a **single
basic block with zero branches**. What it needs from lean-mlir is a short list:
3.5 (vector load/store), 3.3 (constant-index gep), 6.3 (`!llvm.ptr`), and 2.1/2.2
(the store fixes). `point_add_with_opts` adds exactly one branch (5.1).

Of that list, **all but 3.3 are now done**. A constant-index
`getelementptr` is the single remaining blocker for `fd_ed25519_partial_dbl`,
and it is a small one: the shape is always
`getelementptr inbounds %struct, ptr %p, i64 0, i32 k`, which is `ptr.add` by a
statically-known byte offset. The rest of the machinery it needs — vector
load/store of exactly this `<8 x i64>` shape, `!llvm.ptr` block arguments,
correct store semantics, and lemmas to reason about the result — is what the
quad kernel exercised end to end.

The ref side needs all of the above plus 3.4 (aggregate alloca), general gep,
four branches per operation, and 8.1 (inline-asm import).

*(Update 2026-08-24: the first ref point operation is in.
`fd_ed25519_point_is_zero` -- struct geps, an aggregate alloca in its `eq`
callee, and the full call chain down to the fiat kernels -- lifts verbatim
and passes differential `#guard`s; see 3.3, 3.4, 4.1, 5.1. What still gates
`point_add_with_opts` on the ref side is 8.1 and its four branches' worth of
lifted callees, not expressibility.)*

### 9.3 The ladder — not a lean-mlir problem

`fd_ed25519_double_scalar_mul_base` contains three loops (fixed-count table
build; data-dependent leading-zero scan; the ≤256-iteration dbl-and-add ladder)
and an 18-way path split per iteration (3-way on `sign(n1slide[i])` × 3-way on
`sign(n2slide[i])` × 2-way on `i == 0`). `fd_curve25519_scalar_wnaf` adds three
more loops, two nested, with `break`/`continue`.

None of this needs to be lifted. Both builds run the *same* ladder source over
the *same* wNAF digits, so the two executions take the same path iteration by
iteration; only the point operations underneath differ. The congruence argument
("related points in ⇒ related points out") is an induction over the digit list
in plain Lean, with the 18-way split as an `rcases`. Every ladder-path operation
exists on both sides with the same name and signature — `partial_dbl`,
`point_add_final_mul`, `point_add_final_mul_projective`, `point_add_with_opts`,
`point_sub_with_opts`, `into_precomputed`, `point_dbln`, `point_set_zero`,
`point_neg`, `point_eq_z1`, `point_frombytes_2x` — so the correspondence is 1:1.

The `ai[n1slide[i]/2]` table lookup is a load from a data-dependent index, but
it can be hoisted: in the congruence lemma it is just "some point from the
table", i.e. a universally quantified argument, so the lifted region never
contains the indexed access.

---

## 9a. A block-sized walk is the unit of proof, and it does not divide

`fd_r43x6_ge_decode2`'s `^bb0` is ~200 instructions -- both decodes, the `u`/`v`
chain, the square root and the sign fixup. Peeled as one theorem it takes
2m12s, and the cost is not any one tactic: `simp` under `denote_eval` /
`simp_peephole` is 62s of it, and the *same* step costs 0.2s early and 0.9s
late, because every tactic works against the valuation spine and the residual
program, both of which only grow.

The tail blocks do divide -- `bb1_run`, `bb2_run`, ... are stated as

    StateT.run (fd_r43x6_ge_decode2.blocks.run V bb1) s = ...

and entered with `denote_enter_block`, which resolves the `Blocks.get`. That
names a *whole* block. A suffix of a block has no name, so a mid-block cut
cannot be stated at all: one cannot write a lemma about a program one cannot
write down.

**Naming the suffix does not work.** `BlockCom.drop n c` -- dependent, since
the context grows one type per instruction -- with `take n c` for the prefix's
effect and `denote_eq_take_drop` was implemented and proved, and each half of
`^bb2` worked on its own. The *seam* is what fails: the prefix ends with
`exact tail …`, which asks the elaborator for
`residual =?= (BlockCom.drop 56 bb2Body).2`, and since `drop` compiles to
`Nat.brecOn`, `whnf` builds a 56-deep `Nat.below` tower over a term that is
the whole region. It does not finish in fifteen minutes, against 71s for the
undivided walk. That work was reverted.

**Sealing the valuation does, and is not worth it yet.** `denote_seal`
replaces the accumulated spine with a fresh opaque variable and keeps exactly
the facts the rest of the block reads, never naming the program:

    denote_seal W with x235 := hv235, c17 := env.c17, …
    denote_number_from 259

leaves the residual `BlockCom` in the goal untouched, `W` in place of the
spine, and `x235 : W ⟨23, _⟩ = …`, `c17 : W ⟨237, _⟩ = …` in the context. Each
index is found by the tactic -- a value the walk pushed is located in the
spine, a read of the ambient valuation is shifted by the spine's height, and
anything else is probed for in the block's arguments -- so the cut is written
in terms of the names the proof already uses. `denote_number_from` re-anchors
the stepper, which reads its index off the valuation's depth.

Three cuts in `^bb2` (`%222`, `%258`, `%280`) take it from a 110-deep spine to
four chunks of 20, 36, 22 and 32:

| | elaboration | kernel | file |
|---|---|---|---|
| `bb2_run`, undivided | 71.6s | 4.4s | 79.7s |
| three seals | 39.0s | 9.8s | 54.7s |

**It is archived on `archive/denote-seal`, not on the main branch.** One proof
was ever cut, and the cut costs a 33-entry list of crossing facts to write --
which is the block's internal contract, but it is 33 lines of it. The saving
is a third of one proof; the complexity is a tactic in the shared layer plus a
change to `fold_unsigned`'s constant search. Until it applies to `^bb0` as
well, that trade is not worth taking, so the branch was reset to before it.

Applying it to `^bb0` -- 200 instructions and 2m54s, the largest single proof
in the tree -- is what would change the arithmetic. A cut at `%106` was tried
on that branch: the prefix, constants lifted above it and the thirty-nine
crossing facts written out, comes to 57s, so the half of the split the tactic
handles works at that scale too. The second half does not, for three reasons,
in the order they bite.

* `fold_unsigned` finds the fold's three constants by searching the local
  context for `v = toBitVecValue 64 #v[…]`. After a seal the constant sits
  behind a read of the sealed valuation, `W ⟨192, _⟩ = v6`, so the search has
  to follow one more link and the pre-seal hypothesis has to be gone, or it
  finds that instead. Both are fixed on the archive branch.
* Inlining. `c6 := hv6` seals the *value* of a constant, so every later fold
  carries `toBitVecValue 64 #v[8796093022207, …]` where it used to carry the
  fvar `v6`. Seal `c6 := v6` instead and keep `hv6`.
* `peel_load_vec`, `peel_lifetime` and `peel_call` resolve their operands with
  a fixed `simp only` and take no `with` clause, so a sealed operand -- the
  four `alloca` slots `%49`-`%52`, which `%157`'s `fd_r43x6_pow22523_2` call
  and the lifetime ends read -- cannot be resolved, and the tactic grinds in
  its fallback rather than failing. `peel_store_amb`/`peel_load_vec_amb` in
  `Proof/Point/fd_r43x6_ge_decode2_blocks.lean` are the two-pass versions with
  a `with` clause that `^bb2` needed for the same reason; the shared tactics
  want the same treatment first. **This is the blocker.**

The bisection, for whoever picks this up: with the `%106` seal in place and a
`sorry` at successive points, the prefix is 57s, `%111` 61s, `%136` 71s,
`%156` 80s, and `%157`-`%158` -- the `pow22523_2` call and the two loads that
read its out-parameters back -- does not finish. Nothing between `%107` and
`%156` is anomalous.

Marking the cuts in the `[sllvm| … ]` quotation itself -- an antiquotation for
a chunk boundary -- would not help on its own: what a cut needs is the list of
*facts* that cross it, and the quotation does not know which values a proof
still reads. It would help with the half of the job the tactic still does by
search, namely fixing the boundary at a named instruction rather than at a
count of steps; `denote_seal` currently takes neither, since it reads the
spine out of the goal. The list of crossing facts is what a quotation-level
marker could not supply, and it is the part that costs.

Where the undivided walk spent its time, which is what says the spine is the
cost: `denote_eval`'s `simp_peephole` 28.5s, the local
`peel_load_vec_amb`/`peel_store_amb` 10.1s and 10.0s, `denote_step_reduce …
fold` 5.3s. Every one of them is a traversal of the accumulated spine.
Narrowing the peel macros' first simp pass (dropping `simp_sllvm`) changed
nothing measurable.

What is *not* the lever, measured on the same walk (353 hypotheses, 19k chars
of hypothesis types, 5.4k of goal):

| cleanup | share of context | effect |
|---|---|---|
| 65 state-chain facts (`hequ`/`hwf`/`heq`/`hu`) | small terms | 2m17s -> 2m14s |
| 24 spent `hrun*` run equations (the 20 largest types) | 21% | 2m14s -> 2m12.5s |
| 2 hypotheses holding *unfolded* fold denotations (`hv84`/`hv93`) | 2 hypotheses | 2m12s -> 1m54s |

So the number of hypotheses barely matters and their pretty-printed size barely
matters; what costs is a hypothesis whose right-hand side is an un-named
denotation nest, because every later tactic traverses it. The rule that pays is
to fold a stepped instruction into a named fact and `denote_clear` the raw one
immediately. Everything else is 1-2% a round.

---

## 10. What would unblock what

| Fix | Effort | Unblocks | Status |
|---|---|---|---|
| Un-reserve `nsw`/`nuw`, or accept the generic form in quotations (6.1) | hours | 19/25 ref regions | **done** |
| Add `vpermi2var` (7.1) | 1–2 days | 3/13 avx512 regions | open |
| Add `extractelement` (7.2) | hours | every scalar-limb operation: `is_nonzero`, `diagnose`, `mod`, `pack` | **done** |
| Accept generic-form `llvm.icmp` (6.5) | hours | every region with a comparison | **done** |
| Fix `store` mask and shift (2.1, 2.2) | hours | correctness of any future memory proof | **done** |
| Fix the printer round-trip (6.2) | hours | print/parse round-tripping | open |
| Drop `-fno-inline`, or split with `Zipper` (4.1) | days | 4/13 avx512 regions | open |
| Seal a block's valuation mid-walk (9) | days | the cost of every long block | archived (`archive/denote-seal`) |
| Vector load/store + `!llvm.ptr` + memory lemmas (3.5, 6.3, 3.7) | weeks | the avx512 kernels *as written* | **done** |
| Single-dynamic-index gep (3.3, ref shape) | hours | `fd_f25519_is_zero` and the ref field layer | **done** |
| Struct constant-index gep + aggregate alloca (3.3, 3.4) | days | `fd_ed25519_point_is_zero`; the point-op locals | **done** |
| CFG-layer calls (`BlockCom.call`, 4.1) | days | the whole ref call graph, verbatim, no `-fno-inline` games | **done** |
| Zero-leading two-operand gep fold (3.3) | days | `fd_f25519_set`, `fd_ed25519_point_from`, most `->limb[k]` accesses | **done** |
| Aggregate alloca + general gep + pointer select (3.4) | 1–2 months | ref point layer | open |
| Surface `!mem`, `loadPure`, `storePure` (3.6) | weeks | memory peepholes under the existing theorem | open |
| Forward acyclic CFG: parse + denote (5.1, 5.3) | days | `fd_f25519_is_zero`; any branch-diamond region, incl. the point ops' | **done** |
| Back-edges / loops in the CFG layer (5.1) | days | `fd_f25519_pow22523`; any looping region (nontermination = UB, per `mustProgress`) | **done** |
| Generalise `Scf` off `ℤ` + Scf region parsing (5.2) | research-scale | structured loops over real types | open |
| Accept a `Ty.arith` field in `llvm.insertvalue` (7.3) | hours | verbatim lifting of any AVX-512 region that materialises an `fd_f25519` global | **done** |


## 7.3 `llvm.insertvalue` rejects a vector field

`SLLVMOp.insertvalue` is typed `(bitvec aggW, bitvec fieldW) -> bitvec aggW`:
aggregate registers are modelled by their flat, padded layout, so inserting a
field is a bit-splice. The parser reads the field operand's width with
`getIntWidth`, which throws on anything that is not a `bitvec`.

That is fine for the ref side, whose `struct.fd_f25519` field is
`!llvm.array<5 x i64>` -- a flat 320-bit `bitvec`. It is not fine for AVX-512,
whose field is `vector<8xi64>`, modelled as a vector type rather than a
512-bit `bitvec`:

```
error: Expected type `bitvec _`, but found: i64×8
```

`fd_ed25519_affine_is_small_order` is the first AVX-512 region to use
`llvm.insertvalue` at all. It hits this twice, in the chains `%1`--`%5` and
`%7`--`%11` that materialise the two `@fd_ed25519_order8_point_y{0,1}`
initialisers. Both chains are **transitively dead** -- `%5` and `%11` have no
use, and nothing else consumes the chain -- so the lift drops them and says so
in its module docstring. Only the `addressof`es `%6`/`%12` are live.

**Fixed.** `SLLVMOp.insertvalue` now carries the field's `LLVM.Ty` rather than
its width:

```
| insertvalue (aggW offBits : Nat) (fieldTy : LLVM.Ty)
```

with signature `(bitvec aggW, Ty.arith fieldTy) -> bitvec aggW` and denotation
`SLLVM.insertvalue off agg (LLVM.Ty.flatten fieldTy v)`. `LLVM.Ty.flatten` is
the existing flat, in-memory encoding of an arbitrary arithmetic value, poison
unless every lane is defined -- exactly the aggregate-register model
`insertvalue` already assumed, now applied to vectors as well as scalars.

Behaviour at a `bitvec` field is unchanged: `flatten_bitvec` (in
`Dialect/Basic.lean`) proves `LLVM.Ty.flatten (.bitvec w) x = x`, so every
pre-existing use denotes exactly as before. The parser reads the operand's type
with `argArithTy` instead of `getIntWidth`, and keeps the width check against
the field the position walk selects.

Consequences, now realised:

* `Avx512/Mlir/Point/fd_ed25519_affine_is_small_order.lean` lifts **verbatim**,
  dead constant chains and all -- no deletion, no argument for the reader to
  accept;
* the AVX-512 global initialisers lift too, so
  `Conformance/Spec/Order8.lean` pins its limbs against
  `Avx512/Mlir/Point/fd_ed25519_order8_point_y{0,1}.lean` with `#guard`
  rather than retyping them by hand.

## 8.4 `fd_ed25519_affine_is_small_order`: what is and is not claimed

Each backend's specification (`Ref/Spec/Point/…`, `Avx512/Spec/Point/…`) states
the functional claim: the region returns the indicator of
`(P.X, P.Y) ∈ lowOrder`, the eight low-order points listed in
`Common/Spec/fd_ed25519_affine_is_small_order.lean`, under `Z = 1` and the curve
equation -- the hypotheses that make the region's `X = 0 ∨ Y = 0 ∨ Y = y0 ∨ Y =
y1` shortcut decide membership (`isSmallOrderTest_iff_mem`). Conformance
(`Conformance/Proof/…`) is then the composition of the two.

Not claimed anywhere: that these eight are *all* the points of order dividing 8.
The group law is not formalised (`Curve.lean` stops at representation and
cross-multiplication), so the order labels are documentation from the C comment
and RFC 8032, not theorems.
