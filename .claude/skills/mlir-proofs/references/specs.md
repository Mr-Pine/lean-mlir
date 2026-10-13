# Specs

A function's spec has two layers, proved separately:

1. **bv level**: a pure Lean function over the values the C code manipulates (limbs as
   `Fin 5 → BitVec 64`, vectors as `Vector (BitVec 64) 8`, flags as `BitVec 32`), and an equation
   `f.call … = .value (rets, s')` whose `s'` writes that function's results. Callers chain these
   equations.
2. **mathematical meaning**, only where a caller or the final theorem needs it: what the bv
   function computes in the field, on the curve, or as a hash, under stated bounds.

No `∃ bytes, result = f bytes ∧ semantics bytes = …`: the result is given by an equation.

## The spec function

```lean
/-- `x + y` limbwise, without carrying, in the program's operand order. -/
def fiat_25519_add.spec (x y : Fin 5 → BitVec 64) : Fin 5 → BitVec 64
  | k => y k + x k
```

- Named `f.spec`, in the function's proof file, in an `@[expose] public section`.
- It mirrors the C source: one `let` per C variable, named as in C (`x1 … x152` for fiat), in C's
  operand order, so the steps' named values and the spec's `let`s line up.
- Every function gets its own `spec`, also when it only composes callees
  (`fd_f25519_add.spec a b := fiat_25519_carry.spec (fiat_25519_add.spec a b)`): callers then
  state their results with one name per call, and `hS` stays readable.
- Several outputs: one spec per output object when the C computes them independently, else one
  spec returning a structure (a point's four coordinates).
- A function that only sequences calls on separate objects (`fd_f25519_mul3`) needs no spec of
  its own: its `call_eq` stores the callees' specs in order, under the separation that makes each
  call read the inputs as they were (no output in the block of a later input). Without that
  separation every read would be of the previous memory and the terms would grow with each call.
- Bounds and algebraic properties of the spec are separate pure lemmas
  (`fiat_25519_carry.spec_bound`), never conjuncts of `call_eq`.

## The `call_eq` theorem

```lean
/-- `fiat_25519_add` stores `spec x y` limbwise at `out`. The loads all come before the stores, so
`out` may alias `x` or `y`. -/
public theorem fiat_25519_add.call_eq (out x y : Pointer) (s : GlobalState) (hwf : s.WF)
    (hout : s.mem.LimbsFit out) (hx : s.mem.LimbsFit x) (hy : s.mem.LimbsFit y) :
    fiat_25519_add.call (fiat_25519_add.args (.value out) (.value x) (.value y)) s =
      .value (.nil,
        { s with mem := s.mem.storeLimbs out (fiat_25519_add.spec (s.mem.readLimbs x) (s.mem.readLimbs y)) })
```

- **Arguments**: the pointers and scalars as plain values, passed as `.value p`; `s` and
  `hwf : s.WF` always; `hg : s.mem.Globals f.globals` when `f` or a callee takes a global's
  address. Outputs (stored to) need `Room` (live and writable); inputs only read need `Fits`/`Live`
  (a constant global's block has no `Room`).
- **Result**: an equation, `.value (rets, s')`; `rets` lists the returned values (`.cons (.value r)
  .nil`), `s'` the final state:
  - frame-free (no `alloca`): `{ s with mem := <writes over s.mem> }`;
  - framed: `{ alloc := ⟨s.alloc.nextFreeBlock + k⟩, mem := <writes over s.mem> }`, `k` the
    blocks the function allocates (its frame is erased, the counter is not).
- **Writes** go through the object's store function (`storeLimbs`), outermost last, in the order
  the code writes; values are spec functions of reads of `s` (`s.mem.readLimbs x`).
- **Branches** that change the result are `if`s in `rets`/`s'`, or inside the spec function.
- **Docstring**: what is stored where and returned, and what may alias.

## Preconditions

State exactly what the code needs, through named predicates:

- **Fit**: one predicate per C object and pointer (`s.mem.LimbsFit p` for a field element, an
  `abbrev` over the `Fits` conjuncts and the offset bound, so the tactics split it). A raw
  `Fits s.mem p (8 * n)` with `¬p.offset.uaddOverflow n#64` for byte buffers.
- **Inputs and outputs**: `Fits` (live, in bounds, every bit defined) for what the code reads;
  `Room` (live, in bounds, contents not needed) for what it only writes: an output buffer, a
  caller's fresh slot. A pointer read and written takes `Fits`. A spec that asks `Fits` of an
  output cannot be called on an uninitialized slot. State the post-state's facts the caller
  needs from what was stored (`Fits.storeAt_self : Room m p w → Fits (m.storeAt p x) p w`, a
  `Fits.storeLimbs`-style lemma for an object's store, `mlir_fresh` so the steps record it).
- **Separation**: only where the code's result depends on it: `r.id ≠ a.id`, or
  `[p.id, q.id, …].Nodup` for several.
- **Value bounds**: only where the code has UB without them (an `nsw` that can fire) or the
  result is only specified under them; through a named predicate (`LimbsBounded l b`).
- **Callees passed as parameters**: their spec as a hypothesis (below).

## Chaining callees

A caller's spec is written with its callees' spec functions, and its proof steps each call with
the callee's `call_eq`:

```lean
public theorem fd_f25519_add.call_eq (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : s.mem.LimbsFit r) (ha : s.mem.LimbsFit a) (hb : s.mem.LimbsFit b) :
    fd_f25519_add.call (fd_f25519_add.args (.value r) (.value a) (.value b)) s =
      .value (.cons (.value r) .nil,
        { s with mem := s.mem.storeLimbs r (fd_f25519_add.spec (s.mem.readLimbs a) (s.mem.readLimbs b)) })
```

A callee whose proof is not available (or whose semantics the caller should not depend on) is a
parameter of the lift, and its spec a hypothesis:

```lean
mlir_def fd_ed25519_point_frombytes_2x (frombytes : FromBytes) := { … }
  with @fd_ed25519_point_frombytes := frombytes

public abbrev FromBytes.Spec (frombytes : FromBytes) (ok : Pointer → Pointer → GlobalState → Bool)
    (post : Pointer → Pointer → GlobalState → GlobalState) : Prop :=
  (∀ h buf s, s.WF →
      frombytes (.cons (.value h) (.cons (.value buf) .nil)) s =
        .value (.cons (.value (if ok h buf s then h else Pointer.null)) .nil, post h buf s)) ∧
    ∀ h buf s, s.WF → ∀ k ∈ (post h buf s).mem.mem, k ∈ s.mem.mem
```

Prefer lifting and proving the callee; use the parameter form for callees outside the proof's
scope, and instantiate it with the proved callee before the final theorem.

## Mathematical meaning

In modules of their own (they may import Mathlib; the bv-level proofs never import them):

- a value function per representation (`Limbs.val l : ZMod p`, a point's affine coordinates);
- one theorem per spec function: `(fiat_25519_carry_mul.spec a b).val = a.val * b.val` under
  the bound predicates its inputs satisfy, and the bound its output satisfies;
- the top theorem restates the final `call_eq` in those terms.

Usually the direction is bv → math. The other direction is fine where it is simpler: a constant
table is easier to state as the encoding of the mathematical table and check than to decode.
