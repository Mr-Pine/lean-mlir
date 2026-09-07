/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# What `fd_long_if` is specified to compute

The conditional subtract of `p` in `fd_r43x6_mod_nearly_reduced_limbs`, as a
value rather than a branch: `19` when the condition holds, `0` when it does
not.

This is the *specialised* `fd_long_if`, not the general `c ? t : f`. The
function is `static`, so LLVM sees all its call sites and folds a parameter
that is the same constant at every one of them into the body, leaving the
region with a single argument. See `Mlir/fd_long_if.lean` for the measurement
behind that.

Poison propagates: `llvm.icmp` on a poison operand is poison, and
`LLVM.select` on a poison condition is poison however defined its arms are.
That matters here -- the condition reaching this region is a `zext` of an
`icmp` over the carry chain, so it is poison exactly when the chain is.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- `fd_long_if(c, 19, 0)`: the value the conditional subtract removes from
limb 0. C's condition is "non-zero", so the `0` case is the *false* one. -/
def fdLongIf : LLVM.IntW 32 → LLVM.IntW 64
  | .poison => .poison
  | .value c => .value (if c = 0#32 then 0#64 else 19#64)

@[simp] theorem fdLongIf_poison : fdLongIf .poison = .poison := rfl

@[simp] theorem fdLongIf_zero : fdLongIf (.value 0#32) = .value 0#64 := rfl

/-- The shape the caller uses it in: the condition is a `zext` of an `i1`, so
it is `0` or `1` and never anything else. -/
theorem fdLongIf_one : fdLongIf (.value 1#32) = .value 19#64 := rfl

end Firedancer.Avx512
