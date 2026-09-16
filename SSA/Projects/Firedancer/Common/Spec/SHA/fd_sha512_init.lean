/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.VecNotation
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_init
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_sha512_init` (common)

Every value the region stores is a constant, so this is an exact specification
rather than a frame one: the eight FIPS 180-4 initial hash words land in
`state[0..7]`, `buf_used`, `bit_cnt_lo` and `bit_cnt_hi` are zeroed, the handle
is returned, and nothing else changes. `buf` is left as it was -- the C says
"d/c" -- as is the `i64` between `state` and `buf_used`.

`fd_sha512_private` is laid out `(buf[128], state[8], _, buf_used, bit_cnt_lo,
bit_cnt_hi, _[32])`, so `state[k]` is at byte `128 + 8k` and the three counters
at bytes 200–223. The region zeroes the counters with one 24-byte `memset`
rather than three stores.
-/

namespace Firedancer.Common

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The SHA-512 initial hash value, FIPS 180-4 §5.3.5. -/
def sha512IV : Fin 8 → BitVec 64 :=
  ![0x6a09e667f3bcc908#64, 0xbb67ae8584caa73b#64, 0x3c6ef372fe94f82b#64, 0xa54ff53a5f1d36f1#64,
    0x510e527fade682d1#64, 0x9b05688c2b3e6c1f#64, 0x1f83d9abfb41bd6b#64, 0x5be0cd19137e2179#64]

/-- The memory `fd_sha512_init` leaves: `state[k] := sha512IV k` at `128 + 8k`,
then 24 zero bytes at 200, in the order the region writes them. A `def`, like
`pointOutMem`, so unifiers do not walk nine splices on sight. -/
def sha512InitMem (m : MemoryState) (sha : Pointer) : MemoryState :=
  ((((((((m.splice (sha.withOffset 128) (sha512IV 0)).splice (sha.withOffset 136)
                                (sha512IV 1)).splice
                            (sha.withOffset 144) (sha512IV 2)).splice
                        (sha.withOffset 152) (sha512IV 3)).splice
                    (sha.withOffset 160) (sha512IV 4)).splice
                (sha.withOffset 168) (sha512IV 5)).splice
            (sha.withOffset 176) (sha512IV 6)).splice
        (sha.withOffset 184) (sha512IV 7)).splice
    (sha.withOffset 200) (BitVec.replicate 24 (0#8))

/-- A `fd_sha512_t` at `sha`: the whole 256-byte struct is addressable. -/
abbrev IsSha512Ptr (m : MemoryState) (sha : Pointer) : Prop :=
  Fits m sha (256 * 8)

/-- **`fd_sha512_init` resets the hash state.** It returns `sha` and leaves the
entry state with `sha512InitMem` applied: allocation counter, symbol table and
every block other than `sha`'s untouched. -/
abbrev fd_sha512_init_spec (sha : Pointer) (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_sha512_init.denote (Ctxt.Valuation.singleton (.value sha)))
  ∃ s' : GlobalState,
    StateT.run invocation s = .value ([.value sha]ₕ, s') ∧
      s' ≈ ({ s with mem := sha512InitMem s.mem sha } : GlobalState)

end Firedancer.Common
