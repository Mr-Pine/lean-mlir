/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.fd_ed25519_verify
import SSA.Projects.Firedancer.Ref.Proof.RefWF
import SSA.Projects.Firedancer.Ref.Spec.fd_ed25519_verify -- Should move out of Proof

namespace Firedancer

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519 Common

/-!
# `fd_ed25519_verify`'s globals, across the two builds

`Avx512.fd_ed25519_verify_spec` asks its caller for the two order-8 constants and the base table,
where the ref side reads them off `RefWF`. The two are not interchangeable: a symbol's *address* is
the loader's, the same for both builds, but its *contents* are the build's -- a field element is
five limbs in `ref` and a `wwl_t` in AVX-512, and a table entry is 160 bytes against 192.

So `RefWF` gives the AVX-512 spec everything except the layout: the addresses, and the table's
apartness from `sha`. What is left is `Avx512Globals`, which only the AVX-512 build can state.
The same split applies to `Bt`: `Ref.BaseTableHolds` says the ref table holds it, and
`Avx512Globals`' `tbl` says the AVX-512 table holds it, so assuming both is what says the two
builds tabulate the same points. They are assumed of two states: one state cannot carry both
layouts at the same symbols.
-/

/-- What the AVX-512 build holds at the symbols `RefWF` names: the two order-8 constants as
`wwl_t`s, and the base table as QUADs 192 bytes apart. Stated over whatever address the symbol
table gives, so it carries no address of its own. -/
structure Avx512Globals (s : GlobalState) (Bt : ℕ → PrecomputedPoint) : Prop where
  y0 :
    ∀ g,
      GlobalPtr s "fd_ed25519_order8_point_y0" g →
        ∃ h : Avx512.IsVecPtr s.mem g,
          Avx512.vecValue (Avx512.readVec h) = order8_y0 ∧ R43x6.Reduced (Avx512.readVec h)
  y1 :
    ∀ g,
      GlobalPtr s "fd_ed25519_order8_point_y1" g →
        ∃ h : Avx512.IsVecPtr s.mem g,
          Avx512.vecValue (Avx512.readVec h) = order8_y1 ∧ R43x6.Reduced (Avx512.readVec h)
  tbl :
    ∀ g,
      GlobalPtr s "fd_ed25519_base_point_wnaf_table" g →
        ∀ k < 128,
          ∃ h : Avx512.IsQuadPtr s.mem (g.withOffset (BitVec.ofNat 64 (192 * k))),
            (R43x6.U44 (Avx512.readQuad h).v03 ∧
                R43x6.U44 (Avx512.readQuad h).v14 ∧ R43x6.U44 (Avx512.readQuad h).v25) ∧
              (Avx512.readQuad h).NegBounds 3 ∧
              PrecomputedPoint.ofSlots (Avx512.readQuad h).toPoint = Bt k

/-- The globals `Avx512.fd_ed25519_verify_spec` asks for, in the order it asks for them. -/
abbrev Avx512.VerifyGlobals (s : GlobalState) (sha : Pointer) (Bt : ℕ → PrecomputedPoint) : Prop :=
  (∃ (g0 g1 : Pointer) (h0 : Avx512.IsVecPtr s.mem g0) (h1 : Avx512.IsVecPtr s.mem g1),
      GlobalPtr s "fd_ed25519_order8_point_y0" g0 ∧
        GlobalPtr s "fd_ed25519_order8_point_y1" g1 ∧
        Avx512.vecValue (Avx512.readVec h0) = order8_y0 ∧
        Avx512.vecValue (Avx512.readVec h1) = order8_y1 ∧
        R43x6.Reduced (Avx512.readVec h0) ∧ R43x6.Reduced (Avx512.readVec h1)) ∧
    Avx512.BaseTableHolds s sha Bt

/-- **`RefWF` supplies the AVX-512 globals.** A ref state fixes the three addresses and keeps the
table apart from `sha`; what is left is the layout at those addresses, which only the build itself
can state. -/
abbrev fd_ed25519_verify_globals_equivalent : Prop :=
  ∀ (s s' : GlobalState) (sha : Pointer) (Bt : ℕ → PrecomputedPoint),
    s.RefWF [sha] →
      Ref.BaseTableHolds s Bt →
      s'.globals = s.globals → Avx512Globals s' Bt → Avx512.VerifyGlobals s' sha Bt

/-- A ref state and an AVX-512 state that differ only in their globals: the same counter, the
same symbol table, and the same blocks under the four arguments. One state cannot be both --
`not_refWF_avx512Globals` -- since each build lays out its constants its own way. -/
structure VerifyStates (sR sA : GlobalState) (msg sig pk sha : Pointer) : Prop where
  alloc : sR.alloc = sA.alloc
  globals : sR.globals = sA.globals
  live : ∀ b ∈ [msg.id, sig.id, pk.id, sha.id], sR.mem.live? b = sA.mem.live? b

/-- **The two regions agree.** From a ref state `sR` and an AVX-512 state `sA` that differ only in
their globals, on the same signature, public key and message: both return, both return the same
code, the two final states agree wherever `sR` and `sA` did, and each leaves every block but `sha`
as it was.

`sR` is a module state for `ref` -- `RefWF` and its base table -- and `sA` holds the AVX-512
build's vectors at the same symbols. The digest and the reduced scalar are the caller's `fInit`/
`fApp`/`fFini`/`f`, so both regions hash and reduce the same way; what is compared is the rest. -/
abbrev fd_ed25519_verify_equivalent (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer)
    (sR sA : GlobalState) (hargs : VerifyArgs sR msg sz sig pk sha) (_hRef : sR.RefWF [sha])
    (_hA : sA.WF) (_hst : VerifyStates sR sA msg sig pk sha) : Prop :=
  ∀ (f : BitVec (64 * 8) → Option (Fin 4 → BitVec 64)) (kbits : BitVec (80 * 64))
    fInit fApp fFini fFiniBlk
    (Bt : ℕ → PrecomputedPoint) (dig : BitVec 512) (w : Fin 4 → BitVec 64),
    -- each build's tables, at its own state
    Ref.BaseTableHolds sR Bt →
      Avx512Globals sA Bt →
      BaseVals Bt basePoint wellFormed_basePoint →
      -- the hash and the reduction, as both regions call them
      Sha512KHolds sR sha kbits →
      Sha512KHolds sA sha kbits →
      ScalarReduceBy f →
      Sha512InitBy fInit →
      Sha512AppendBy kbits fApp →
      Sha512FiniBy kbits fFini fFiniBlk →
      ed25519Digest fInit fApp fFini (sR.mem.live? sha.id) sha.offset (readBuf hargs.sigBuf)
          (readBuf hargs.pkBuf) (bytesOf (readWord hargs.msgFits)) =
        some dig →
      f dig = some w →
      ∃ (sRef sAvx : GlobalState) (ret : BitVec 32),
        StateT.run
              (runFunction
                (Ref.fd_ed25519_verify.denote
                  (Ctxt.Valuation.ofHVector
                    [.value sha, .value pk, .value sig, .value sz, .value msg]ₕ)))
              sR =
            .value ([.value ret]ₕ, sRef) ∧
          StateT.run
              (runFunction
                (Avx512.fd_ed25519_verify.denote
                  (Ctxt.Valuation.ofHVector
                    [.value sha, .value pk, .value sig, .value sz, .value msg]ₕ)))
              sA =
            .value ([.value ret]ₕ, sAvx) ∧
          -- one code, and the final states agree where the initial ones did
          sRef.alloc = sAvx.alloc ∧
          sRef.globals = sAvx.globals ∧
          (∀ b : BlockId, sR.mem.live? b = sA.mem.live? b → sRef.mem.live? b = sAvx.mem.live? b) ∧
          -- each run leaves its own state off `sha`
          sRef.alloc = sR.alloc ∧
          sRef.globals = sR.globals ∧
          (∀ b : BlockId, b ≠ sha.id → sRef.mem.live? b = sR.mem.live? b) ∧
          ∀ b : BlockId, b ≠ sha.id → sAvx.mem.live? b = sA.mem.live? b

end Firedancer
