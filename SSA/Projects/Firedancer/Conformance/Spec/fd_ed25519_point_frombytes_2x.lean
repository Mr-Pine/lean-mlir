module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_frombytes_2x
public import SSA.Projects.Firedancer.Ref.Proof.RefWF -- Should move out of Proof
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
public import SSA.Projects.Firedancer.Curve

@[expose] public section

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- A point still fits wherever it fitted before the four coordinate stores:
`pointOutMem` is four splices, and a splice changes no block's liveness or
size. The generalisation of `Ref.isPointPtr_pointOutMem` to a pointer other
than the one written. -/
theorem Ref.isPointPtr_pointOutMem' {m : MemoryState} {p r : Pointer}
    (hp : Ref.IsPointPtr m p) (oX oY oZ oT : Fin 5 → BitVec 64) :
    Ref.IsPointPtr (Ref.pointOutMem m r oX oY oZ oT) p := by
  simp only [Ref.pointOutMem]
  exact Ref.isPointPtr_splice (Ref.isPointPtr_splice
    (Ref.isPointPtr_splice (Ref.isPointPtr_splice hp)))

/-- ... and a QUAD after the three whole-vector stores, for the same reason. -/
theorem Avx512.isQuadPtr_writeQuad {m : MemoryState} {p r : Pointer}
    (hp : Avx512.IsQuadPtr m p) (q : Quad) :
    Avx512.IsQuadPtr (m.writeQuad r q) p :=
  ⟨fits_splice (fits_splice (fits_splice hp.left)), hp.right⟩

abbrev fd_ed25519_point_frombytes_2x_equivalent : Prop :=
  ∀ (s : GlobalState) (a b aBuf bBuf : Pointer),
  (hs : s.RefWF [a, b]) → (ha : Ref.IsPointPtr s.mem a) → (hb : Ref.IsPointPtr s.mem b) → (haBuf : IsByteBufPtr s.mem aBuf) → (hbBuf : IsByteBufPtr s.mem bBuf) →
  (hbBufA : bBuf.id ≠ a.id) →
  -- Both regions write `b`'s point over `a`'s: if the two were the same object
  -- the second store would win, and the first point could not be read back.
  (hbA : b.id ≠ a.id) →
  -- What `Ref.fd_ed25519_point_frombytes_2x_conforms` asks of the caller: each
  -- buffer apart from the point it decodes into, and neither point the block
  -- `llvm.mlir.zero` names -- the region null-checks what it is handed back.
  (haBufA : aBuf.id ≠ a.id) → (hbBufB : bBuf.id ≠ b.id) →
  (haNull : a.id ≠ SLLVM.nullBlock) → (hbNull : b.id ≠ SLLVM.nullBlock) →

  let refResult' := StateT.run (runFunction (Ref.fd_ed25519_point_frombytes_2x.denote (Ctxt.Valuation.ofHVector [.value bBuf, .value b, .value aBuf, .value a]ₕ ))) s

  ∀ (s' : GlobalState) (a' b' aBuf' bBuf' : Pointer),
  (hs' : s'.WF) → (ha' : Avx512.IsQuadPtr s'.mem a') → (hb' : Avx512.IsQuadPtr s'.mem b') → (haBuf' : Avx512.IsWvPtr s'.mem aBuf') → (hbBuf' : Avx512.IsWvPtr s'.mem bBuf') → (hbA' : b'.id ≠ a'.id) →
  let avxResult' := StateT.run (runFunction (Avx512.fd_ed25519_point_frombytes_2x.denote (Ctxt.Valuation.ofHVector [.value bBuf', .value b', .value aBuf', .value a']ₕ ))) s'

  ((fun blk => blk.bytes.extractLsb' aBuf.offsetInBits 256) <$> s.mem.live? aBuf.id) = ((fun blk => blk.bytes.extractLsb' aBuf'.offsetInBits 256) <$> s'.mem.live? aBuf'.id) →
  ((fun blk => blk.bytes.extractLsb' bBuf.offsetInBits 256) <$> s.mem.live? bBuf.id) = ((fun blk => blk.bytes.extractLsb' bBuf'.offsetInBits 256) <$> s'.mem.live? bBuf'.id) →

  ∃ (refResult : _) (avxResult : _) (hrefResult : refResult' = .value refResult) (havxResult : avxResult' = .value avxResult),

    refResult.fst = avxResult.fst ∧

    refResult.fst = [.value 0#32]ₕ → (
      ∃ aX aY aZ aT bX bY bZ bT,
        let refMem := Ref.pointOutMem (Ref.pointOutMem s.mem a aX aY aZ aT) b bX bY bZ bT
        let refAfterState : GlobalState := { s with mem := refMem }
      ∃ aQuad' bQuad',
        let avxMem := (s'.mem.writeQuad a' aQuad').writeQuad b' bQuad'
        let avxAfterState : GlobalState := { s' with mem := avxMem }

        ∃ (href : refResult.snd ≈ refAfterState) (havx : avxResult.snd ≈ avxAfterState),
          let refA := Ref.readPoint (p := a) (m := refMem)
            (Ref.isPointPtr_pointOutMem' (r := b)
              (Ref.isPointPtr_pointOutMem' (r := a) ha aX aY aZ aT) bX bY bZ bT)
          let refB := Ref.readPoint (p := b) (m := refMem)
            (Ref.isPointPtr_pointOutMem
              (Ref.isPointPtr_pointOutMem' (r := a) hb aX aY aZ aT) bX bY bZ bT)

          let avxA := (Avx512.readQuad (p := a') (m := avxMem)
            (Avx512.isQuadPtr_writeQuad (Avx512.isQuadPtr_writeQuad ha' _) _)).toPoint
          let avxB := (Avx512.readQuad (p := b') (m := avxMem)
            (Avx512.isQuadPtr_writeQuad (Avx512.isQuadPtr_writeQuad hb' _) _)).toPoint

          refA = avxA ∧
          refB = avxB
    )

end Firedancer
