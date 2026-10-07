import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableCalls
namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common Firedancer.Ref _root_.Ed25519
abbrev firedancerReachableSpec (programs : FiredancerShaPrograms) (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer)
    (s : GlobalState) (hmsg : Fits s.mem msg (sz.toNat * 8)) (hr : IsByteBufPtr s.mem sig)
    (hS : IsByteBufPtr s.mem (sig.withOffset 32)) (ha : IsByteBufPtr s.mem pk)
    (f : BitVec (64 * 8) → Option (Fin 4 → BitVec 64)) (kbits : BitVec (80 * 64))
    (b₀ b₁ b₂ b₃ b₄ : Option LiveBlock) (dig : BitVec 512) :
    Prop :=
  let invocation :=
    runFunction
      ((firedancerRefProgram programs).denote
        (Ctxt.Valuation.ofHVector [.value sha, .value pk, .value sig, .value sz, .value msg]ₕ))
  let result := StateT.run invocation s
  let r := readBuf hr
  let S := (readBuf hS).toNat
  let a := readBuf ha
  let B := basePoint.toAffine wellFormed_basePoint
  sig.offset.toNat + 64 ≤ 2 ^ 64 →
    msg.offset.toNat + sz.toNat ≤ 2 ^ 64 →
    IsSha512Ptr s.mem sha →
    sha.offset.toNat + 256 ≤ 2 ^ 64 →
    Sha512KHolds s sha kbits →
    sha.id ≠ sig.id →
    sha.id ≠ pk.id →
    sha.id ≠ msg.id →
    s.RefWF [sha] →
    FiredancerReachableMemoryReady s msg sig pk →
    ScalarReduceBy f →
    FiredancerReachableInit programs (s.mem.live? sha.id) b₀ sha.offset →
    FiredancerReachableAppend programs kbits b₀ b₁ sha.offset (bytesOf (n := 32) r) →
    FiredancerReachableAppend programs kbits b₁ b₂ sha.offset (bytesOf (n := 32) a) →
    FiredancerReachableAppend programs kbits b₂ b₃ sha.offset (bytesOf (readWord hmsg)) →
    FiredancerReachableFinish programs kbits b₃ b₄ sha.offset dig →
    ∀ Bt,
      BaseTableHolds s Bt →
        BaseVals Bt basePoint wellFormed_basePoint →
        ∀ w,
              f dig = some w →
                ∃ (s' : GlobalState) (ret : BitVec 32),
                  result = .value ([.value ret]ₕ, s') ∧
                    s'.alloc = s.alloc ∧
                    s'.globals = s.globals ∧
                    (∀ b : BlockId, b ≠ sha.id → s'.mem.live? b = s.mem.live? b) ∧
                    ret ∈
                      [FD_ED25519_SUCCESS, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY,
                        FD_ED25519_ERR_MSG] ∧
                    (ret = FD_ED25519_ERR_SIG ∨ ret = FD_ED25519_ERR_PUBKEY → s ≈ s') ∧
                    -- a run that hashed leaves `sha` as `fini` does; the others never write it
                    (ret = FD_ED25519_SUCCESS ∨ ret = FD_ED25519_ERR_MSG →
                      ∀ shaBlk,
                        some b₄ = some shaBlk →
                          s'.mem.live? sha.id = shaBlk) ∧
                    (groupOrder ≤ S → ret = FD_ED25519_ERR_SIG) ∧
                    (S < groupOrder → (¬∃ A, Encodes a A) → ret = FD_ED25519_ERR_PUBKEY) ∧
                    (S < groupOrder →
                      (∃ A, Encodes a A) → (¬∃ R, Encodes r R) → ret = FD_ED25519_ERR_SIG) ∧
                    (S < groupOrder →
                      ∀ A R,
                        Encodes a A →
                          Encodes r R →
                          ((A.x, A.y) ∈ lowOrder → ret = FD_ED25519_ERR_PUBKEY) ∧
                            ((A.x, A.y) ∉ lowOrder →
                              (R.x, R.y) ∈ lowOrder → ret = FD_ED25519_ERR_SIG) ∧
                            ((A.x, A.y) ∉ lowOrder →
                              (R.x, R.y) ∉ lowOrder →
                              (ret = FD_ED25519_SUCCESS ↔
                                  ((packWords w).toNat % 2 ^ 255) • -A + S • B = R) ∧
                                (ret = FD_ED25519_SUCCESS ∨ ret = FD_ED25519_ERR_MSG)))

end Agave.Ed25519.Bridge
