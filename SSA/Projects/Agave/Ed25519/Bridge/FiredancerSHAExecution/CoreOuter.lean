import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreBranches

/-! Actual scalar core outer-loop edges and feedforward stores. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

structure OuterStateReady (E : Env program.Γ) (s : State) : Prop where
  a : E.read (%51) = .value s.a
  b : E.read (%50) = .value s.b
  c : E.read (%49) = .value s.c
  d : E.read (%48) = .value s.d
  e : E.read (%47) = .value s.e
  f : E.read (%46) = .value s.f
  g : E.read (%45) = .value s.g
  h : E.read (%44) = .value s.h

structure OuterPointersReady (E : Env program.Γ) (chain data : Pointer) (n : Nat) : Prop where
  p0 : E.read (%arg0) = .value chain
  p8 : E.read (%29) = .value (chain.add 8#64)
  p16 : E.read (%30) = .value (chain.add 16#64)
  p24 : E.read (%31) = .value (chain.add 24#64)
  p32 : E.read (%32) = .value (chain.add 32#64)
  p40 : E.read (%33) = .value (chain.add 40#64)
  p48 : E.read (%34) = .value (chain.add 48#64)
  p56 : E.read (%35) = .value (chain.add 56#64)
  data : E.read (%52) = .value data
  count : E.read (%53) = .value (BitVec.ofNat 64 n)
  zero : E.read (%8) = .value 0#64
  minusOne : E.read (%13) = .value 18446744073709551615#64
  blockSize : E.read (%27) = .value 128#64

def outerNextEnv (E : Env program.Γ) (s : State) (data : Pointer) (n : Nat) : Env program.Γ :=
  E[%44 := .value s.h, %45 := .value s.g, %46 := .value s.f,
    %47 := .value s.e, %48 := .value s.d, %49 := .value s.c,
    %50 := .value s.b, %51 := .value s.a, %52 := .value data,
    %53 := .value (BitVec.ofNat 64 n)]

theorem outerNext_ready (E : Env program.Γ) (s : State) (data : Pointer) (n : Nat) :
    OuterStateReady (outerNextEnv E s data n) s := by
  constructor <;> simp [outerNextEnv, mlir_env]

@[simp] theorem params1 : program.blockParams 1 =
    .cons (%44) (.cons (%45) (.cons (%46) (.cons (%47) (.cons (%48)
      (.cons (%49) (.cons (%50) (.cons (%51) (.cons (%52) (.cons (%53) .nil))))))))) := rfl
@[simp] theorem params5 : program.blockParams 5 = .nil := rfl

/-- Lifetime markers have no memory effect, and the first loop starts at round zero. -/
theorem outer_start (E : Env program.Γ) (state : GlobalState) (s : State)
    (h : OuterStateReady E s) (hz : E.read (%8) = .value 0#64) :
    program.bb1.run program.blockParams E state =
      .value ((firstNextEnv E 0 s, .inr 2), state) := by
  simp [program.bb1, BasicBlock.run, Instr.run, Exit.run, Jump.run,
    firstNextEnv, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, hz,
    List.foldlM_cons, List.foldlM_nil, Regs.read_cons, Regs.read_nil,
    Env.writeMany_cons, Env.writeMany_nil, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect]

/-- Store order and native chaining-word byte order match the imported C body. -/
def feedforwardMemory (m : MemoryState) (p : Pointer) (s : State) : MemoryState :=
  let m := m.storeAt p s.a
  let m := m.storeAt (p.add 8#64) s.b
  let m := m.storeAt (p.add 16#64) s.c
  let m := m.storeAt (p.add 24#64) s.d
  let m := m.storeAt (p.add 32#64) s.e
  let m := m.storeAt (p.add 40#64) s.f
  let m := m.storeAt (p.add 48#64) s.g
  m.storeAt (p.add 56#64) s.h

def feedforwardEnv (E : Env program.Γ) (s : State) (data : Pointer) (n : Nat) : Env program.Γ :=
  E[%162 := .value s.a, %163 := .value s.b, %164 := .value s.c,
    %165 := .value s.d, %166 := .value s.e, %167 := .value s.f,
    %168 := .value s.g, %169 := .value s.h, %170 := .value (data.add 128#64),
    %171 := .value (BitVec.ofNat 64 (n - 1)),
    %172 := .value (BitVec.ofBool (BitVec.ofNat 64 (n - 1) == 0#64))]

theorem outer_decrement (n : Nat) (hn : 0 < n) (hb : n < 2^63) :
    Operation.add {nsw := true} (.value (BitVec.ofNat 64 n)) (.value 18446744073709551615#64) =
      .value (BitVec.ofNat 64 (n - 1)) := by
  have ht : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  have hi : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [ht]; omega), ht]
  have hov : (BitVec.ofNat 64 n).saddOverflow 18446744073709551615#64 = false := by
    simp only [BitVec.saddOverflow, hi]
    norm_num
    omega
  have heq : BitVec.ofNat 64 n + 18446744073709551615#64 = BitVec.ofNat 64 (n - 1) := by
    change BitVec.ofNat 64 n + (-1#64) = _
    rw [← BitVec.sub_eq_add_neg]
    exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) hn
  simp [Operation.add, hov, heq]

theorem feedforward_body (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (n : Nat) (initial final : State)
    (ho : OuterStateReady E initial) (hf : FinalReady E final)
    (hp : OuterPointersReady E chain data n)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hn : 0 < n) (hb : n < 2^63) :
    List.foldlM Instr.run E program.bb4.body state =
      .value (feedforwardEnv E (feedForward initial final) data n,
        {state with mem := feedforwardMemory state.mem chain (feedForward initial final)}) := by
  have hp0 : E.args 0 = .value chain := hp.p0
  have hf0 : Fits state.mem chain 64 := by
    have h := hc.fits_add (k := 0) (count := 8) (by decide)
    simpa using h
  let s := feedForward initial final
  have hc1 := hc.storeAt chain s.a
  have hf1 := hc1.fits_add (k := 8) (count := 8) (by decide)
  have hc2 := hc1.storeAt (chain.add 8#64) s.b
  have hf2 := hc2.fits_add (k := 16) (count := 8) (by decide)
  have hc3 := hc2.storeAt (chain.add 16#64) s.c
  have hf3 := hc3.fits_add (k := 24) (count := 8) (by decide)
  have hc4 := hc3.storeAt (chain.add 24#64) s.d
  have hf4 := hc4.fits_add (k := 32) (count := 8) (by decide)
  have hc5 := hc4.storeAt (chain.add 32#64) s.e
  have hf5 := hc5.fits_add (k := 40) (count := 8) (by decide)
  have hc6 := hc5.storeAt (chain.add 40#64) s.f
  have hf6 := hc6.fits_add (k := 48) (count := 8) (by decide)
  have hc7 := hc6.storeAt (chain.add 48#64) s.g
  have hf7 := hc7.fits_add (k := 56) (count := 8) (by decide)
  have hd' := ((((((((hd.storeAt chain s.a).storeAt (chain.add 8#64) s.b).storeAt
    (chain.add 16#64) s.c).storeAt (chain.add 24#64) s.d).storeAt
    (chain.add 32#64) s.e).storeAt (chain.add 40#64) s.f).storeAt
    (chain.add 48#64) s.g).storeAt (chain.add 56#64) s.h).gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at hd'
  dsimp only [s, feedForward] at hf1 hf2 hf3 hf4 hf5 hf6 hf7 hd'
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (b + a) := by
    simp [Operation.add, BitVec.add_comm]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    feedforwardEnv, feedforwardMemory, feedForward, hp0,
    hp.p8, hp.p16, hp.p24, hp.p32, hp.p40, hp.p48, hp.p56,
    hp.data, hp.count, hp.zero, hp.minusOne, hp.blockSize,
    ho.a, ho.b, ho.c, ho.d, ho.e, ho.f, ho.g, ho.h,
    hf.a, hf.b, hf.c, hf.d, hf.e, hf.f, hf.g, hf.h,
    hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hd', hadd, outer_decrement n hn hb,
    Operation.store, Operation.icmp, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

/-- At one remaining block, the actual branch reaches the actual return block. -/
theorem feedforward_last (E : Env program.Γ) (state : GlobalState)
    (chain data : Pointer) (initial final : State)
    (ho : OuterStateReady E initial) (hf : FinalReady E final)
    (hp : OuterPointersReady E chain data 1)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128) :
    program.bb4.run program.blockParams E state =
      .value ((feedforwardEnv E (feedForward initial final) data 1, .inr 5),
        {state with mem := feedforwardMemory state.mem chain (feedForward initial final)}) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    feedforward_body E state chain data 1 initial final ho hf hp hc hd (by decide) (by decide),
    PoisonOr.value_bind]
  simp [program.bb4, Exit.run, Jump.run, feedforwardEnv,
    Regs.read_nil, Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect]

theorem core_return (E : Env program.Γ) (state : GlobalState) :
    program.bb5.run program.blockParams E state = .value ((E, .inl .nil), state) := rfl

/-- The feedforward writes preserve the live ranges used in subsequent blocks. -/
theorem feedforwardMemory_live {m : MemoryState} {p q : Pointer} {bytes : Nat}
    (s : State) (h : SmallRange m q bytes) :
    SmallRange (feedforwardMemory m p s) q bytes := by
  exact (((((((h.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

theorem feedforwardMemory_other_block (m : MemoryState) (p : Pointer) (s : State)
    (id : BlockId) (hne : id ≠ p.id) : (feedforwardMemory m p s)[id]? = m[id]? := by
  have hn (k : BitVec 64) : (⟨id, 0⟩ : Pointer).id ≠ (p.add k).id := hne
  simp only [feedforwardMemory, MemoryState.getElem?_storeAt_ne (hn _),
    MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) hne]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
