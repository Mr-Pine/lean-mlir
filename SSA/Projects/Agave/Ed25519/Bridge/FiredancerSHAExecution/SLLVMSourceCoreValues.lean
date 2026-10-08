import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreMemory

/-! The actual SLLVM core's ambient SSA valuation and threaded branch arguments.
The argument lists are the exact result of the existing SLLVM `threadLive`
transformation, not a replacement program. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The entry block's complete, immutable ambient register valuation. -/
def ambient (kp chain stack data : Pointer) (count : Word) (initial : State) :
    Ctxt.Valuation core.cfgCtx :=
  Ctxt.Valuation.ofHVector (
    .value initial.h ::ₕ
    .value initial.g ::ₕ
    .value initial.f ::ₕ
    .value initial.e ::ₕ
    .value initial.d ::ₕ
    .value initial.c ::ₕ
    .value initial.b ::ₕ
    .value initial.a ::ₕ
    .value (chain.withOffset 56#64) ::ₕ
    .value (chain.withOffset 48#64) ::ₕ
    .value (chain.withOffset 40#64) ::ₕ
    .value (chain.withOffset 32#64) ::ₕ
    .value (chain.withOffset 24#64) ::ₕ
    .value (chain.withOffset 16#64) ::ₕ
    .value (chain.withOffset 8#64) ::ₕ
    .value stack ::ₕ
    .value 128#64 ::ₕ
    .value 80#64 ::ₕ
    .value 9#64 ::ₕ
    .value 6#64 ::ₕ
    .value 45#64 ::ₕ
    .value 7#64 ::ₕ
    .value 63#64 ::ₕ
    .value 14#64 ::ₕ
    .value 15#64 ::ₕ
    .value 1#64 ::ₕ
    .value 25#64 ::ₕ
    .value 30#64 ::ₕ
    .value 36#64 ::ₕ
    .value kp ::ₕ
    .value 18446744073709551615#64 ::ₕ
    .value 23#64 ::ₕ
    .value 46#64 ::ₕ
    .value 50#64 ::ₕ
    .value 3#64 ::ₕ
    .value 0#64 ::ₕ
    .value 56#64 ::ₕ
    .value 48#64 ::ₕ
    .value 40#64 ::ₕ
    .value 32#64 ::ₕ
    .value 24#64 ::ₕ
    .value 16#64 ::ₕ
    .value 8#64 ::ₕ
    .value 1#32 ::ₕ
    .value count ::ₕ
    .value data ::ₕ
    .value chain ::ₕ HVector.nil)

def outerTarget (initial : State) (data : Pointer) (count : Word) : SuccArgs core.cfgSigs :=
  ⟨0, rfl, [.value initial.h, .value initial.g, .value initial.f, .value initial.e,
    .value initial.d, .value initial.c, .value initial.b, .value initial.a,
    .value data, .value count]ₕ⟩

def firstTarget (initial work : State) (data : Pointer) (count : Word) (i : Nat) :
    SuccArgs core.cfgSigs :=
  ⟨1, rfl, [.value work.a, .value work.b, .value work.c, .value work.d,
    .value work.e, .value work.f, .value (BitVec.ofNat 64 i), .value work.h, .value work.g,
    .value initial.h, .value initial.g, .value initial.f, .value initial.e,
    .value initial.d, .value initial.c, .value initial.b, .value initial.a,
    .value data, .value count]ₕ⟩

def laterTarget (initial work : State) (data : Pointer) (count : Word) (i : Nat) :
    SuccArgs core.cfgSigs :=
  ⟨2, rfl, [.value work.a, .value work.b, .value work.c, .value work.d,
    .value work.e, .value work.f, .value (BitVec.ofNat 64 i), .value work.h, .value work.g,
    .value initial.h, .value initial.g, .value initial.f, .value initial.e,
    .value initial.d, .value initial.c, .value initial.b, .value initial.a,
    .value data, .value count]ₕ⟩

/-- `work` is the result of round 79; the threaded operands retain precisely
its shifted old words and its two newly computed words. -/
def feedforwardTarget (initial work : State) (data : Pointer) (count : Word) :
    SuccArgs core.cfgSigs :=
  ⟨3, rfl, [.value initial.h, .value initial.g, .value initial.f, .value initial.e,
    .value initial.d, .value initial.c, .value initial.b, .value initial.a,
    .value data, .value count, .value work.b, .value work.c, .value work.d,
    .value work.f, .value work.g, .value work.h, .value work.e, .value work.a]ₕ⟩

def doneTarget : SuccArgs core.cfgSigs := ⟨4, rfl, .nil⟩

def blockInput (target : SuccArgs core.cfgSigs) (V : Ctxt.Valuation core.cfgCtx) :
    Ctxt.Valuation (Ctxt.ofList target.ts.reverse ++ core.cfgCtx) :=
  Ctxt.Valuation.ofHVector target.args.reverse ++ V

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
