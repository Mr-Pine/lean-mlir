import SSA.Projects.Agave.Ed25519.Proof.Verifier.BcmpBoundary

/-!
# Ordinary bytewise ABI adapter for the external comparison

This file proves the conversion from the ordinary bytewise specification of
`bcmp` to the imported verifier's actual comparison and cleanup. It does not
define, replace, or prove an implementation of the external symbol. Every
external execution premise is an explicit theorem parameter.

The input condition needs just 32 readable bytes and nonwrapping addresses for
those bytes. In particular, it needs neither disjointness nor alignment nor the
small-allocation invariant needed elsewhere for flags-7 GEP instructions.
The optional caller frame preserves only blocks that existed before the call;
acceptance needs no frame at all.
-/

namespace Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- All 32 observed byte addresses are valid; only the last byte address must
be representable. No condition is imposed on a one-past pointer. -/
structure Input32 (m : MemoryState) (p : Pointer) : Prop where
  fits : Fits m p 256
  lastByte : ¬p.offset.uaddOverflow 31#64

theorem input32_of_smallRange {m : MemoryState} {p : Pointer}
    (h : SmallRange m p 32) : Input32 m p :=
  ⟨h.fits, h.no_wrap (k := 31) (by decide)⟩

/-- The portable semantic part of `bcmp(..., 32)`: equality of individual
bytes, including zero bytes and all high-bit values. -/
def Equal32 (m : MemoryState) (left right : Pointer) : Prop :=
  ∀ i : Fin 32, m.readAt (left.add (BitVec.ofNat 64 i.val)) 8 =
    m.readAt (right.add (BitVec.ofNat 64 i.val)) 8

theorem read_byte (m : MemoryState) (p : Pointer) (h : Input32 m p)
    (i : Fin 32) :
    m.readAt (p.add (BitVec.ofNat 64 i.val)) 8 =
      (m.readAt p 256).extractLsb' (i.val * 8) 8 := by
  have hi : i.val < 18446744073709551616 := by omega
  have hoff : ¬p.offset.uaddOverflow (BitVec.ofNat 64 i.val) := by
    have hlast := h.lastByte
    simp only [BitVec.uaddOverflow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] at *
    norm_num at hlast ⊢
    omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] using
    (MemoryState.readAt_add_of_readAt (w := 8) h.fits hoff
      (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]; omega) rfl)

/-- The bytewise ABI predicate and RIR's bulk read are exactly equivalent,
under the input-address conditions. -/
theorem equal32_iff_readAt (m : MemoryState) (left right : Pointer)
    (hl : Input32 m left) (hr : Input32 m right) :
    Equal32 m left right ↔ m.readAt left 256 = m.readAt right 256 := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hbyte := h ⟨k / 8, by omega⟩
    rw [read_byte m left hl, read_byte m right hr] at hbyte
    have hbit := congrArg (fun x : BitVec 8 => x.getLsbD (k % 8)) hbyte
    have hmod : k % 8 < 8 := Nat.mod_lt _ (by decide)
    have hindex : k / 8 * 8 + k % 8 = k := by omega
    simpa [BitVec.getLsbD_extractLsb', hmod, hindex] using hbit
  · intro h i
    rw [read_byte m left hl i, read_byte m right hr i, h]

/-- Termination with a defined i32 result and its zero/nonzero meaning for
one exact call. No property of unrelated calls or lengths is required. -/
def Invocation (call : Bcmp.Call) (left right : Pointer) (state : GlobalState) : Prop :=
  ∃ (after : GlobalState) (result : BitVec 32),
    call (Bcmp.args left right) state = .value (.cons (.value result) .nil, after) ∧
    (result = 0 ↔ Equal32 state.mem left right)

/-- This is an equivalence, not an additional semantic assumption: the
adapter neither loses nor strengthens the observed result condition. -/
theorem invocation_iff (call : Bcmp.Call) (left right : Pointer) (state : GlobalState)
    (hl : Input32 state.mem left) (hr : Input32 state.mem right) :
    Invocation call left right state ↔ Bcmp.Invocation call left right state := by
  simp only [Invocation, Bcmp.Invocation, equal32_iff_readAt state.mem left right hl hr]

/-- The smallest block-level caller frame used here. Fresh/private blocks and
the allocation counter are unrestricted, and final state well-formedness is
not required for the cleanup, which performs no loads or allocations. -/
def CallerFrame (before after : GlobalState) : Prop :=
  ∀ (id : BlockId) (block : MemoryBlock), before.mem[id]? = some block →
    after.mem[id]? = some block

theorem CallerFrame.readAt {before after : GlobalState} (h : CallerFrame before after)
    (p : Pointer) (width : Nat) (block : MemoryBlock)
    (hp : before.mem[p.id]? = some block) :
    after.mem.readAt p width = before.mem.readAt p width := by
  simp only [MemoryState.readAt, hp, h p.id block hp]

theorem CallerFrame.smallRange {before after : GlobalState} (h : CallerFrame before after)
    (p : Pointer) (bytes : Nat) (hp : SmallRange before.mem p bytes) :
    SmallRange after.mem p bytes := by
  obtain ⟨block, hb, hsmall, hsize⟩ := hp
  exact ⟨block, h p.id block hb, hsmall, hsize⟩

theorem CallerFrame.readBytes {before after : GlobalState} (h : CallerFrame before after)
    (p : Pointer) (bytes : Nat) (value : BitVec (8 * bytes))
    (hp : ReadBytes before p bytes value) : ReadBytes after p bytes value := by
  refine ⟨h.smallRange p bytes hp.1, ?_⟩
  obtain ⟨block, hb, _, _⟩ := hp.1
  exact (h.readAt p (8 * bytes) block hb).trans hp.2

/-- Optional ordinary no-write/no-free guarantee for blocks owned by the
caller. This deliberately avoids the stronger all-address `ReadOnlyFrame`. -/
def FramedInvocation (call : Bcmp.Call) (left right : Pointer) (state : GlobalState) : Prop :=
  ∃ (after : GlobalState) (result : BitVec 32),
    call (Bcmp.args left right) state = .value (.cons (.value result) .nil, after) ∧
    CallerFrame state after ∧ (result = 0 ↔ Equal32 state.mem left right)

theorem FramedInvocation.toInvocation {call : Bcmp.Call} {left right : Pointer}
    {state : GlobalState} (h : FramedInvocation call left right state) :
    Invocation call left right state := by
  obtain ⟨after, result, hcall, _, heq⟩ := h
  exact ⟨after, result, hcall, heq⟩

/-- Compatibility adapter for callers that still require the existing
universal `CompareContract`. The only semantic premise is bytewise equality;
the old contract's stronger frame is supplied separately and explicitly. -/
theorem compareContract_of_bytewise (call : Bcmp.Call)
    (h : ∀ (left right : Pointer) (state : GlobalState), state.WF →
      SmallRange state.mem left 32 → SmallRange state.mem right 32 →
      ∃ (after : GlobalState) (result : BitVec 32),
        call (Bcmp.args left right) state = .value (.cons (.value result) .nil, after) ∧
        ReadOnlyFrame state after ∧ (result = 0 ↔ Equal32 state.mem left right)) :
    CompareContract call := by
  intro left right state a b hwf ha hb
  obtain ⟨after, result, hcall, hframe, heq⟩ := h left right state hwf ha.1 hb.1
  refine ⟨after, result, hcall, hframe, ?_⟩
  rw [equal32_iff_readAt state.mem left right
    (input32_of_smallRange ha.1) (input32_of_smallRange hb.1), ha.2, hb.2] at heq
  exact heq

/-- Execute the actual imported call, select, and both cleanup blocks from
the bytewise ABI premise. Arbitrary nonzero return codes all reject. -/
theorem compression_tail (p : Primitives) (g : Globals)
    (E : Env program.Γ) (state compared : GlobalState)
    (out point signature : Pointer) (a r : Bytes32)
    (hout : E.read (%26) = .value out) (hpoint : E.read (%25) = .value point)
    (hsig : E.read (%arg1) = .value signature)
    (hlen : E.read (%1) = .value 32#64)
    (hzero : E.read (%19) = .value 0#32)
    (hok : E.read (%13) = .value 255#8)
    (herr : E.read (%8) = .value 2#8)
    (hc : p.compressPoint (args2 out point) state = .value (.nil, compared))
    (ha : compared.mem.readAt out 256 = a)
    (hr : compared.mem.readAt signature 256 = r)
    (hleft : Input32 compared.mem out) (hright : Input32 compared.mem signature)
    (hb : Invocation p.compareBytes out signature compared) :
    ∃ after, (program p g).runFrom E 10 state =
      .value (.cons (.value (code (decide (a = r)))) .nil, after) :=
  Bcmp.compression_tail_of_invocation p g E state compared out point signature a r
    hout hpoint hsig hlen hzero hok herr hc ha hr
    ((invocation_iff _ _ _ _ hleft hright).mp hb)

/-- The same real cleanup preserves the weaker ordinary caller frame. No
final `WF`, global memory identity, allocation-counter identity, or properties
of fresh block addresses are hidden in the premises. -/
theorem compression_tail_framed (p : Primitives) (g : Globals)
    (E : Env program.Γ) (state compared : GlobalState)
    (out point signature : Pointer) (a r : Bytes32)
    (hout : E.read (%26) = .value out) (hpoint : E.read (%25) = .value point)
    (hsig : E.read (%arg1) = .value signature)
    (hlen : E.read (%1) = .value 32#64)
    (hzero : E.read (%19) = .value 0#32)
    (hok : E.read (%13) = .value 255#8)
    (herr : E.read (%8) = .value 2#8)
    (hc : p.compressPoint (args2 out point) state = .value (.nil, compared))
    (ha : compared.mem.readAt out 256 = a)
    (hr : compared.mem.readAt signature 256 = r)
    (hleft : Input32 compared.mem out) (hright : Input32 compared.mem signature)
    (hb : FramedInvocation p.compareBytes out signature compared) :
    ∃ after, (program p g).runFrom E 10 state =
      .value (.cons (.value (code (decide (a = r)))) .nil, after) ∧
      CallerFrame compared after := by
  obtain ⟨after, result, hcall, hframe, heq⟩ := hb
  have heq' : result = 0#32 ↔ a = r := by
    rw [equal32_iff_readAt compared.mem out signature hleft hright, ha, hr] at heq
    exact heq
  refine ⟨after, ?_, hframe⟩
  rw [Dalek.compression_tail p g E state compared after out point signature result
    hout hpoint hsig hlen hzero hok herr hc hcall]
  simp only [heq']

end Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.ByteABI
