import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionReturn
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionFeedForwardMemory

/-! The bulk loop's eight original final stores and closed return. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

structure BulkChainPointers (E : Env program.Γ) (chain : Pointer) : Prop where
  ptr : E.read (%arg0) = .value chain
  p1 : E.read (%335) = .value (chain.add 8#64)
  p2 : E.read (%336) = .value (chain.add 16#64)
  p3 : E.read (%337) = .value (chain.add 24#64)
  p4 : E.read (%338) = .value (chain.add 32#64)
  p5 : E.read (%339) = .value (chain.add 40#64)
  p6 : E.read (%340) = .value (chain.add 48#64)
  p7 : E.read (%341) = .value (chain.add 56#64)

structure BulkStoreReady (E : Env program.Γ) (chain : Pointer) (s : Spec.State) : Prop where
  ptr : E.read (%arg0) = .value chain
  p1 : E.read (%335) = .value (chain.add 8#64)
  p2 : E.read (%336) = .value (chain.add 16#64)
  p3 : E.read (%337) = .value (chain.add 24#64)
  p4 : E.read (%338) = .value (chain.add 32#64)
  p5 : E.read (%339) = .value (chain.add 40#64)
  p6 : E.read (%340) = .value (chain.add 48#64)
  p7 : E.read (%341) = .value (chain.add 56#64)
  a : E.read (%654) = .value s.a
  b : E.read (%655) = .value s.b
  c : E.read (%656) = .value s.c
  d : E.read (%657) = .value s.d
  e : E.read (%658) = .value s.e
  f : E.read (%659) = .value s.f
  g : E.read (%660) = .value s.g
  h : E.read (%661) = .value s.h

def bulkStoreMem (mem : MemoryState) (chain : Pointer) (s : Spec.State) : MemoryState :=
  let m1 := mem.storeAt chain s.a
  let m2 := m1.storeAt (chain.add 8#64) s.b
  let m3 := m2.storeAt (chain.add 16#64) s.c
  let m4 := m3.storeAt (chain.add 24#64) s.d
  let m5 := m4.storeAt (chain.add 32#64) s.e
  let m6 := m5.storeAt (chain.add 40#64) s.f
  let m7 := m6.storeAt (chain.add 48#64) s.g
  let m8 := m7.storeAt (chain.add 56#64) s.h
  m8

private theorem bulk_splice_adjacent {n low high : Nat} (bytes : BitVec n) (off : Nat)
    (lo : BitVec low) (hi : BitVec high) :
    Memory.spliceBits (Memory.spliceBits bytes off lo) (off + low) hi =
      Memory.spliceBits bytes off (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [Memory.getLsbD_spliceBits, BitVec.getLsbD_append]
  grind

private theorem bulk_pack_reassoc (s : Spec.State) :
    s.h ++ (s.g ++ (s.f ++ (s.e ++ (s.d ++ (s.c ++ (s.b ++ s.a)))))) = Spec.pack s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Spec.pack, BitVec.getLsbD_append]
  grind

theorem bulkStoreMem_eq (mem : MemoryState) (chain : Pointer)
    (hc : SmallRange mem chain 64) (s : Spec.State) :
    bulkStoreMem mem chain s = mem.storeAt chain (Spec.pack s) := by
  have h8 : (chain.add 8#64).offsetInBits = chain.offsetInBits + 64 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 8) (by decide))
  have h16 : (chain.add 16#64).offsetInBits = chain.offsetInBits + 128 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 16) (by decide))
  have h24 : (chain.add 24#64).offsetInBits = chain.offsetInBits + 192 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 24) (by decide))
  have h32 : (chain.add 32#64).offsetInBits = chain.offsetInBits + 256 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 32) (by decide))
  have h40 : (chain.add 40#64).offsetInBits = chain.offsetInBits + 320 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 40) (by decide))
  have h48 : (chain.add 48#64).offsetInBits = chain.offsetInBits + 384 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 48) (by decide))
  have h56 : (chain.add 56#64).offsetInBits = chain.offsetInBits + 448 := by
    simpa using Pointer.offsetInBits_add (hc.no_wrap (k := 56) (by decide))
  obtain ⟨block, hb, _, _⟩ := hc
  unfold bulkStoreMem MemoryState.storeAt
  simp only [Pointer.add_id, hb, h8, h16, h24, h32, h40, h48, h56]
  simp only [MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert_self]
  simp only [bulk_splice_adjacent, bulk_pack_reassoc, MemoryState.mk.injEq]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  by_cases hk : chain.id = k <;> simp [Std.ExtHashMap.getElem?_insert, hk]

theorem bulk_store_body (E : Env program.Γ) (mem : GlobalState) (chain : Pointer)
    (s : Spec.State) (h : BulkStoreReady E chain s) (hc : SmallRange mem.mem chain 64) :
    List.foldlM Instr.run E program.bb17.body mem =
      .value (E, {mem with mem := mem.mem.storeAt chain (Spec.pack s)}) := by
  have hp : E.args 0 = .value chain := h.ptr
  have hf0 : Fits mem.mem (chain.add 0#64) 64 :=
    hc.fits_add (k := 0) (count := 8) (by decide)
  have hf1 : Fits mem.mem (chain.add 8#64) 64 :=
    hc.fits_add (k := 8) (count := 8) (by decide)
  have hf2 : Fits mem.mem (chain.add 16#64) 64 :=
    hc.fits_add (k := 16) (count := 8) (by decide)
  have hf3 : Fits mem.mem (chain.add 24#64) 64 :=
    hc.fits_add (k := 24) (count := 8) (by decide)
  have hf4 : Fits mem.mem (chain.add 32#64) 64 :=
    hc.fits_add (k := 32) (count := 8) (by decide)
  have hf5 : Fits mem.mem (chain.add 40#64) 64 :=
    hc.fits_add (k := 40) (count := 8) (by decide)
  have hf6 : Fits mem.mem (chain.add 48#64) 64 :=
    hc.fits_add (k := 48) (count := 8) (by decide)
  have hf7 : Fits mem.mem (chain.add 56#64) 64 :=
    hc.fits_add (k := 56) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hf0
  rw [← bulkStoreMem_eq mem.mem chain hc s]
  simp [program.bb17, List.foldlM_cons, List.foldlM_nil, Instr.run, bulkStoreMem,
    hp, h.p1, h.p2, h.p3, h.p4, h.p5, h.p6, h.p7,
    h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h,
    hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, Fits.storeAt_iff,
    Operation.store, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem bulk_store_block (E : Env program.Γ) (mem : GlobalState) (chain : Pointer)
    (s : Spec.State) (h : BulkStoreReady E chain s) (hc : SmallRange mem.mem chain 64) :
    program.bb17.run program.blockParams E mem =
      .value ((E, .inr 18), {mem with mem := mem.mem.storeAt chain (Spec.pack s)}) := by
  simp only [BasicBlock.run, EffectM.bind_eq, bulk_store_body E mem chain s h hc,
    PoisonOr.value_bind]
  simp [program.bb17, Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_store_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain : Pointer) (s : Spec.State) (h : BulkStoreReady E chain s)
    (hc : SmallRange mem.mem chain 64) :
    (program g).runFrom E 17 mem =
      .value (.nil, {mem with mem := mem.mem.storeAt chain (Spec.pack s)}) := by
  rw [Func.runFrom_eq]
  change (program.bb17.run program.blockParams E mem >>= _) = _
  rw [bulk_store_block E mem chain s h hc]
  exact return_end_runFrom g _ _

theorem bulk_store_evalFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain : Pointer) (s : Spec.State) (h : BulkStoreReady E chain s)
    (hc : SmallRange mem.mem chain 64) :
    (program g).evalFrom 2 E 17 mem =
      .value (some .nil, {mem with mem := mem.mem.storeAt chain (Spec.pack s)}) := by
  rw [Func.evalFrom]
  change (program.bb17.run program.blockParams E mem >>= _) = _
  rw [bulk_store_block E mem chain s h hc]
  simp only [PoisonOr.value_bind]
  rw [Func.evalFrom]
  simp only [EffectM.bind_eq]
  change (program.bb18.run program.blockParams E _ >>= _) = _
  rw [return_end_block]
  rfl

end Agave.Ed25519.SHA512.Execution.Avx2
