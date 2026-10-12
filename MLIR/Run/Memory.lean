module

public import MLIR.Semantics.Instruction

namespace MLIR

public section

/-- A store of a value without poison leaves, of a type without padding: its bits, defined. -/
theorem run_store {ptr : Pointer} {t : Ty} {v} {b : BitVec t.width} (hroom : Room s.mem ptr t.width)
    (hv : t.flatten v = .value b) (hpad : t.hasPadding = false) :
    (Operation.store (.value ptr) v) env s =
      .value (env, { s with mem := s.mem.storeAt ptr b }) := by
  have hp := Ty.hasPtr_of_flatten hv
  simp [Operation.store, hroom, Ty.ptrLeaves_of_hasPtr hp, throwUBIf,
    Ty.flattenDef_of_flatten hv hpad, mlir_effect, MemoryState.storeAt_eq_storeDef]

/-- A store of any value without pointers: its bits, defined but in poison leaves and padding. -/
theorem run_storeDef {ptr : Pointer} {t : Ty} {v : ⟦t⟧} (hroom : Room s.mem ptr t.width)
    (hp : t.hasPtr = false) :
    (Operation.store (.value ptr) v) env s =
      .value (env, { s with mem := s.mem.storeDef ptr (t.flattenDef v).1 (t.flattenDef v).2 }) := by
  simp [Operation.store, hroom, Ty.ptrLeaves_of_hasPtr hp, throwUBIf, mlir_effect]

/-- A store of any value: its bits, defined but in poison leaves, padding and pointers, and its
pointers recorded. -/
theorem run_storeValue {ptr : Pointer} {t : Ty} {v : ⟦t⟧} (hroom : Room s.mem ptr t.width) :
    (Operation.store (.value ptr) v) env s =
      .value
        (env,
          { s with
            mem :=
              (s.mem.storeDef ptr (t.flattenDef v).1 (t.flattenDef v).2).recordPtrs ptr
                (t.ptrLeaves 0 v) }) := by
  simp [Operation.store, hroom, throwUBIf, mlir_effect]

/-- A store of a pointer: its bits undefined, the pointer recorded. -/
theorem run_storePtr {ptr q : Pointer} (hroom : Room s.mem ptr 64) :
    (Operation.store (τ := .ptr) (.value ptr) (.value q)) env s =
      .value (env, { s with mem := s.mem.storePtr ptr q }) := by
  rw [run_storeValue hroom, MemoryState.storePtr_eq]
  rfl

/-- A store of a poison pointer: its bits undefined, nothing recorded. -/
theorem run_storePtr_poison {ptr : Pointer} (hroom : Room s.mem ptr 64) :
    (Operation.store (τ := .ptr) (.value ptr) .poison) env s =
      .value (env, { s with mem := s.mem.storeDef ptr 0#64 0#64 }) := by
  rw [run_storeValue hroom]
  rfl

/-- `memcpy` of `n` known bytes: a store at `dst` of the bits read at `src`. -/
theorem run_memcpy {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hd : (Range.of dst (8 * n)).Disjoint (Range.of src (8 * n))) (hfd : Room s.mem dst (8 * n))
    (hfs : Fits s.mem src (8 * n)) :
    (Operation.memcpy (.value dst) (.value src) (.value len)) env s =
      .value (env, { s with mem := s.mem.storeAt dst (s.mem.readAt src (8 * n)) }) := by
  subst hn
  simp [Operation.memcpy, hd, hfd, hfs.room, throwUBIf, mlir_effect,
    MemoryState.definedAt_of_fits hfs, MemoryState.storeAt_eq_storeDef]

/-- `memcpy` of `n` bytes: their bits and which are defined. -/
theorem run_memcpyDef {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hd : (Range.of dst (8 * n)).Disjoint (Range.of src (8 * n))) (hfd : Room s.mem dst (8 * n))
    (hfs : Room s.mem src (8 * n)) :
    (Operation.memcpy (.value dst) (.value src) (.value len)) env s =
      .value
        (env,
          { s with
            mem :=
              s.mem.storeDef dst (s.mem.readAt src (8 * n)) (s.mem.definedAt src (8 * n)) }) := by
  subst hn
  simp [Operation.memcpy, hd, hfd, hfs, throwUBIf, mlir_effect]

/-- `memmove` of `n` known bytes: a store at `dst` of the bits read at `src`, which may overlap. -/
theorem run_memmove {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hfd : Room s.mem dst (8 * n)) (hfs : Fits s.mem src (8 * n)) :
    (Operation.memmove (.value dst) (.value src) (.value len)) env s =
      .value (env, { s with mem := s.mem.storeAt dst (s.mem.readAt src (8 * n)) }) := by
  subst hn
  simp [Operation.memmove, hfd, hfs.room, throwUBIf, mlir_effect,
    MemoryState.definedAt_of_fits hfs, MemoryState.storeAt_eq_storeDef]

/-- `memmove` of `n` bytes: their bits and which are defined. -/
theorem run_memmoveDef {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hfd : Room s.mem dst (8 * n)) (hfs : Room s.mem src (8 * n)) :
    (Operation.memmove (.value dst) (.value src) (.value len)) env s =
      .value
        (env,
          { s with
            mem :=
              s.mem.storeDef dst (s.mem.readAt src (8 * n)) (s.mem.definedAt src (8 * n)) }) := by
  subst hn
  simp [Operation.memmove, hfd, hfs, throwUBIf, mlir_effect]

/-- `ptrtoaddr`: the value of the state's addresses, the state unchanged. -/
theorem run_ptrtoaddr {dst : Dst Γ (.bv w)} {p : Reg Γ .ptr} :
    Instr.run env (.ptrtoaddr dst p) s =
      .value (env.write dst (Operation.ptrtoaddr s.mem.addr (env.read p)), s) :=
  rfl

/-- `memset` of `n` bytes: a store at `src` of the repeated byte. -/
theorem run_memset {dst : Pointer} {val : BitVec 8} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hfd : Room s.mem dst (8 * n)) :
    (Operation.memset (.value dst) (.value val) (.value len)) env s =
      .value (env, { s with mem := s.mem.storeAt dst (val.replicate n) }) := by
  subst hn
  simp [Operation.memset, hfd, throwUBIf, mlir_effect]

/-- A load of known bits, of a type without pointers: their value. -/
theorem run_load {ptr : Pointer} {t : Ty} {v} {dst : Dst Γ t} (hfits : Fits s.mem ptr t.width)
    (hv : (t.unflatten (s.mem.readAt ptr t.width)) = v) (hp : t.hasPtr = false := by simp) :
    (Operation.load dst (.value ptr)) env s = .value (env[dst := v], s) := by
  simp [Operation.load, hfits.inBounds, throwUBIf, ← hv, mlir_effect,
    MemoryState.definedAt_of_fits hfits, Ty.unflattenDef_allOnes, Ty.setPtrs_of_hasPtr hp]

/-- A load of any bits in bounds, of a type without pointers: poison leaves where they are
undefined. -/
theorem run_loadDef {ptr : Pointer} {t : Ty} {dst : Dst Γ t} (h : InBounds s.mem ptr t.width)
    (hp : t.hasPtr = false := by simp) :
    (Operation.load dst (.value ptr)) env s =
      .value
        (env[dst := t.unflattenDef (s.mem.readAt ptr t.width) (s.mem.definedAt ptr t.width)],
          s) := by
  simp [Operation.load, h, throwUBIf, mlir_effect, Ty.setPtrs_of_hasPtr hp]

/-- A load of any value in bounds: poison leaves where they are undefined, pointer leaves the
pointers stored there. -/
theorem run_loadValue {ptr : Pointer} {t : Ty} {dst : Dst Γ t} (h : InBounds s.mem ptr t.width) :
    (Operation.load dst (.value ptr)) env s =
      .value
        (env[dst :=
            t.setPtrs 0 (fun o => s.mem.ptrAt ptr.id (ptr.offsetInBits + o))
              (t.unflattenDef (s.mem.readAt ptr t.width) (s.mem.definedAt ptr t.width))],
          s) := by
  simp [Operation.load, h, throwUBIf, mlir_effect]

/-- A load of a pointer: the pointer stored there. -/
theorem run_loadPtr {ptr : Pointer} {dst : Dst Γ .ptr} (h : InBounds s.mem ptr 64) :
    (Operation.load dst (.value ptr)) env s = .value (env[dst := s.mem.loadPtr ptr], s) := by
  rw [run_loadValue h]
  rfl

theorem run_alloca {Γ : Ctx} {env : ⟪Γ⟫} {dst : Dst Γ .ptr} {s : GlobalState} {bytes : Nat}
    {dead : Bool} :
    (modifyGetThe GlobalState fun s => (env.write dst (.value s.allocaPtr), s.alloca bytes dead) :
          EffectM ⟪Γ⟫)
        s =
      .value (env.write dst (.value s.allocaPtr), s.alloca bytes dead) :=
  rfl

/-- `lifetime.start` of a pointer: its object live, its bits undefined. -/
theorem run_lifetimeStart {p : Pointer} :
    (Operation.lifetimeStart (.value p)) env s =
      .value (env, { s with mem := s.mem.lifetimeStart p }) :=
  rfl

/-- `lifetime.end` of a pointer: its object dead. -/
theorem run_lifetimeEnd {p : Pointer} :
    (Operation.lifetimeEnd (.value p)) env s =
      .value (env, { s with mem := s.mem.lifetimeEnd p }) :=
  rfl

/-- `lifetime.start` of poison: nothing. -/
theorem run_lifetimeStart_poison : (Operation.lifetimeStart .poison) env s = .value (env, s) :=
  rfl

/-- `lifetime.end` of poison: nothing. -/
theorem run_lifetimeEnd_poison : (Operation.lifetimeEnd .poison) env s = .value (env, s) :=
  rfl

/-- `assume` of `1`: nothing. -/
theorem run_assume : (Operation.assume (.value 1#1)) env s = .value (env, s) :=
  rfl

theorem run_addressof {Γ : Ctx} {env : ⟪Γ⟫} {s : GlobalState} {t : Ty} {v : EffectM ⟦t⟧} {x : ⟦t⟧}
    {b : BitVec t.width} {dst : Dst Γ .ptr} (hv : v s = .value (x, s)) (hb : t.flatten x = .value b)
    (hpad : t.hasPadding = false) :
    Instr.run env (.addressof v dst) s =
      .value
        (env.write dst (.value s.allocaPtr),
          let s' := s.alloca ((t.width + 7) / 8)
          { s' with mem := s'.mem.storeAt s.allocaPtr b }) := by
  have hp := Ty.hasPtr_of_flatten hb
  simp only [Instr.run, EffectM.bind_eq, hv, PoisonOr.value_bind, Ty.flattenDef_of_flatten hb hpad,
    Ty.ptrLeaves_of_hasPtr hp, MemoryState.recordPtrs_nil, MemoryState.storeAt_eq_storeDef]
  rfl

/-- `run_addressof` of a global whose initializer gives `wrap r`: a fresh block of `n` bytes holding
`r`'s bits, at their literal width `w`. -/
theorem run_addressof_wrap {Γ : Ctx} {env : ⟪Γ⟫} {s : GlobalState} {t : Ty} {v : EffectM ⟦t⟧}
    {r : ⟦t⟧ᵣ} {dst : Dst Γ .ptr} {w n : Nat} (hv : v s = .value (Ty.wrap r, s))
    (hp : t.hasPtr = false) (hpad : t.hasPadding = false) (hw : t.width = w)
    (hn : (w + 7) / 8 = n) :
    Instr.run env (.addressof v dst) s =
      .value
        (env.write dst (.value s.allocaPtr),
          { alloc := ⟨s.alloc.nextFreeBlock + 1⟩,
            mem := s.mem.addBlock ⟨s.alloc.nextFreeBlock⟩ n (Ty.flatBits r (hw := hw)) }) := by
  rw [← GlobalState.alloca_storeAt_allocaPtr, Ty.flatBits_eq]
  subst hw hn
  exact run_addressof hv (Ty.flatten_wrap hp) hpad

/-- `run_addressof` of a global with undefined members (`x`'s bits `b`, defined where `d` is set,
at their literal width `w`), no pointer stored: a fresh block of `n` bytes holding them, masked. -/
theorem run_addressof_def {Γ : Ctx} {env : ⟪Γ⟫} {s : GlobalState} {t : Ty} {v : EffectM ⟦t⟧}
    {x : ⟦t⟧} {dst : Dst Γ .ptr} {w n : Nat} {b d : BitVec w} (hv : v s = .value (x, s))
    (hl : t.ptrLeaves 0 x = []) (hw : t.width = w)
    (hx : t.flattenDef x = (b.cast hw.symm, d.cast hw.symm))
    (hn : (w + 7) / 8 = n) :
    Instr.run env (.addressof v dst) s =
      .value
        (env.write dst (.value s.allocaPtr),
          let s' := s.alloca n
          { s' with mem := s'.mem.storeDef s.allocaPtr b d }) := by
  subst hn hw
  simp only [Instr.run, EffectM.bind_eq, hv, PoisonOr.value_bind, hx, BitVec.cast_eq, hl,
    MemoryState.recordPtrs_nil]
  rfl

@[mlir_operation]
theorem gep_value {ptr} (h : ¬ptr.offset.uaddOverflow off) :
    Operation.gep (.value off) (.value ptr) = .value (ptr.add off) := by simp [Operation.gep, h]

/-- `gepBack` by at most the pointer's offset. -/
@[mlir_operation]
theorem gepBack_value {ptr} (h : n ≤ ptr.offset.toNat) :
    Operation.gepBack n (.value ptr) = .value (ptr.add (-BitVec.ofNat 64 n)) := by
  simp [Operation.gepBack, Nat.not_lt.mpr h]

/-- `gepInt` to an offset in `[0, 2 ^ 64)`. -/
@[mlir_operation]
theorem gepInt_value {ptr : Pointer} {off : Int} (h₀ : 0 ≤ (ptr.offset.toNat : Int) + off)
    (h₁ : (ptr.offset.toNat : Int) + off < 2 ^ 64) :
    Operation.gepInt off (.value ptr) = .value (ptr.add (BitVec.ofInt 64 off)) := by
  have h : 0 ≤ (ptr.offset.toNat : Int) + off ∧ (ptr.offset.toNat : Int) + off < 2 ^ 64 := ⟨h₀, h₁⟩
  simp only [Operation.gepInt, PoisonOr.value_bind, h, and_self, ↓reduceIte]

@[mlir_operation]
theorem gepInt_poison : Operation.gepInt off .poison = .poison :=
  rfl

/-- `gep` by an offset that wraps: poison. -/
@[mlir_operation]
theorem gep_overflow {ptr} (h : ptr.offset.uaddOverflow off) :
    Operation.gep (.value off) (.value ptr) = .poison := by simp [Operation.gep, h]

@[mlir_operation]
theorem gepDyn_poison : Operation.gepDyn byteOff stride ptr .poison = .poison :=
  rfl

/-- `gepDyn` by a value index: the unsigned reading, else the signed one. -/
theorem gepDyn_value_idx {i : BitVec 64} :
    Operation.gepDyn byteOff stride ptr (.value i) =
      if byteOff + i.toNat * stride < 2 ^ 64 then
        (Operation.gep (.value (BitVec.ofNat 64 (byteOff + i.toNat * stride))) ptr).orElse
          (Operation.gepInt (byteOff + i.toInt * stride) ptr)
      else Operation.gepInt (byteOff + i.toInt * stride) ptr :=
  rfl

/-- `gepDyn`'s unsigned reading by the index itself. -/
theorem gepDynUnsigned_zero_one {ptr} {i : BitVec 64} :
    Operation.gepDynUnsigned 0 1 ptr (.value i) = Operation.gep (.value i) ptr := by
  simp [Operation.gepDynUnsigned, i.isLt]

/-- `gepDyn` whose unsigned reading is a value: that value. -/
theorem gepDyn_of_unsigned {idx : PoisonOr (BitVec 64)} {q : Pointer}
    (h : Operation.gepDynUnsigned byteOff stride ptr idx = .value q) :
    Operation.gepDyn byteOff stride ptr idx = .value q := by
  cases idx using PoisonOr.casesOn' with
  | poison => exact absurd h (PoisonOr.poison_ne_value q)
  | value i =>
    rw [gepDyn_value_idx]
    simp only [Operation.gepDynUnsigned, PoisonOr.value_bind] at h
    split
    · rename_i hc
      simp only [hc, ↓reduceIte] at h
      rw [h, PoisonOr.value_orElse]
    · rename_i hc
      simp only [hc, ↓reduceIte] at h
      exact absurd h (PoisonOr.poison_ne_value q)

/-- `gepDyn` whose unsigned reading is a value: that reading. -/
theorem gepDyn_eq_unsigned {idx : PoisonOr (BitVec 64)} {q : Pointer}
    (h : Operation.gepDynUnsigned byteOff stride ptr idx = .value q) :
    Operation.gepDyn byteOff stride ptr idx = Operation.gepDynUnsigned byteOff stride ptr idx :=
  (gepDyn_of_unsigned h).trans h.symm

/-- `gepDyn` whose unsigned reading is poison: the signed one. -/
theorem gepDyn_of_unsigned_poison {i : BitVec 64}
    (h : Operation.gepDynUnsigned byteOff stride ptr (.value i) = .poison) :
    Operation.gepDyn byteOff stride ptr (.value i) =
      Operation.gepInt (byteOff + i.toInt * stride) ptr := by
  rw [gepDyn_value_idx]
  simp only [Operation.gepDynUnsigned, PoisonOr.value_bind] at h
  split
  · rename_i hc
    simp only [hc, ↓reduceIte] at h
    rw [h, PoisonOr.poison_orElse]
  · rfl

/-- `gepInt` leaving `[0, 2 ^ 64)`. -/
theorem gepInt_of_not {p : Pointer} {off : Int}
    (h : ¬(0 ≤ (p.offset.toNat : Int) + off ∧ (p.offset.toNat : Int) + off < 2 ^ 64)) :
    Operation.gepInt off (.value p) = .poison := by
  simp only [Operation.gepInt, PoisonOr.value_bind, h, ↓reduceIte]

/-- `gepDyn` by an index below `2 ^ 63`: its unsigned reading, the signed one the same. -/
theorem gepDyn_eq_unsigned_of_lt {i : BitVec 64} (hi : i.toNat < 2 ^ 63) :
    Operation.gepDyn byteOff stride ptr (.value i) =
      Operation.gepDynUnsigned byteOff stride ptr (.value i) := by
  have hint : (byteOff : Int) + i.toInt * stride = ((byteOff + i.toNat * stride : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
    push_cast
    rfl
  rw [gepDyn_value_idx, hint]
  simp only [Operation.gepDynUnsigned, PoisonOr.value_bind]
  cases ptr using PoisonOr.casesOn' with
  | poison => split <;> rfl
  | value p =>
    split
    · rename_i h
      by_cases hov : p.offset.uaddOverflow (BitVec.ofNat 64 (byteOff + i.toNat * stride))
      · have hov' : 2 ^ 64 ≤ p.offset.toNat + (byteOff + i.toNat * stride) := by
          simpa [BitVec.uaddOverflow, Nat.mod_eq_of_lt h] using hov
        rw [gep_overflow hov, PoisonOr.poison_orElse, gepInt_of_not]
        omega
      · rw [gep_value hov, PoisonOr.value_orElse]
    · rw [gepInt_of_not]
      omega

/-- `gepDyn` by an index whose offset fits, from a pointer whose offset does not overflow. -/
theorem gepDyn_value {ptr} {i : BitVec 64} (h : byteOff + i.toNat * stride < 2 ^ 64)
    (hov : ¬ptr.offset.uaddOverflow (BitVec.ofNat 64 (byteOff + i.toNat * stride))) :
    Operation.gepDyn byteOff stride (.value ptr) (.value i) =
      .value (ptr.add (BitVec.ofNat 64 (byteOff + i.toNat * stride))) := by
  simp [Operation.gepDyn, h, gep_value hov]

end

end MLIR
