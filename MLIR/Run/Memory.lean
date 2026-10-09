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
  simp [Operation.store, hroom, hp, throwUBIf, Ty.flattenDef_of_flatten hv hpad, mlir_effect,
    MemoryState.storeAt]

/-- A store of any value: its bits, defined but in poison leaves and padding. -/
theorem run_storeDef {ptr : Pointer} {t : Ty} {v : ⟦t⟧} (hroom : Room s.mem ptr t.width)
    (hp : t.hasPtr = false) :
    (Operation.store (.value ptr) v) env s =
      .value (env, { s with mem := s.mem.storeDef ptr (t.flattenDef v).1 (t.flattenDef v).2 }) := by
  simp [Operation.store, hroom, hp, throwUBIf, mlir_effect]

/-- `memcpy` of `n` known bytes: a store at `dst` of the bits read at `src`. -/
theorem run_memcpy {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hd : (Range.of dst (8 * n)).Disjoint (Range.of src (8 * n))) (hfd : Room s.mem dst (8 * n))
    (hfs : Fits s.mem src (8 * n)) :
    (Operation.memcpy (.value dst) (.value src) (.value len)) env s =
      .value (env, { s with mem := s.mem.storeAt dst (s.mem.readAt src (8 * n)) }) := by
  subst hn
  simp [Operation.memcpy, hd, hfd, hfs.room, throwUBIf, mlir_effect,
    MemoryState.definedAt_of_fits hfs, MemoryState.storeAt]

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

/-- `memset` of `n` bytes: a store at `src` of the repeated byte. -/
theorem run_memset {dst : Pointer} {val : BitVec 8} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hfd : Room s.mem dst (8 * n)) :
    (Operation.memset (.value dst) (.value val) (.value len)) env s =
      .value (env, { s with mem := s.mem.storeAt dst (val.replicate n) }) := by
  subst hn
  simp [Operation.memset, hfd, throwUBIf, mlir_effect]

/-- A load of known bits: their value. -/
theorem run_load {ptr : Pointer} {t : Ty} {v} {dst : Dst Γ t} (hfits : Fits s.mem ptr t.width)
    (hv : (t.unflatten (s.mem.readAt ptr t.width)) = v) :
    (Operation.load dst (.value ptr)) env s = .value (env[dst := v], s) := by
  simp [Operation.load, hfits.inBounds, throwUBIf, ← hv, mlir_effect,
    MemoryState.definedAt_of_fits hfits, Ty.unflattenDef_allOnes]

/-- A load of any bits in bounds: poison leaves where they are undefined. -/
theorem run_loadDef {ptr : Pointer} {t : Ty} {dst : Dst Γ t} (h : InBounds s.mem ptr t.width) :
    (Operation.load dst (.value ptr)) env s =
      .value
        (env[dst := t.unflattenDef (s.mem.readAt ptr t.width) (s.mem.definedAt ptr t.width)],
          s) := by
  simp [Operation.load, h, throwUBIf, mlir_effect]

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
  simp only [Instr.run, EffectM.bind_eq, hv, PoisonOr.value_bind, hp, throwUBIf, Bool.false_eq_true,
    ↓reduceIte, Ty.flattenDef_of_flatten hb hpad]
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

@[mlir_operation]
theorem gep_value {ptr} (h : ¬ptr.offset.uaddOverflow off) :
    Operation.gep (.value off) (.value ptr) = .value (ptr.add off) := by simp [Operation.gep, h]

/-- `gepBack` by at most the pointer's offset. -/
@[mlir_operation]
theorem gepBack_value {ptr} (h : n ≤ ptr.offset.toNat) :
    Operation.gepBack n (.value ptr) = .value (ptr.add (-BitVec.ofNat 64 n)) := by
  simp [Operation.gepBack, Nat.not_lt.mpr h]

/-- `gepDyn` by an index whose offset fits, from a pointer whose offset does not overflow. -/
@[mlir_operation]
theorem gepDyn_value {ptr} {i : BitVec 64} (h : byteOff + i.toNat * stride < 2 ^ 64)
    (hov : ¬ptr.offset.uaddOverflow (BitVec.ofNat 64 (byteOff + i.toNat * stride))) :
    Operation.gepDyn byteOff stride (.value ptr) (.value i) =
      .value (ptr.add (BitVec.ofNat 64 (byteOff + i.toNat * stride))) := by
  simp [Operation.gepDyn, h, gep_value hov]

end

end MLIR
