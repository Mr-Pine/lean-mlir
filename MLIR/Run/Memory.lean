module

public import MLIR.Semantics.Instruction
public import MLIR.Semantics.GlobalInitializer

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
pointers recorded, their addresses there. -/
theorem run_storeValue {ptr : Pointer} {t : Ty} {v : ⟦t⟧} (hroom : Room s.mem ptr t.width) :
    (Operation.store (.value ptr) v) env s =
      .value
        (env,
          { s with
            mem :=
              (s.mem.storeDef ptr (t.flattenDef v).1 (t.flattenDef v).2).recordPtrs ptr
                (t.ptrLeaves 0 v) }) := by
  simp [Operation.store, hroom, throwUBIf, mlir_effect]

/-- A store of a pointer: its address, the pointer recorded. -/
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
  simp [Operation.memcpy, hd, hfd, hfs.live, throwUBIf, mlir_effect,
    MemoryState.storeCopy_of_fits hfs]

/-- `memcpy` of `n` bytes: their bits, which are defined, and the live pointers among them. -/
theorem run_memcpyDef {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hd : (Range.of dst (8 * n)).Disjoint (Range.of src (8 * n))) (hfd : Room s.mem dst (8 * n))
    (hfs : Live s.mem src (8 * n)) :
    (Operation.memcpy (.value dst) (.value src) (.value len)) env s =
      .value
        (env,
          { s with
            mem :=
              s.mem.storeCopy dst (s.mem.readAt src (8 * n)) (s.mem.definedAt src (8 * n))
                (s.mem.ptrsIn src (8 * n)) }) := by
  subst hn
  simp [Operation.memcpy, hd, hfd, hfs, throwUBIf, mlir_effect]

/-- `memcpy` of `n` bytes carrying no live pointer: their bits and which are defined. -/
theorem run_memcpyDef_noPtrs {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hd : (Range.of dst (8 * n)).Disjoint (Range.of src (8 * n))) (hfd : Room s.mem dst (8 * n))
    (hfs : Live s.mem src (8 * n)) (hp : s.mem.ptrsIn src (8 * n) = fun _ => none) :
    (Operation.memcpy (.value dst) (.value src) (.value len)) env s =
      .value
        (env,
          { s with
            mem :=
              s.mem.storeDef dst (s.mem.readAt src (8 * n)) (s.mem.definedAt src (8 * n)) }) := by
  rw [run_memcpyDef hn hd hfd hfs, MemoryState.storeCopy_of_ptrsIn hp]

/-- `memmove` of `n` known bytes: a store at `dst` of the bits read at `src`, which may overlap. -/
theorem run_memmove {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hfd : Room s.mem dst (8 * n)) (hfs : Fits s.mem src (8 * n)) :
    (Operation.memmove (.value dst) (.value src) (.value len)) env s =
      .value (env, { s with mem := s.mem.storeAt dst (s.mem.readAt src (8 * n)) }) := by
  subst hn
  simp [Operation.memmove, hfd, hfs.live, throwUBIf, mlir_effect,
    MemoryState.storeCopy_of_fits hfs]

/-- `memmove` of `n` bytes: their bits, which are defined, and the live pointers among them. -/
theorem run_memmoveDef {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hfd : Room s.mem dst (8 * n)) (hfs : Live s.mem src (8 * n)) :
    (Operation.memmove (.value dst) (.value src) (.value len)) env s =
      .value
        (env,
          { s with
            mem :=
              s.mem.storeCopy dst (s.mem.readAt src (8 * n)) (s.mem.definedAt src (8 * n))
                (s.mem.ptrsIn src (8 * n)) }) := by
  subst hn
  simp [Operation.memmove, hfd, hfs, throwUBIf, mlir_effect]

/-- `memmove` of `n` bytes carrying no live pointer: their bits and which are defined. -/
theorem run_memmoveDef_noPtrs {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hfd : Room s.mem dst (8 * n)) (hfs : Live s.mem src (8 * n))
    (hp : s.mem.ptrsIn src (8 * n) = fun _ => none) :
    (Operation.memmove (.value dst) (.value src) (.value len)) env s =
      .value
        (env,
          { s with
            mem :=
              s.mem.storeDef dst (s.mem.readAt src (8 * n)) (s.mem.definedAt src (8 * n)) }) := by
  rw [run_memmoveDef hn hfd hfs, MemoryState.storeCopy_of_ptrsIn hp]

/-- `ptrtoaddr`: the value of the state's addresses, the state unchanged. -/
theorem run_ptrtoaddr {dst : Dst Γ (.bv w)} {p : Reg Γ .ptr} :
    Instr.run env (.ptrtoaddr dst p) s =
      .value (env.write dst (Operation.ptrtoaddr s.mem.addr (env.read p)), s) :=
  rfl

/-- `masked.load` with no poison mask lane and every set lane in bounds: the set lanes' bits, the
others `passthru`'s, the state unchanged. -/
theorem run_maskedLoad {dst : Dst Γ (.vec l w)} {p : Pointer} {mask : ⟦.vec l 1⟧}
    {passthru : ⟦.vec l w⟧} (hm : mask.toList.any (·.isPoison) = false)
    (hb : ∀ i : Fin l, mask[i] = .value 1#1 → Operation.LaneInBounds s.mem p w i) :
    (Operation.maskedLoad dst (.value p) mask passthru) env s =
      .value
        (env.write dst
            (Vector.ofFn fun i =>
              if mask[i] = .value 1#1 then
                (Ty.bv w).unflattenDef (s.mem.readAt (Operation.lanePtr p w i) w)
                  (s.mem.knownAt (Operation.lanePtr p w i) w)
              else passthru[i]),
          s) := by
  have hb' : ¬∃ i : Fin l, mask[(i : Nat)] = .value 1#1 ∧ ¬Operation.LaneInBounds s.mem p w i :=
    fun ⟨i, h, h'⟩ => h' (hb i h)
  simp [Operation.maskedLoad, hm, hb', throwUBIf, mlir_effect]

/-- `masked.store` with no poison mask lane and no set lane's offset wrapping: a `store` per set
lane, first to last. -/
theorem run_maskedStore {v : ⟦.vec l w⟧} {p : Pointer} {mask : ⟦.vec l 1⟧}
    (hm : mask.toList.any (·.isPoison) = false)
    (hw : ∀ i : Fin l, mask[i] = .value 1#1 → p.offset.toNat + i * (w / 8) < 2 ^ 64) :
    Operation.maskedStore v (.value p) mask env (Γ := Γ) =
      (List.finRange l).foldlM (init := env) fun env (i : Fin l) =>
        if mask[i] = .value 1#1 then
          Operation.store (τ := .bv w) (.value (Operation.lanePtr p w i)) v[i] env
        else pure env := by
  simp only [Operation.maskedStore, hm, throwUBIf, Bool.false_eq_true, ite_false, pure_bind,
    show ¬¬∀ i : Fin l, _ from fun h => h hw]

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
    MemoryState.knownAt_of_fits hfits, Ty.unflattenDef_allOnes, Ty.setPtrs_of_hasPtr hp]

/-- A load of bits all read as known (a stored pointer's address), of a type without pointers:
their value. -/
theorem run_load_known {ptr : Pointer} {t : Ty} {v} {dst : Dst Γ t}
    (h : InBounds s.mem ptr t.width) (hk : s.mem.knownAt ptr t.width = BitVec.allOnes _)
    (hv : (t.unflatten (s.mem.readAt ptr t.width)) = v) (hp : t.hasPtr = false := by simp) :
    (Operation.load dst (.value ptr)) env s = .value (env[dst := v], s) := by
  simp [Operation.load, h, throwUBIf, ← hv, mlir_effect, hk, Ty.unflattenDef_allOnes,
    Ty.setPtrs_of_hasPtr hp]

/-- A load of any bits in bounds, of a type without pointers: poison leaves where they are not
known. -/
theorem run_loadDef {ptr : Pointer} {t : Ty} {dst : Dst Γ t} (h : InBounds s.mem ptr t.width)
    (hp : t.hasPtr = false := by simp) :
    (Operation.load dst (.value ptr)) env s =
      .value
        (env[dst := t.unflattenDef (s.mem.readAt ptr t.width) (s.mem.knownAt ptr t.width)], s) := by
  simp [Operation.load, h, throwUBIf, mlir_effect, Ty.setPtrs_of_hasPtr hp]

/-- A load of any bits in bounds with no live pointer over them, of a type without pointers:
poison leaves where they are undefined. -/
theorem run_loadDef_of_ptrFree {ptr : Pointer} {t : Ty} {dst : Dst Γ t}
    (h : InBounds s.mem ptr t.width) (hf : PtrFree s.mem ptr t.width)
    (hp : t.hasPtr = false := by simp) :
    (Operation.load dst (.value ptr)) env s =
      .value
        (env[dst := t.unflattenDef (s.mem.readAt ptr t.width) (s.mem.definedAt ptr t.width)],
          s) := by
  rw [run_loadDef h hp, MemoryState.knownAt_of_ptrFree hf]

/-- A load of any value in bounds: poison leaves where they are not known, pointer leaves the
pointers stored there. -/
theorem run_loadValue {ptr : Pointer} {t : Ty} {dst : Dst Γ t} (h : InBounds s.mem ptr t.width) :
    (Operation.load dst (.value ptr)) env s =
      .value
        (env[dst :=
            t.setPtrs 0 (fun o => s.mem.ptrAt ptr.id (ptr.offsetInBits + o))
              (t.unflattenDef (s.mem.readAt ptr t.width) (s.mem.knownAt ptr t.width))],
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

theorem run_addressof {Γ : Ctx} {env : ⟪Γ⟫} {s : GlobalState} {dst : Dst Γ .ptr}
    (h : s.mem.globals sym = some (b, g)) :
    Instr.run env (.addressof sym dst) s = .value (env.write dst (.value ⟨b, 0⟩), s) := by
  simp [Instr.run, h, mlir_effect]

/-! ### A global's block, from its image -/

/-- A global's image is `(t.width + 7) / 8` bytes long. -/
theorem GlobalInitializer.image_bytes {g : GlobalInitializer} :
    g.image.bytes = (g.t.width + 7) / 8 := by
  unfold image; split <;> rfl

/-- A block holding an image, from its start: in bounds for its bytes. -/
theorem GlobalImage.inBounds {m : MemoryState} {img : GlobalImage}
    (hb : m[b]? = some (img.block r a)) (hn : img.bytes = n) : InBounds m ⟨b, 0⟩ (8 * n) :=
  ⟨_, hb, by simp [Pointer.offsetInBits, MemoryBlock.lengthInBits, GlobalImage.block, hn]⟩

/-- A block holding an image is live in its bounds. -/
theorem GlobalImage.live {m : MemoryState} {img : GlobalImage} (hb : m[b]? = some (img.block r a))
    (hn : img.bytes = n) : Live m ⟨b, 0⟩ (8 * n) :=
  ⟨_, hb, rfl, by simp [Pointer.offsetInBits, MemoryBlock.lengthInBits, GlobalImage.block, hn]⟩

/-- A mutable global's image's block: writable, so room in its bounds. -/
theorem GlobalImage.room {m : MemoryState} {img : GlobalImage} (hb : m[b]? = some (img.block r a))
    (hn : img.bytes = n) (hc : img.constant = false) : Room m ⟨b, 0⟩ (8 * n) :=
  ⟨GlobalImage.live hb hn, _, hb, by simp [GlobalImage.block, hc]⟩

/-- A global's bits read from its block's start, `w` of them: its value's, without pointer
members. -/
theorem GlobalInitializer.readAt {m : MemoryState} {g : GlobalInitializer} {x : ⟦g.t⟧}
    (hb : m[b]? = some (g.image.block r a)) (hv : ∀ s, g.value s = .value (x, s))
    (hp : g.ptrs = []) (hw : g.t.width = w) {B : BitVec w}
    (hB : (g.t.flattenDef x).1 = B.cast hw.symm) : m.readAt ⟨b, 0⟩ w = B := by
  subst hw
  simp only [BitVec.cast_eq] at hB
  rw [image_eq hv] at hb
  simp only [MemoryState.readAt, hb, GlobalImage.block, GlobalImage.linkedBits, hp, List.foldl_nil,
    hB, Pointer.offsetInBits]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i < 8 * ((g.t.width + 7) / 8) := by omega
  simp [hi, this]

/-- A global's defined bits at its block's start, `w` of them: its value's. -/
theorem GlobalInitializer.definedAt {m : MemoryState} {g : GlobalInitializer} {x : ⟦g.t⟧}
    (hb : m[b]? = some (g.image.block r a)) (hv : ∀ s, g.value s = .value (x, s))
    (hw : g.t.width = w) {D : BitVec w} (hD : (g.t.flattenDef x).2 = D.cast hw.symm) :
    m.definedAt ⟨b, 0⟩ w = D := by
  subst hw
  simp only [BitVec.cast_eq] at hD
  rw [image_eq hv] at hb
  simp only [MemoryState.definedAt, hb, GlobalImage.block, hD, Pointer.offsetInBits]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i < 8 * ((g.t.width + 7) / 8) := by omega
  simp [hi, this]

/-- A constant global without pointer members holds no pointer. -/
theorem PtrFree.of_global {s : GlobalState} {g : GlobalInitializer} {q : Pointer} (hwf : s.WF)
    (hg : s.mem.globals sym = some (q.id, g.image)) (hc : g.constant = true) (hp : g.ptrs = []) :
    PtrFree s.mem q w := by
  have hb := hwf.const_block hg (by rw [GlobalInitializer.image_constant, hc])
  have hi : g.image.ptrs = [] := by unfold GlobalInitializer.image; split <;> simp [hp]
  refine ⟨fun o _ _ => ?_⟩
  simp [MemoryState.ptrAt, hb, MemoryState.imageBlock, GlobalImage.block, MemoryBlock.ptrAt,
    GlobalImage.linkedPtrs, hi]

/-- A plain global's bits: its raw value's, all defined. -/
theorem GlobalInitializer.flattenDef_wrap {g : GlobalInitializer} {w : Nat} {r : ⟦g.t⟧ᵣ}
    (hp : g.t.hasPtr = false) (hpad : g.t.hasPadding = false) (hw : g.t.width = w) :
    g.t.flattenDef (Ty.wrap r) =
      ((Ty.flatBits r (hw := hw)).cast hw.symm, (BitVec.allOnes w).cast hw.symm) := by
  subst hw
  rw [Ty.flattenDef_of_flatten (Ty.flatten_wrap hp) hpad]
  simp [Ty.flatBits_eq]

/-- A writable block is no read-only one's. -/
theorem Writable.ne_of_readOnly {m : MemoryState} {blk : MemoryBlock} (hq : Writable m q)
    (hb : m[b]? = some blk) (hro : blk.writable = false) : q.id ≠ b := by
  rintro rfl
  obtain ⟨blk', hb', hw⟩ := hq
  rw [hb] at hb'
  cases hb'
  simp [hw] at hro

/-- A constant global's block is read-only. -/
theorem GlobalImage.block_writable {img : GlobalImage} (hc : img.constant = true) :
    (img.block r a).writable = false := by simp [GlobalImage.block, hc]

/-- A constant global's block in `m` is read-only. -/
theorem MemoryState.imageBlock_writable {m : MemoryState} {img : GlobalImage}
    (hc : img.constant = true) : (m.imageBlock img).writable = false :=
  GlobalImage.block_writable hc

/-- A mutable global's block in a `WF` state: in bounds for its bytes. -/
theorem GlobalState.WF.mutable_inBounds {s : GlobalState} (hwf : s.WF)
    (h : s.mem.globals sym = some (b, g)) (hc : g.constant = false) (hn : g.bytes = n) :
    InBounds s.mem ⟨b, 0⟩ (8 * n) := by
  obtain ⟨blk, hb, -, hl⟩ := hwf.mutable_block h hc
  exact ⟨blk, hb, by simp [Pointer.offsetInBits, MemoryBlock.lengthInBits, hl, hn]⟩

/-- A mutable global's block in a `WF` state is writable. -/
theorem GlobalState.WF.mutable_writable {s : GlobalState} (hwf : s.WF)
    (h : s.mem.globals sym = some (b, g)) (hc : g.constant = false) : Writable s.mem ⟨b, 0⟩ := by
  obtain ⟨blk, hb, hw, -⟩ := hwf.mutable_block h hc
  exact ⟨blk, hb, hw⟩

/-- Live, with its first `w` bits defined: they fit. -/
theorem Fits.of_definedAt_self {m : MemoryState} {p : Pointer} {D : BitVec v} (hl : Live m p v)
    (hd : m.definedAt p v = D) (hw : w ≤ v) (hD : D.extractLsb' 0 w = BitVec.allOnes w) :
    Fits m p w := by
  obtain ⟨blk, hblk, hlv, hsz⟩ := hl
  refine ⟨blk, hblk, hlv, by omega, ?_⟩
  subst hd
  simp only [MemoryState.definedAt, hblk,
    BitVec.extractLsb'_extractLsb'_add (show 0 + w ≤ v by omega), Nat.add_zero] at hD
  exact hD

/-- Live, with its bits at `p.add off` defined: they fit. -/
theorem Fits.of_definedAt {m : MemoryState} {p : Pointer} {off : BitVec 64} {D : BitVec v}
    (hl : Live m p v) (hd : m.definedAt p v = D) (hov : ¬p.offset.uaddOverflow off)
    (hw : off.toNat * 8 + w ≤ v) (hD : D.extractLsb' (off.toNat * 8) w = BitVec.allOnes w) :
    Fits m (p.add off) w := by
  obtain ⟨blk, hblk, hlv, hsz⟩ := hl
  have hblk' : m[(p.add off).id]? = some blk := hblk
  refine
    ⟨blk, hblk', hlv, by
      rw [Pointer.offsetInBits_add hov]; omega, ?_⟩
  subst hd
  simp only [MemoryState.definedAt, hblk, BitVec.extractLsb'_extractLsb'_add hw] at hD
  rw [Pointer.offsetInBits_add hov]
  exact hD

/-- `gep` without flags: the address, wrapping. -/
@[mlir_operation]
theorem gep_none {ptr : Pointer} :
    Operation.gep {} (.value off) (.value ptr) = .value (ptr.add off) := by
  simp [Operation.gep]

/-- `gep`'s `nusw` test: the offset, signed, takes the address out of `[0, 2 ^ 64)`. -/
theorem gep_nusw_iff (a off : BitVec 64) :
    (if off.msb then a.toNat < (-off).toNat else a.uaddOverflow off) ↔
      ¬(0 ≤ (a.toNat : Int) + off.toInt ∧ (a.toNat : Int) + off.toInt < 2 ^ 64) := by
  have ha := a.isLt
  have ho := off.isLt
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases hm : off.msb
  · have h : 2 ^ 63 ≤ off.toNat := by
      simpa [BitVec.msb_eq_decide] using hm
    simp only [hm, ↓reduceIte, BitVec.toNat_neg]
    split <;> omega
  · have h : off.toNat < 2 ^ 63 := by
      simpa [BitVec.msb_eq_decide] using hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte, BitVec.uaddOverflow, decide_eq_true_eq]
    split <;> omega

/-- An offset below `2 ^ 63` is not negative. -/
theorem msb_of_lt {off : BitVec 64} (h : off.toNat < 2 ^ 63) : off.msb = false := by
  simp [BitVec.msb_eq_decide]
  omega

/-- `gep` by an offset that does not wrap, below `2 ^ 63` for `nusw`. -/
theorem gep_value {f : GepFlags} {ptr : Pointer} (h : ¬ptr.offset.uaddOverflow off)
    (hs : f.nusw = false ∨ off.toNat < 2 ^ 63) :
    Operation.gep f (.value off) (.value ptr) = .value (ptr.add off) := by
  rcases hs with hs | hs
  · simp [Operation.gep, h, hs]
  · simp [Operation.gep, h, msb_of_lt hs]

/-- `gep` by an offset that wraps: poison, for `nuw`, or `nusw` with the offset below `2 ^ 63`. -/
theorem gep_overflow {f : GepFlags} {ptr : Pointer} (h : ptr.offset.uaddOverflow off)
    (hf : f.nuw = true ∨ f.nusw = true ∧ off.toNat < 2 ^ 63) :
    Operation.gep f (.value off) (.value ptr) = .poison := by
  rcases hf with hf | ⟨hf, hs⟩
  · simp [Operation.gep, h, hf]
  · simp only [Operation.gep, PoisonOr.value_bind, h, and_true, hf, msb_of_lt hs,
      Bool.false_eq_true, ↓reduceIte]
    split <;> rfl

/-- `gepBack` without flags: the address, wrapping. -/
@[mlir_operation]
theorem gepBack_none {ptr : Pointer} :
    Operation.gepBack {} n (.value ptr) = .value (ptr.add (-BitVec.ofNat 64 n)) := by
  simp [Operation.gepBack]

/-- `gepBack` by at most the pointer's offset, without `nuw`. -/
theorem gepBack_value {f : GepFlags} {ptr : Pointer} (h : n ≤ ptr.offset.toNat)
    (hf : f.nuw = false) :
    Operation.gepBack f n (.value ptr) = .value (ptr.add (-BitVec.ofNat 64 n)) := by
  simp [Operation.gepBack, Nat.not_lt.mpr h, hf]

/-- `gepSigned` whose offset and the addresses it passes through stay in range. -/
theorem gepSigned_value {byteOff stride : Nat} {f : GepFlags} {p : Pointer} {i : BitVec 64}
    (h₀ : -2 ^ 63 ≤ i.toInt * stride) (h₁ : byteOff + i.toInt * stride < 2 ^ 63)
    (h₂ : (byteOff : Int) < 2 ^ 63) (h₃ : (p.offset.toNat : Int) + byteOff < 2 ^ 64)
    (h₄ : 0 ≤ (p.offset.toNat : Int) + i.toInt * stride)
    (h₅ : 0 ≤ (p.offset.toNat : Int) + byteOff + i.toInt * stride)
    (h₆ : (p.offset.toNat : Int) + byteOff + i.toInt * stride < 2 ^ 64)
    (h₇ : f.nuw = true → p.offset.toNat + (byteOff + i.toNat * stride) < 2 ^ 64) :
    Operation.gepSigned f byteOff stride i (.value p) =
      .value (p.add (BitVec.ofInt 64 (byteOff + i.toInt * stride))) := by
  simp only [Operation.gepSigned, PoisonOr.value_bind]
  rw [ite_eq_left ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩]

@[mlir_operation]
theorem gepSigned_poison : Operation.gepSigned f byteOff stride i .poison = .poison :=
  rfl

@[mlir_operation]
theorem gepDyn_poison : Operation.gepDyn f byteOff stride ptr .poison = .poison :=
  rfl

/-- `gepDyn` by a value index, unfolded. -/
theorem gepDyn_value_idx {i : BitVec 64} :
    Operation.gepDyn f byteOff stride ptr (.value i) =
      if f.nusw ∧ 2 ^ 63 ≤ byteOff + i.toNat * stride then
        Operation.gepSigned f byteOff stride i ptr
      else if f.nuw ∧ ¬byteOff + i.toNat * stride < 2 ^ 64 then
        .poison
      else
        Operation.gep f (.value (BitVec.ofNat 64 (byteOff + i.toNat * stride))) ptr :=
  rfl

/-- `gepDyn` without `nusw`: the offset read unsigned, poison for `nuw` where it wraps. -/
theorem gepDyn_of_not_nusw {i : BitVec 64} (hf : f.nusw = false) :
    Operation.gepDyn f byteOff stride ptr (.value i) =
      if f.nuw ∧ ¬byteOff + i.toNat * stride < 2 ^ 64 then
        .poison
      else
        Operation.gep f (.value (BitVec.ofNat 64 (byteOff + i.toNat * stride))) ptr := by
  simp [gepDyn_value_idx, hf]

/-- `gepDyn_of_not_nusw` by bytes: the `gep` by the index itself. -/
theorem gepDyn_zero_one_of_not_nusw {i : BitVec 64} (hf : f.nusw = false) :
    Operation.gepDyn f 0 1 ptr (.value i) = Operation.gep f (.value i) ptr := by
  simp [gepDyn_of_not_nusw hf, i.isLt]

/-- `gepDyn` with `nusw` by an offset below `2 ^ 63`, where the signed and unsigned readings agree:
the `gep` by it, unsigned. -/
theorem gepDyn_of_lt {i : BitVec 64} (hf : f.nusw = true)
    (h : byteOff + i.toNat * stride < 2 ^ 63) :
    Operation.gepDyn f byteOff stride ptr (.value i) =
      Operation.gep { nuw := true } (.value (BitVec.ofNat 64 (byteOff + i.toNat * stride)))
        ptr := by
  have hlt : (BitVec.ofNat 64 (byteOff + i.toNat * stride)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact h
  rw [gepDyn_value_idx, ite_eq_right (by omega), ite_eq_right (by omega)]
  cases ptr using PoisonOr.casesOn' with
  | poison => rfl
  | value p =>
    by_cases hov : p.offset.uaddOverflow (BitVec.ofNat 64 (byteOff + i.toNat * stride))
    · rw [gep_overflow hov (.inr ⟨hf, hlt⟩), gep_overflow hov (.inl rfl)]
    · rw [gep_value hov (.inr hlt), gep_value hov (.inl rfl)]

/-- A masked index is below `2 ^ 63` where its mask is. -/
theorem toNat_and_lt {x c : BitVec 64} (h : c.toNat < 2 ^ 63) : (x &&& c).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right h

/-- `gepDyn_of_lt` by bytes: the `gep` by the index itself. -/
theorem gepDyn_zero_one_of_lt {i : BitVec 64} (hf : f.nusw = true) (h : i.toNat < 2 ^ 63) :
    Operation.gepDyn f 0 1 ptr (.value i) = Operation.gep { nuw := true } (.value i) ptr := by
  rw [gepDyn_of_lt hf (by omega)]
  simp

/-- `i.toInt * stride` read unsigned, where the index is below `2 ^ 63` or does not count. -/
theorem toInt_mul_of_lt {stride : Nat} {i : BitVec 64} (h : stride = 0 ∨ i.toNat < 2 ^ 63) :
    i.toInt * (stride : Int) = ((i.toNat * stride : Nat) : Int) := by
  rcases h with h | h
  · simp [h]
  · rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
    push_cast
    rfl

/-- `gepDyn` with `nusw` whose unsigned `gep` is poison: the signed one (also poison where the
offset is below `2 ^ 63`). -/
theorem gepDyn_of_unsigned_poison {i : BitVec 64} (hf : f.nusw = true)
    (h : Operation.gep { nuw := true } (.value (BitVec.ofNat 64 (byteOff + i.toNat * stride))) ptr =
      .poison) :
    Operation.gepDyn f byteOff stride ptr (.value i) =
      Operation.gepSigned f byteOff stride i ptr := by
  by_cases hge : 2 ^ 63 ≤ byteOff + i.toNat * stride
  · rw [gepDyn_value_idx, ite_eq_left ⟨hf, hge⟩]
  rw [gepDyn_of_lt hf (by omega), h]
  cases ptr using PoisonOr.casesOn' with
  | poison => rfl
  | value p =>
    have hov : p.offset.uaddOverflow (BitVec.ofNat 64 (byteOff + i.toNat * stride)) := by
      cases hb : p.offset.uaddOverflow (BitVec.ofNat 64 (byteOff + i.toNat * stride))
      · rw [gep_value (by simp [hb]) (.inl rfl)] at h
        exact absurd h (PoisonOr.value_ne_poison _)
      · rfl
    have h' : 2 ^ 64 ≤ p.offset.toNat + (byteOff + i.toNat * stride) := by
      simpa [BitVec.uaddOverflow, Nat.mod_eq_of_lt (show byteOff + i.toNat * stride < 2 ^ 64 by
        omega)] using hov
    have hd := toInt_mul_of_lt (i := i) (stride := stride)
      (by rcases Nat.eq_zero_or_pos stride with h0 | h0
          · exact .inl h0
          · right
            have : i.toNat ≤ i.toNat * stride := Nat.le_mul_of_pos_right _ h0
            omega)
    simp only [Operation.gepSigned, PoisonOr.value_bind, hd]
    rw [ite_eq_right (by omega)]

/-- `gepDyn_of_unsigned_poison` by bytes. -/
theorem gepDyn_zero_one_of_unsigned_poison {i : BitVec 64} (hf : f.nusw = true)
    (h : Operation.gep { nuw := true } (.value i) ptr = .poison) :
    Operation.gepDyn f 0 1 ptr (.value i) = Operation.gepSigned f 0 1 i ptr :=
  gepDyn_of_unsigned_poison hf (by simpa using h)

/-- `gepDyn` by an index whose offset fits (below `2 ^ 63` for `nusw`), from a pointer whose offset
does not overflow. -/
theorem gepDyn_value {ptr : Pointer} {i : BitVec 64} (h : byteOff + i.toNat * stride < 2 ^ 64)
    (hs : f.nusw = false ∨ byteOff + i.toNat * stride < 2 ^ 63)
    (hov : ¬ptr.offset.uaddOverflow (BitVec.ofNat 64 (byteOff + i.toNat * stride))) :
    Operation.gepDyn f byteOff stride (.value ptr) (.value i) =
      .value (ptr.add (BitVec.ofNat 64 (byteOff + i.toNat * stride))) := by
  cases hn : f.nusw
  · rw [gepDyn_of_not_nusw hn, ite_eq_right (by omega), gep_value hov (.inl hn)]
  · rw [gepDyn_of_lt hn (by simpa [hn] using hs), gep_value hov (.inl rfl)]

end

end MLIR
