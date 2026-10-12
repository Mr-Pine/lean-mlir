module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # Pointers in memory: stored, loaded back and through; a dynamic `gep` back; libsodium's
`crypto_verify_n`, its operands' pointers in `volatile` locals -/

namespace MLIR.Tests.Syntax.Pointers

@[expose] public section

/-- A pointer stored into a slot, loaded back, and loaded through. -/
mlir_def viaSlot := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
    "llvm.store"(%arg0, %1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    %2 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %3 = "llvm.load"(%2) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%3) : (i64) -> ()
}

/-- `p[-1]`, by a dynamic index. -/
mlir_def back := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %1 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %2 = "llvm.load"(%1) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    "llvm.return"(%2) : (i8) -> ()
}

mlir_def crypto_verify_n :=
"llvm.func"() <{CConv = #llvm.cconv<fastcc>, arg_attrs = [{llvm.nonnull, llvm.noundef}, {llvm.nonnull, llvm.noundef}, {llvm.noundef, llvm.range = #llvm.constant_range<i32, 16, 65>}], dso_local, function_type = !llvm.func<i32 (ptr, ptr, i32)>, linkage = #llvm.linkage<internal>, memory_effects = #llvm.memory_effects<other = read, argMem = read, inaccessibleMem = readwrite, errnoMem = read, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, passthrough = ["nofree", "norecurse", "nosync", "ssp", ["min-legal-vector-width", "128"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.range = #llvm.constant_range<i32, -1, 65535>}], sym_name = "crypto_verify_n", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 2 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
^bb0(%arg12: !llvm.ptr, %arg13: !llvm.ptr, %arg14: i32):
  %161 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
  %162 = "llvm.mlir.constant"() <{value = 31 : i32}> : () -> i32
  %163 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
  %164 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
  %165 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
  %166 = "llvm.mlir.constant"() <{value = dense<0> : vector<4xi32>}> : () -> vector<4xi32>
  %167 = "llvm.mlir.constant"() <{value = dense<0> : vector<16xi8>}> : () -> vector<16xi8>
  %168 = "llvm.mlir.constant"() <{value = dense<0> : vector<2xi64>}> : () -> vector<2xi64>
  %169 = "llvm.mlir.constant"() <{value = 16 : i32}> : () -> i32
  %170 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
  %171 = "llvm.alloca"(%161) <{alignment = 16 : i64, elem_type = vector<2xi64>}> : (i32) -> !llvm.ptr
  %172 = "llvm.alloca"(%161) <{alignment = 16 : i64, elem_type = vector<2xi64>}> : (i32) -> !llvm.ptr
  %173 = "llvm.alloca"(%161) <{alignment = 16 : i64, elem_type = vector<2xi64>}> : (i32) -> !llvm.ptr
  %174 = "llvm.alloca"(%161) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
  %175 = "llvm.alloca"(%161) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
  %176 = "llvm.alloca"(%161) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
  "llvm.intr.lifetime.start"(%171) : (!llvm.ptr) -> ()
  "llvm.intr.lifetime.start"(%172) : (!llvm.ptr) -> ()
  "llvm.intr.lifetime.start"(%173) : (!llvm.ptr) -> ()
  "llvm.intr.lifetime.start"(%174) : (!llvm.ptr) -> ()
  "llvm.intr.lifetime.start"(%175) : (!llvm.ptr) -> ()
  "llvm.store"(%arg12, %175) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr, !llvm.ptr) -> ()
  "llvm.intr.lifetime.start"(%176) : (!llvm.ptr) -> ()
  "llvm.store"(%arg13, %176) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr, !llvm.ptr) -> ()
  %177 = "llvm.load"(%175) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> !llvm.ptr
  %178 = "llvm.load"(%177) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
  "llvm.store"(%178, %171) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %179 = "llvm.load"(%176) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> !llvm.ptr
  %180 = "llvm.load"(%179) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
  "llvm.store"(%180, %172) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %181 = "llvm.load"(%171) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %182 = "llvm.load"(%172) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %183 = "llvm.xor"(%182, %181) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
  "llvm.store"(%183, %173) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %184 = "llvm.icmp"(%arg14, %162) <{predicate = 8 : i64}> : (i32, i32) -> i1
  "llvm.cond_br"(%184)[^bb1, ^bb4] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^bb1:  // pred: ^bb0
  %185 = "llvm.lshr"(%arg14, %163) : (i32, i32) -> i32
  %186 = "llvm.load"(%175) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> !llvm.ptr
  %187 = "llvm.getelementptr"(%186) <{elem_type = i8, noWrapFlags = 0 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
  %188 = "llvm.load"(%187) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
  "llvm.store"(%188, %171) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %189 = "llvm.load"(%176) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> !llvm.ptr
  %190 = "llvm.getelementptr"(%189) <{elem_type = i8, noWrapFlags = 0 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
  %191 = "llvm.load"(%190) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
  "llvm.store"(%191, %172) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %192 = "llvm.load"(%173) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %193 = "llvm.load"(%171) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %194 = "llvm.load"(%172) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %195 = "llvm.xor"(%194, %193) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
  %196 = "llvm.or"(%195, %192) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
  "llvm.store"(%196, %173) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %197 = "llvm.icmp"(%185, %164) <{predicate = 0 : i64}> : (i32, i32) -> i1
  "llvm.cond_br"(%197)[^bb4, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^bb2:  // pred: ^bb1
  %198 = "llvm.load"(%175) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> !llvm.ptr
  %199 = "llvm.getelementptr"(%198) <{elem_type = i8, noWrapFlags = 0 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
  %200 = "llvm.load"(%199) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
  "llvm.store"(%200, %171) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %201 = "llvm.load"(%176) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> !llvm.ptr
  %202 = "llvm.getelementptr"(%201) <{elem_type = i8, noWrapFlags = 0 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
  %203 = "llvm.load"(%202) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
  "llvm.store"(%203, %172) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %204 = "llvm.load"(%173) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %205 = "llvm.load"(%171) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %206 = "llvm.load"(%172) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %207 = "llvm.xor"(%206, %205) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
  %208 = "llvm.or"(%207, %204) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
  "llvm.store"(%208, %173) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %209 = "llvm.icmp"(%185, %165) <{predicate = 0 : i64}> : (i32, i32) -> i1
  "llvm.cond_br"(%209)[^bb4, ^bb3] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^bb3:  // pred: ^bb2
  %210 = "llvm.load"(%175) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> !llvm.ptr
  %211 = "llvm.getelementptr"(%210) <{elem_type = i8, noWrapFlags = 0 : i32, rawConstantIndices = array<i32: 48>}> : (!llvm.ptr) -> !llvm.ptr
  %212 = "llvm.load"(%211) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
  "llvm.store"(%212, %171) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %213 = "llvm.load"(%176) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> !llvm.ptr
  %214 = "llvm.getelementptr"(%213) <{elem_type = i8, noWrapFlags = 0 : i32, rawConstantIndices = array<i32: 48>}> : (!llvm.ptr) -> !llvm.ptr
  %215 = "llvm.load"(%214) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
  "llvm.store"(%215, %172) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %216 = "llvm.load"(%173) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %217 = "llvm.load"(%171) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %218 = "llvm.load"(%172) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %219 = "llvm.xor"(%218, %217) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
  %220 = "llvm.or"(%219, %216) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
  "llvm.store"(%220, %173) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  "llvm.br"()[^bb4] : () -> ()
^bb4:  // 4 preds: ^bb0, ^bb1, ^bb2, ^bb3
  %221 = "llvm.load"(%173) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> vector<2xi64>
  %222 = "llvm.bitcast"(%221) : (vector<2xi64>) -> vector<4xi32>
  %223 = "llvm.icmp"(%222, %166) <{predicate = 0 : i64}> : (vector<4xi32>, vector<4xi32>) -> vector<4xi1>
  %224 = "llvm.sext"(%223) : (vector<4xi1>) -> vector<4xi32>
  %225 = "llvm.bitcast"(%224) : (vector<4xi32>) -> vector<16xi8>
  %226 = "llvm.icmp"(%225, %167) <{predicate = 2 : i64}> : (vector<16xi8>, vector<16xi8>) -> vector<16xi1>
  %227 = "llvm.bitcast"(%226) : (vector<16xi1>) -> i16
  %228 = "llvm.zext"(%227) : (i16) -> i32
  "llvm.store"(%228, %174) <{alignment = 4 : i64, ordering = 0 : i64, volatile_}> : (i32, !llvm.ptr) -> ()
  "llvm.store"(%168, %171) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  "llvm.store"(%168, %172) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  "llvm.store"(%168, %173) <{alignment = 16 : i64, ordering = 0 : i64, volatile_}> : (vector<2xi64>, !llvm.ptr) -> ()
  %229 = "llvm.load"(%174) <{alignment = 4 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i32
  %230 = "llvm.add"(%229, %161) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
  %231 = "llvm.lshr"(%230, %169) : (i32, i32) -> i32
  %232 = "llvm.add"(%231, %170) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
  "llvm.intr.lifetime.end"(%176) : (!llvm.ptr) -> ()
  "llvm.intr.lifetime.end"(%175) : (!llvm.ptr) -> ()
  "llvm.intr.lifetime.end"(%174) : (!llvm.ptr) -> ()
  "llvm.intr.lifetime.end"(%173) : (!llvm.ptr) -> ()
  "llvm.intr.lifetime.end"(%172) : (!llvm.ptr) -> ()
  "llvm.intr.lifetime.end"(%171) : (!llvm.ptr) -> ()
  "llvm.return"(%232) : (i32) -> ()
}) : () -> ()

end

/-! ## Steps -/

-- the pointer read back from the slot, the word through it
example (p : Pointer) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 64) :
    viaSlot.call (viaSlot.args (.value p)) s =
      .value
        (.cons (.value (s.mem.readAt p 64)) .nil,
          { s with alloc := ⟨s.alloc.nextFreeBlock + 1⟩ }) := by
  func_init
  block_init
  step_pure
  step_alloca
  step_store
  guard_hyp hread_v1 : S.mem.loadPtr v1 = .value p
  step_load
  step_load with v
  finish_block
  subst hS
  erase_frame
  subst hv
  rfl

-- a byte back from `q`, which is a byte into its block
example (q : Pointer) (s : GlobalState) (hwf : s.WF)
    (hq : Fits s.mem (q.add 18446744073709551615#64) 8) (ho : q.offset = 1#64) :
    back.call (back.args (.value q)) s =
      .value (.cons (.value (s.mem.readAt (q.add 18446744073709551615#64) 8)) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pure
  step_load with v
  finish_block
  subst hS hv
  rfl

/-! ## Execution tests -/

section Tests

private def x : Pointer := ⟨⟨1⟩, 0⟩
private def y : Pointer := ⟨⟨2⟩, 0⟩

/-- `x` and `y`, 32 bytes each. -/
private def s0 (a b : Nat) : GlobalState :=
  ⟨⟨3⟩, ⟨Std.ExtHashMap.ofList [(⟨1⟩, .ofBytes 32 (BitVec.ofNat 256 a)),
    (⟨2⟩, .ofBytes 32 (BitVec.ofNat 256 b))]⟩⟩

private def verifyOut (a b : Nat) (n : BitVec 32 := 32) : Option ⟦Ty.bv 32⟧ :=
  match crypto_verify_n.eval 5 (crypto_verify_n.args (.value x) (.value y) (.value n)) (s0 a b) with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

#guard verifyOut 0x1234 0x1234 == some (.value 0)
#guard verifyOut 0x1234 0x1235 == some (.value (-1))
#guard verifyOut (2 ^ 255) 0 == some (.value (-1))
#guard verifyOut (2 ^ 256 - 1) (2 ^ 256 - 1) == some (.value 0)
-- 16 bytes compared only
#guard verifyOut (2 ^ 255) 0 16 == some (.value 0)

private def backOut (off : Nat) : Option ⟦Ty.bv 8⟧ :=
  match back.eval 1 (back.args (.value ⟨⟨1⟩, BitVec.ofNat 64 off⟩)) (s0 0x0201 0) with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

#guard backOut 1 == some (.value 1)
#guard backOut 2 == some (.value 2)
-- before the block's start: poison, a load of which is UB
#guard backOut 0 == none

end Tests

end MLIR.Tests.Syntax.Pointers
