{
  ^bb0(%arg5: !llvm.ptr, %arg6: !llvm.ptr, %arg7: !llvm.ptr):
    %186 = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i64
    %187 = "llvm.mlir.constant"() <{value = 768 : i64}> : () -> i64
    %188 = "llvm.mlir.constant"() <{value = dense<16> : vector<16xi32>}> : () -> vector<16xi32>
    %189 = "llvm.mlir.constant"() <{value = 512 : i64}> : () -> i64
    %190 = "llvm.mlir.constant"() <{value = dense<20> : vector<16xi32>}> : () -> vector<16xi32>
    %191 = "llvm.mlir.constant"() <{value = dense<24> : vector<16xi32>}> : () -> vector<16xi32>
    %192 = "llvm.mlir.constant"() <{value = dense<25> : vector<16xi32>}> : () -> vector<16xi32>
    %193 = "llvm.load"(%arg6) <{alignment = 64 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<16xi32>
    %194 = "llvm.load"(%arg7) <{alignment = 64 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<16xi32>
    %195 = "llvm.load"(%arg5) <{alignment = 64 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<16xi32>
    %196 = "llvm.getelementptr"(%arg5, %186) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %197 = "llvm.load"(%196) <{alignment = 64 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<16xi32>
    %198 = "llvm.add"(%195, %193) <{overflowFlags = 0 : i32}> : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %199 = "llvm.add"(%198, %197) <{overflowFlags = 0 : i32}> : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %200 = "llvm.getelementptr"(%arg5, %187) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %201 = "llvm.load"(%200) <{alignment = 64 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<16xi32>
    %202 = "llvm.xor"(%199, %201) : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %203 = "llvm.intr.fshl"(%202, %202, %188) : (vector<16xi32>, vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %204 = "llvm.getelementptr"(%arg5, %189) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %205 = "llvm.load"(%204) <{alignment = 64 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<16xi32>
    %206 = "llvm.add"(%203, %205) <{overflowFlags = 0 : i32}> : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %207 = "llvm.xor"(%206, %197) : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %208 = "llvm.intr.fshl"(%207, %207, %190) : (vector<16xi32>, vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %209 = "llvm.add"(%199, %194) <{overflowFlags = 0 : i32}> : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %210 = "llvm.add"(%209, %208) <{overflowFlags = 0 : i32}> : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    "llvm.store"(%210, %arg5) <{alignment = 64 : i64, ordering = 0 : i64}> : (vector<16xi32>, !llvm.ptr) -> ()
    %211 = "llvm.xor"(%210, %203) : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %212 = "llvm.intr.fshl"(%211, %211, %191) : (vector<16xi32>, vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    "llvm.store"(%212, %200) <{alignment = 64 : i64, ordering = 0 : i64}> : (vector<16xi32>, !llvm.ptr) -> ()
    %213 = "llvm.add"(%212, %206) <{overflowFlags = 0 : i32}> : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    "llvm.store"(%213, %204) <{alignment = 64 : i64, ordering = 0 : i64}> : (vector<16xi32>, !llvm.ptr) -> ()
    %214 = "llvm.xor"(%213, %208) : (vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    %215 = "llvm.intr.fshl"(%214, %214, %192) : (vector<16xi32>, vector<16xi32>, vector<16xi32>) -> vector<16xi32>
    "llvm.store"(%215, %196) <{alignment = 64 : i64, ordering = 0 : i64}> : (vector<16xi32>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
