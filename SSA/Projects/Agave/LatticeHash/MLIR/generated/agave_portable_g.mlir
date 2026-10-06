{
  ^bb0(%arg0: !llvm.ptr, %arg1: i32, %arg2: i32):
    %0 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 16 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 20 : i32}> : () -> i32
    %5 = "llvm.mlir.constant"() <{value = 24 : i32}> : () -> i32
    %6 = "llvm.mlir.constant"() <{value = 25 : i32}> : () -> i32
    %7 = "llvm.load"(%arg0) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %8 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %9 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %10 = "llvm.add"(%7, %arg1) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
    %11 = "llvm.add"(%10, %9) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
    %12 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %14 = "llvm.xor"(%13, %11) : (i32, i32) -> i32
    %15 = "llvm.intr.fshl"(%14, %14, %2) : (i32, i32, i32) -> i32
    %16 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %17 = "llvm.load"(%16) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %18 = "llvm.add"(%17, %15) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
    %19 = "llvm.xor"(%18, %9) : (i32, i32) -> i32
    %20 = "llvm.intr.fshl"(%19, %19, %4) : (i32, i32, i32) -> i32
    %21 = "llvm.add"(%11, %arg2) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
    %22 = "llvm.add"(%21, %20) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
    "llvm.store"(%22, %arg0) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %23 = "llvm.xor"(%22, %15) : (i32, i32) -> i32
    %24 = "llvm.intr.fshl"(%23, %23, %5) : (i32, i32, i32) -> i32
    "llvm.store"(%24, %12) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %25 = "llvm.add"(%24, %18) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
    "llvm.store"(%25, %16) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %26 = "llvm.xor"(%25, %20) : (i32, i32) -> i32
    %27 = "llvm.intr.fshl"(%26, %26, %6) : (i32, i32, i32) -> i32
    "llvm.store"(%27, %8) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
