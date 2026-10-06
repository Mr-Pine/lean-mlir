{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 160 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 192 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 224 : i64}> : () -> i64
    %7 = "llvm.load"(%arg0) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %8 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %9 = "llvm.load"(%8) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %10 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %11 = "llvm.load"(%10) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %12 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %14 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %15 = "llvm.load"(%14) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %16 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %17 = "llvm.load"(%16) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %18 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %19 = "llvm.load"(%18) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %20 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %21 = "llvm.load"(%20) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %22 = "llvm.shufflevector"(%7, %9) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %23 = "llvm.shufflevector"(%7, %9) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %24 = "llvm.shufflevector"(%11, %13) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %25 = "llvm.shufflevector"(%11, %13) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %26 = "llvm.shufflevector"(%15, %17) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %27 = "llvm.shufflevector"(%15, %17) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %28 = "llvm.shufflevector"(%19, %21) <{mask = array<i32: 0, 8, 1, 9, 4, 12, 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %29 = "llvm.shufflevector"(%19, %21) <{mask = array<i32: 2, 10, 3, 11, 6, 14, 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %30 = "llvm.shufflevector"(%22, %24) <{mask = array<i32: 0, 1, 8, 9, 4, 5, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %31 = "llvm.shufflevector"(%22, %24) <{mask = array<i32: 2, 3, 10, 11, 6, 7, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %32 = "llvm.shufflevector"(%23, %25) <{mask = array<i32: 0, 1, 8, 9, 4, 5, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %33 = "llvm.shufflevector"(%23, %25) <{mask = array<i32: 2, 3, 10, 11, 6, 7, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %34 = "llvm.shufflevector"(%26, %28) <{mask = array<i32: 0, 1, 8, 9, 4, 5, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %35 = "llvm.shufflevector"(%26, %28) <{mask = array<i32: 2, 3, 10, 11, 6, 7, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %36 = "llvm.shufflevector"(%27, %29) <{mask = array<i32: 0, 1, 8, 9, 4, 5, 12, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %37 = "llvm.shufflevector"(%27, %29) <{mask = array<i32: 2, 3, 10, 11, 6, 7, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %38 = "llvm.shufflevector"(%30, %34) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%38, %arg0) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %39 = "llvm.shufflevector"(%31, %35) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%39, %8) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %40 = "llvm.shufflevector"(%32, %36) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%40, %10) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %41 = "llvm.shufflevector"(%33, %37) <{mask = array<i32: 0, 1, 2, 3, 8, 9, 10, 11>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%41, %12) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %42 = "llvm.shufflevector"(%30, %34) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%42, %14) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %43 = "llvm.shufflevector"(%31, %35) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%43, %16) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %44 = "llvm.shufflevector"(%32, %36) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%44, %18) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %45 = "llvm.shufflevector"(%33, %37) <{mask = array<i32: 4, 5, 6, 7, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%45, %20) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
