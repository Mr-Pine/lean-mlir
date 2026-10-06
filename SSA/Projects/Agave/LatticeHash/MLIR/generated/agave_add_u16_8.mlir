{
  ^bb0(%arg30: !llvm.ptr, %arg31: !llvm.ptr, %arg32: !llvm.ptr):
    %2589 = "llvm.load"(%arg31) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<16xi16>
    %2590 = "llvm.load"(%arg32) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<16xi16>
    %2591 = "llvm.add"(%2590, %2589) <{overflowFlags = 0 : i32}> : (vector<16xi16>, vector<16xi16>) -> vector<16xi16>
    "llvm.store"(%2591, %arg30) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<16xi16>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
