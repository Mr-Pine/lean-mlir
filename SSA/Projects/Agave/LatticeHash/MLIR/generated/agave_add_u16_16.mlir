{
  ^bb0(%arg33: !llvm.ptr, %arg34: !llvm.ptr, %arg35: !llvm.ptr):
    %2592 = "llvm.load"(%arg34) <{alignment = 64 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<32xi16>
    %2593 = "llvm.load"(%arg35) <{alignment = 64 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<32xi16>
    %2594 = "llvm.add"(%2593, %2592) <{overflowFlags = 0 : i32}> : (vector<32xi16>, vector<32xi16>) -> vector<32xi16>
    "llvm.store"(%2594, %arg33) <{alignment = 64 : i64, ordering = 0 : i64}> : (vector<32xi16>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
