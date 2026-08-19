import Cli
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.LLVMRiscV.ParseAndTransform
import SSA.Projects.RISCV64.ParseAndTransform

set_option compiler.extract_closed false

/-- `verbose_flag` takes in a filename and assuming the file is wellformed,
 prints verbose output to the command line. Additionally it prints
 a string indicating that the verbose flag was set. If the parsing fails,
 it returns with the exit code of 1 to signalize failure. The exit code 1
 indicates success. -/
def verbose_flag (fileName : String ) : IO UInt32 := do
      let icom? ← parseComFromFile fileName
      match icom? with
      | none => return 1
      | some (Sigma.mk _Γ icom) => do
      IO.println "Flag `--verbose` was set."
      IO.println s!"{repr icom}" -- we print everything, meaning effect, return type and com
      return 0

def wellformed (fileName : String ) : IO UInt32 := do
    let icom? ← parseComFromFile fileName
    match icom? with
    | none => return 1
    | some (Sigma.mk _Γ ⟨_eff, ⟨_retTy, c⟩⟩) => do
      IO.println s!"{Com.printModule c}"
      return 0

/-- Parse with the **SLLVM** dialect rather than `LLVM`.

This is the only front end that accepts memory operations, so it is what a
region containing `llvm.load`/`llvm.store` has to be checked against. -/
def wellformedSllvm (fileName : String) : IO UInt32 := do
    let icom? ← Com.parseFromFile LeanMLIR.SLLVM fileName
    match icom? with
    | none => return 1
    | some (Sigma.mk Γ ⟨eff, ⟨retTy, _c⟩⟩) => do
      IO.println s!"ok: {reprStr Γ.toList} -[{reprStr eff}]-> {reprStr retTy}"
      return 0

def runMainCmd (args : Cli.Parsed) : IO UInt32 := do
  let fileName := args.positionalArg! "file" |>.as! String
  if args.hasFlag "verbose" then -- in this case we just mirror the llvm program again and checked that it is wellformed.
    let code ← verbose_flag fileName
    return code
  if args.hasFlag "sllvm" then -- parsing with the SLLVM dialect (the one with memory)
    let code ← wellformedSllvm fileName
    return code
  if args.hasFlag "riscv" then -- parsing as riscv
    let code ←  parseAsRiscv fileName
    return code
  if args.hasFlag "passriscv64" then -- optimized ISel pass including GlobalISel combiners and pseudoops
    let code ← passriscv64 fileName
    return code
  if args.hasFlag "passriscv64_optimized" then -- lowering pass to a RISC-V 64 SSA-assembly IR
    let code ← passriscv64_optimized fileName
    return code
  if args.hasFlag "passriscv64_optimized_const" then -- lowering pass to a RISC-V 64 SSA-assembly IR, including rewrites with constant matching
    let code ← passriscv64_optimized fileName
    return code
  if args.hasFlag "passriscv64_selectiondag" then -- lowering pass to RISC-V 64 SSA-assembly IR applying optimizations from SelectionDAG
    let code ← passriscv64_selectiondag fileName
    return code
  else
    let code ← wellformed fileName
    return code

def mainCmd := `[Cli|
    opt VIA runMainCmd;
    "opt: apply verified rewrites"
    FLAGS:
      verbose; "Prints verbose output for debugging using the Repr typeclass to print."
      passriscv64; "Lowering pass to a RISC-V 64 SSA-assembly IR"
      sllvm; "Parse the file with the SLLVM dialect, which models memory"
      riscv; "Allows to parse a file as a RISC-V 64 SSA-assembly IR"
      passriscv64_optimized; "Allows to parse a file as a RISC-V 64 SSA-assembly IR"
      passriscv64_optimized_const; "Allows to parse a file as a RISC-V 64 SSA-assembly IR, including rewrites with constant matching"
      passriscv64_selectiondag; "Lowering pass to RISC-V 64 SSA-assembly IR applying optimizations from SelectionDAG"
    ARGS:
      file: String; "Input filename"
    ]

def main (args : List String): IO UInt32 :=
  mainCmd.validate args
