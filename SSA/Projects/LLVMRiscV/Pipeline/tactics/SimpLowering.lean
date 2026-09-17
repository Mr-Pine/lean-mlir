import SSA.Projects.RISCV64.Tactic.SimpRiscV
import SSA.Projects.InstCombine.ForLean
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import LeanMLIR.Dialects.LLVM.Syntax
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

open Lean
open Lean.Elab.Tactic

/-- Shifts by a constant `BitVec` amount go through `Nat`: v4.34 `bv_decide` fails on them
with "constant shift should have been eliminated". -/
theorem shiftLeft_ofNat_eq_shiftLeft_toNat {w v : Nat} (x : BitVec w) (n : Nat) :
    x <<< BitVec.ofNat v n = x <<< (BitVec.ofNat v n).toNat :=
  BitVec.shiftLeft_eq' ..

/-
This file defines the `simp_lowering` tactic, which combines the LLVM tactics with the RISC-V simplification
tactic and invokes `bv_decide`. The tactic is designed to solve instruction lowering patterns that
fall within the domain solvable by `bv_decide`. We have enhanced the LLVM tactics to handle PoisonOr
cases, and the RISC-V tactic simplifies RISC-V definitions so that the remaining goals are suitable
for `bv_decide`.
To enable this proof automation, rewrite implementors must tag their rewrite rules with
`@[simp_denote]`. This ensures that the initial invocation of `simp_peephole` within the
`simp_lowering` tactic unfolds the relevant definitions, allowing subsequent tactics to proceed.

The purpose of this tactic is to maximize proof automation for instruction lowering rewrite patterns
-/
macro "simp_lowering" : tactic =>
  `(tactic|
    ( simp_peephole
      simp_alive_undef
      simp_riscv
      simp_alive_ops
      simp_alive_case_bash
      -- v4.34: case bashing leaves raw `nat_lit` widths in binder types, which `bv_decide` rejects
      all_goals try dsimp only
      -- v4.34: `simp_riscv` rewrites `if` conditions but not their `Decidable` instances,
      -- which then only typecheck past `implicit` transparency
      set_option backward.isDefEq.respectTransparency false in simp_alive_split
      all_goals try simp only [shiftLeft_ofNat_eq_shiftLeft_toNat]))
