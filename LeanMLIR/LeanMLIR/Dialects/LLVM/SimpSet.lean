/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Meta.Tactic.Simp.Attr

public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Lean.LabelAttribute

@[expose] public section

register_simp_attr simp_llvm

register_simp_attr simp_llvm_option

/-- The simp-set used in `simp_alive_case_bash` to attempt to discharge trivial `none` cases -/
register_simp_attr simp_llvm_case_bash

register_simp_attr simp_llvm_split

register_simp_attr bv_ofBool
