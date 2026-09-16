/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
This file should import everything in the LeanMLIR core, *besides* individual dialects
-/
module

public import LeanMLIR.Framework
public import LeanMLIR.Tactic
public import LeanMLIR.Util
public import LeanMLIR.MLIRSyntax

-- ## Transformations
public import LeanMLIR.Transforms.Rewrite
public import LeanMLIR.Transforms.CSE
public import LeanMLIR.Transforms.DCE
