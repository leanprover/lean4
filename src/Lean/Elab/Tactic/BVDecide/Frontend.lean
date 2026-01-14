/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Elab.Tactic.BVDecide.Frontend.Attr
public import Lean.Elab.Tactic.BVDecide.Frontend.BVCheck
public import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide
public import Lean.Elab.Tactic.BVDecide.Frontend.BVTrace
public import Lean.Elab.Tactic.BVDecide.Frontend.LRAT
public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize

public section

/-!
This module provides the tactic frontends, consisting of:
- `bv_decide`, the bitblasting based `BitVec` decision procedure itself.
- `bv_check`, like `bv_decide` but the LRAT proof is provided as a file so no need to call a SAT solver.
- `bv_decide?`, converts `bv_decide?` into `bv_check` calls.
-/
