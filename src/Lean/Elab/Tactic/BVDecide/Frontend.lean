/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Attr
import Lean.Elab.Tactic.BVDecide.Frontend.BVCheck
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide
import Lean.Elab.Tactic.BVDecide.Frontend.BVTrace
import Lean.Elab.Tactic.BVDecide.Frontend.LRAT
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize

/-!
This module provides the tactic frontends, consisting of:
- `bv_decide`, the bitblasting based `BitVec` decision procedure itself.
- `bv_check`, like `bv_decide` but the LRAT proof is provided as a file so no need to call a SAT solver.
- `bv_decide?`, converts `bv_decide?` into `bv_check` calls.
-/
