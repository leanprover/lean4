/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Class
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Instance
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddResult
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddSound
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddSound

@[expose] public section

/-!
This directory contains the current implementation of the LRAT checker that is plugged into the
generic LRAT checking loop from `LRATChecker` and then used in the surface level LRAT checker
that is publicly exposed.
-/
