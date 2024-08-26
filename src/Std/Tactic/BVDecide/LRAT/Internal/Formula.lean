/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Class
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Instance
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddResult
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddSound
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddSound

/-!
This directory contains the current implementation of the LRAT checker that is plugged into the
generic LRAT checking loop from `LRATChecker` and then used in the surface level LRAT checker
that is publicly exposed.
-/
