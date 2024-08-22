/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Actions
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Assignment
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.CNF
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Formula
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Entails
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Assignment
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Clause
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.LRATChecker
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.PosFin
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Convert

/-!
This module contains the internals of the current LRAT checker implementation. It should not be
considered part of the API of `bv_decide` and will be removed or largely refactored in the future.
-/
