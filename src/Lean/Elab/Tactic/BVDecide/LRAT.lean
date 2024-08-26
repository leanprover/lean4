/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.LRAT.Trim
import Lean.Elab.Tactic.BVDecide.LRAT.Parser

/-!
This directory contains the implementation of the LRAT parsing and trimming algorithms.
They mostly live here because they used datastructures and parsing infrastructure from `Lean`.
Otherwise they could be put into `Std.Tactic.BVDecide.LRAT`.
-/
