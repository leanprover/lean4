/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast
import Std.Tactic.BVDecide.LRAT
import Std.Tactic.BVDecide.Normalize
import Std.Tactic.BVDecide.Reflect
import Std.Tactic.BVDecide.Syntax

/-!
This directory contains the implementation of the bitblaster and LRAT checker for `bv_decide`,
as well as custom theorems used for reflection.
-/
