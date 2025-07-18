/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast
public import Std.Tactic.BVDecide.LRAT
public import Std.Tactic.BVDecide.Normalize
public import Std.Tactic.BVDecide.Reflect
public import Std.Tactic.BVDecide.Syntax

@[expose] public section

/-!
This directory contains the implementation of the bitblaster and LRAT checker for `bv_decide`,
as well as custom theorems used for reflection.
-/
