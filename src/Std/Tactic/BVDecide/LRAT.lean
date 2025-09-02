/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Actions
public import Std.Tactic.BVDecide.LRAT.Checker
public import Std.Tactic.BVDecide.LRAT.Parser

@[expose] public section

/-!
This directory contains the implementation of the LRAT certificate checking algorithm as well as
parsers for the binary and the non-binary LRAT format.
-/
