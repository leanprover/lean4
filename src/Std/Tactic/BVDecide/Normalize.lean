/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Canonicalize
public import Std.Tactic.BVDecide.Normalize.Equal
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
This directory contains the lemmas used for the normalizing simp set of `bv_decide`.
They are a combination of:
- rules that turn hypotheses involving `BitVec` and `Bool` into something of the form `x = true`
  where `x` only consists of `BitVec` and `Bool` terms, notably no `Prop`. This makes it easy to
  reflect the terms.
- rewrite rules used by Bitwuzla.
-/
