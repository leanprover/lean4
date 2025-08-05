/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.ProofMode
public import Std.Tactic.Do.Syntax

@[expose] public section

/-!
This directory contains the syntax definition for tactics related to the proof mode of `Std.Do.SPred`.
Their builtin implementation lives in `Lean.Elab.Tactic.Do` to enable using the tactics without
public importing `Lean`.
-/
