/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Key

/-!
# Lake Targets

This module contains the declarative definition of a `Target`.
-/

open Std

namespace Lake

/-- A Lake target that is expected to produce an output of a specific type. -/
public structure Target (α : Type) where
  key : PartialBuildKey

/--
Shorthand for `Array (Target α)` that supports
dot notation for Lake-specific operations (e.g., `fetch`).
-/
public abbrev TargetArray α := Array (Target α)

namespace Target

public protected def repr (x : Target α) (prec : Nat) : Format :=
  let indent := if prec >= max_prec then 1 else 2
  let ctor := "Lake.Target.mk" ++ Format.line ++ reprArg x.key
  Repr.addAppParen (.group (.nest indent ctor)) prec

public instance : Repr (Target α) := ⟨Target.repr⟩
public instance : ToString (Target α) := ⟨(·.key.toString)⟩
public instance : Coe PartialBuildKey (Target α) := ⟨Target.mk⟩
