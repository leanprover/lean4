/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Coe
import Init.NotationExtra

set_option linter.missingDocs true
set_option autoImplicit false

universe u

/--
Optional arguments. `OptionArg α` is a synonym `Option α`. The difference is
that there is a coercion `α → OptionArg α` given by `OptionArg.some`, while the corresponding
coercion `α → Option α` is not enabled by default.

The purpose of `OptionArg α` is to allow library authors to make arguments optional from one library
version to another in a non-breaking way.

The API of `OptionArg` is intentionally kept minimal in order to reduce API duplication between
`OptionArg` and `Option`. Given `o : OptionArg α`, `o.toOption` is the corresponding `Option α`,
for which the full option API is then available.
-/
def OptionArg (α : Type u) := Option α

instance optionArgCoe {α : Type u} : Coe α (OptionArg α) where
  coe := some

instance {α : Type u} : Inhabited (OptionArg α) :=
  inferInstanceAs <| Inhabited (Option α)

instance {α : Type u} [DecidableEq α] : DecidableEq (OptionArg α) :=
  inferInstanceAs <| DecidableEq (Option α)
