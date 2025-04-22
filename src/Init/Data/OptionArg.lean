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
Optional arguments. As an inductive type, `OptionArg α` is the same as `Option α`. The difference is
that there is a coercion `α → OptionArg α` given by `OptionArg.some`, while the corresponding
coercion `α → Option α` is not enabled by default.

The purpose of `OptionArg α` is to allow library authors to make arguments optional from one library
version to another in a non-breaking way.

The API of `OptionArg` is intentionally kept minimal in order to reduce API duplication between
`OptionArg` and `Option`. Given `o : OptionArg α`, `o.toOption` is the corresponding `Option α`,
for which the full option API is then available.
-/
inductive OptionArg (α : Type u) : Type u where
  /-- No value. -/
  | none : OptionArg α
  /-- Some value of type `α`. -/
  | some (val : α) : OptionArg α
deriving DecidableEq

instance {α : Type u} : Inhabited (OptionArg α) where
  default := .none

instance optionArgCoe {α : Type u} : Coe α (OptionArg α) where
  coe := OptionArg.some

namespace OptionArg

/-- Convert an `OptionArg α` to `Option α` by mapping `none` to `none` and `some a` to `some a`. -/
@[inline] def toOption {α : Type u} : OptionArg α → Option α
  | .none => .none
  | .some a => .some a

@[simp]
theorem toOption_some {α : Type u} {a : α} : (OptionArg.some a).toOption = Option.some a := rfl

@[simp]
theorem toOption_none {α : Type u} : (OptionArg.none : OptionArg α).toOption = Option.none := rfl

/-- Returns `true` on `some x` and `false` on `none`. -/
@[inline] def isSome {α : Type u} : OptionArg α → Bool
  | .none => false
  | .some _ => true

@[simp]
theorem isSome_eq {α : Type u} {o : OptionArg α} : o.isSome = o.toOption.isSome := by
  cases o <;> simp [isSome]

/--
Gets an optional value, returning a given default on `none`.

This function is `@[macro_inline]`, so `fallback` will not be evaluated unless `o` turns out to be
`none`.
-/
@[macro_inline] def getD {α : Type u} (o : OptionArg α) (fallback : α) : α :=
  match o with
  | .none => fallback
  | .some a => a

@[simp]
theorem getD_eq {α : Type u} {o : OptionArg α} {fallback : α} :
    o.getD fallback = o.toOption.getD fallback := by
  cases o <;> simp [getD]

end OptionArg
