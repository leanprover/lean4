/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Coe
import Init.NotationExtra

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

@[inline]
def OptionArg.toOption {α : Type u} : OptionArg α → Option α
  | OptionArg.none => Option.none
  | OptionArg.some a => Option.some a
