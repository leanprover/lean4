/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Defs
public import Init.Data.Iterators.Combinators.FilterMap
public import Init.Data.String.Pattern
public import Init.Data.String.ToSlice
public import Init.Data.String.Slice

set_option doc.verso true

/-!
# String API
-/

public section

namespace String

section
open String.Slice Pattern

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]


/--
Constructs a new string obtained by replacing all occurrences of {name}`pattern` with
{name}`replacement` in {name}`s`.

Examples:
* {lean}`"red green blue".replace "e" "" = "rd grn blu"`
* {lean}`"red green blue".replace "ee" "E" = "red grEn blue"`
* {lean}`"red green blue".replace "e" "E" = "rEd grEEn bluE"`
* {lean}`"abc".replace "" "k" = "rakbkck"`
-/
@[inline]
def replace [ToForwardSearcher ρ σ] [ToSlice α] (s : String) (pattern : ρ)
    (replacement : α) : String :=
  s.toSlice.replace pattern replacement

end

end String
