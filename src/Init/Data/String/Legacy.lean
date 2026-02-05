/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.Basic

/-!
# Legacy string functions

This file contains `String` functions which have since been replaced by different functions and
will be deprecated in the future.
-/

public section

namespace String

@[specialize] def splitAux (s : String) (p : Char → Bool) (b : Pos.Raw) (i : Pos.Raw) (r : List String) : List String :=
  if h : i.atEnd s then
    let r := (b.extract s i)::r
    r.reverse
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (Pos.Raw.lt_next s _)
    if p (i.get s) then
      let i' := i.next s
      splitAux s p i' i' (b.extract s i :: r)
    else
      splitAux s p b (i.next s) r
termination_by s.rawEndPos.1 - i.1

/--
Splits a string at each character for which `p` returns `true`.

The characters that satisfy `p` are not included in any of the resulting strings. If multiple
characters in a row satisfy `p`, then the resulting list will contain empty strings.

This is a legacy function. Use `String.split` instead.

Examples:
* `"coffee tea water".split (·.isWhitespace) = ["coffee", "tea", "water"]`
* `"coffee  tea  water".split (·.isWhitespace) = ["coffee", "", "tea", "", "water"]`
* `"fun x =>\n  x + 1\n".split (· == '\n') = ["fun x =>", "  x + 1", ""]`
-/
@[inline] def splitToList (s : String) (p : Char → Bool) : List String :=
  splitAux s p 0 0 []

/--
Auxiliary for `splitOn`. Preconditions:
* `sep` is not empty
* `b <= i` are indexes into `s`
* `j` is an index into `sep`, and not at the end

It represents the state where we have currently parsed some split parts into `r` (in reverse order),
`b` is the beginning of the string / the end of the previous match of `sep`, and the first `j` bytes
of `sep` match the bytes `i-j .. i` of `s`.
-/
def splitOnAux (s sep : String) (b : Pos.Raw) (i : Pos.Raw) (j : Pos.Raw) (r : List String) : List String :=
  if i.atEnd s then
    let r := (b.extract s i)::r
    r.reverse
  else
    if i.get s == j.get sep then
      let i := i.next s
      let j := j.next sep
      if j.atEnd sep then
        splitOnAux s sep i i 0 (b.extract s (i.unoffsetBy j)::r)
      else
        splitOnAux s sep b i j r
    else
      splitOnAux s sep b ((i.unoffsetBy j).next s) 0 r
termination_by (s.rawEndPos.1 - (j.byteDistance i), sep.rawEndPos.1 - j.1)
decreasing_by
  focus
    rename_i h _ _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Pos.Raw.lt_next s _))
  focus
    rename_i i₀ j₀ _ eq h'
    rw [show (j₀.next sep).byteDistance (i₀.next s) = j₀.byteDistance i₀ by
      change (_ + Char.utf8Size _) - (_ + Char.utf8Size _) = _
      rw [(beq_iff_eq ..).1 eq, Nat.add_sub_add_right]; rfl]
    right; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.le_add_right ..) (Nat.gt_of_not_le (mt decide_eq_true h')))
      (Pos.Raw.lt_next sep _)
  focus
    rename_i h _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (Pos.Raw.lt_next s _)

/--
Splits a string `s` on occurrences of the separator string `sep`. The default separator is `" "`.

When `sep` is empty, the result is `[s]`. When `sep` occurs in overlapping patterns, the first match
is taken. There will always be exactly `n+1` elements in the returned list if there were `n`
non-overlapping matches of `sep` in the string. The separators are not included in the returned
substrings.

This is a legacy function. Use `String.split` instead.

Examples:
* `"here is some text ".splitOn = ["here", "is", "some", "text", ""]`
* `"here is some text ".splitOn "some" = ["here is ", " text "]`
* `"here is some text ".splitOn "" = ["here is some text "]`
* `"ababacabac".splitOn "aba" = ["", "bac", "c"]`
-/
@[inline] def splitOn (s : String) (sep : String := " ") : List String :=
  if sep == "" then [s] else splitOnAux s sep 0 0 0 []

end String
