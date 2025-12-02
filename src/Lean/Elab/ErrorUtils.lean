/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Simmons
-/
module

prelude
import Init.Notation
import Init.Data.String

/--
Translate numbers (1, 2, 3, ...) to ordinals ("first", "second", "third", ...). Not appropriate for
numbers that could conceivably be larger
than 19 in real examples.
-/
def _root_.Nat.toOrdinal : Nat -> String
  | 0 => "zeroth"
  | 1 => "first"
  | 2 => "second"
  | 3 => "third"
  | 4 => "fourth"
  | 5 => "fifth"
  | n => if n % 100 > 10 && n % 100 < 20 then
      s!"{n}th"
    else if n % 10 == 2 then
      s!"{n}nd"
    else if n % 10 == 3 then
      s!"{n}rd"
    else
      s!"{n}th"

/-- Make an oxford-comma-separated list of strings. -/
private def _root_.List.toOxford : List String -> String
  | [] => ""
  | [a] => a
  | [a, b] => a ++ " and " ++ b
  | [a, b, c] => a ++ ", " ++ b  ++ ", and " ++ c
  | a :: as => a ++ ", " ++ toOxford as

/--
Give alternative forms of a string if the `count` is 1 or not.

 - `(1).plural == ""`
 - `(2).plural == "s"`
 - `(1).plural "wug" == "wug"`
 - `(2).plural "wug" == "wugs"`
 - `(1).plural "it" "they" == "it"`
 - `(2).plural "it" "they" == "they"`
-/
private def _root_.Nat.plural (count : Nat) (singular : String := "") (plural : String := singular ++ "s") :=
  if count = 1 then
    singular
  else
    plural
