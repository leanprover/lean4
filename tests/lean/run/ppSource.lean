import Lean.PrettyPrinter.Source

open Lean PrettyPrinter in
/--
info: def foo :=
  1
-/
#guard_msgs in
#eval do
  let input := "def foo:=1\n"
  let result ← ppSource input "<test>"
  IO.println result

open Lean PrettyPrinter in
/--
info: def foo :=
  1
def bar :=
  2
-/
#guard_msgs in
#eval do
  let input := "def foo:=1\ndef bar:=2\n"
  let result ← ppSource input "<test>"
  IO.println result

-- Test that comments between commands are preserved
open Lean PrettyPrinter in
/--
info: def foo :=
  1

-- a comment
def bar :=
  2
-/
#guard_msgs in
#eval do
  let input := "def foo := 1\n\n-- a comment\ndef bar := 2\n"
  let result ← ppSource input "<test>"
  IO.println result

-- Test that already-formatted input round-trips
open Lean PrettyPrinter in
/-- info: true -/
#guard_msgs in
#eval do
  let input := "def foo :=\n  1\n"
  let result ← ppSource input "<test>"
  IO.println (result == input)

-- Test blank line collapsing (3+ newlines → 2)
open Lean PrettyPrinter in
/--
info: def foo :=
  1

def bar :=
  2
-/
#guard_msgs in
#eval do
  let input := "def foo := 1\n\n\n\ndef bar := 2\n"
  let result ← ppSource input "<test>"
  IO.println result
