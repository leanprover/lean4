

open Lean (versionString)

open Nat (zero)

/-- Docs -/
def xyy : Nat := 3

/--
error: unknown identifier 'xy'

Suggestions: 'xyy', 'xyz', 'zxy'
-/
#guard_msgs in
def foo (xyz zxy : Nat) := xy

/--
error: unknown identifier 'zaro'

Suggestion: 'zero'
-/
#guard_msgs in
def foo (xyz zxy : Nat) := zaro

/--
error: unknown identifier 'scc'

Suggestion: 'Acc'
-/
#guard_msgs in
example := scc

/--
error: unknown identifier 'scc'

Suggestions: 'Acc', 'succ'
-/
#guard_msgs in
open Nat in
example := scc

/--
error: unknown identifier 'SuArray'

Suggestions: 'Array', 'Subarray'
-/
#guard_msgs in
def x : Type := SuArray Nat

/--
error: unknown identifier 'Std.Formatxnil'

Suggestion: 'Std.Format.nil'
-/
#guard_msgs in
example := Std.Formatxnil

/-- error: unknown identifier 'Formatxnil' -/
#guard_msgs in
example := Formatxnil

namespace Std

/--
error: unknown identifier 'Formatxnil'

Suggestion: 'Format.nil'
-/
#guard_msgs in
example := Formatxnil

namespace Format


/--
error: unknown identifier 'Asociative'

Suggestion: 'Associative'
-/
#guard_msgs in
example := @Asociative


/--
error: unknown identifier 'niil'

Suggestion: 'nil'
-/
#guard_msgs in
example : Format := niil
