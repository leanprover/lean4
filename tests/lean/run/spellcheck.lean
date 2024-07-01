
/-! Tests the spelling suggestions provided for identifiers -/
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

/-! Check that opening Nat did the right thing here -/
/--
error: unknown identifier 'zaro'

Suggestion: 'zero'
-/
#guard_msgs in
def foo (xyz zxy : Nat) := zaro

/-! Check that opening Nat did not bring `succ` into scope -/
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

/-! Check that dots are fixable just like any other typo -/
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

end Std.Format

/-!
# Protected Names

Test that protected names are respected.
-/

namespace Test
def abcdefg : Unit := ()
protected def abcdefh : Unit := ()
end Test

/--
error: unknown identifier 'abcdef'

Suggestion: 'id_def'
-/
#guard_msgs in
example : Unit := abcdef

/--
error: unknown identifier 'abcdef'

Suggestion: 'abcdefg'
-/
#guard_msgs in
open Test in
example : Unit := abcdef

/--
error: unknown identifier 'abcdefh'

Suggestion: 'abcdefg'
-/
#guard_msgs in
open Test in
example : Unit := abcdefh

/--
error: unknown identifier 'Test.abcdef'

Suggestions: 'Test.abcdefg', 'Test.abcdefh'
-/
#guard_msgs in
example : Unit := Test.abcdef
