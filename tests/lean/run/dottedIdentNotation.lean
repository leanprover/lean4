import Lean
/-!
# Tests of dotted identifier notation
-/

/-!
Basic test
-/
/-- info: Nat.zero : Nat -/
#guard_msgs in #check (.zero : Nat)

/-!
Expected type can be a pi type
-/
/-- info: Nat.succ : Nat → Nat -/
#guard_msgs in #check (.succ : _ → Nat)

/-!
Needs expected type
-/
/--
error: Invalid dotted identifier notation: The expected type of `.zero` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `BitVec.zero`
  [apply] `Dyadic.zero`
  [apply] `Nat.zero`
  [apply] `Vector.zero`
  [apply] `Zero.zero`
  [apply] `Lean.Level.zero`
  [apply] `System.Uri.UriEscape.zero`
  [apply] `Lean.Grind.IntModule.OfNatModule.zero`
  [apply] `Lean.Grind.Linarith.Expr.zero`
  [apply] `Std.Time.TimeZone.Offset.zero`
  [apply] `Lean.Elab.Tactic.Do.Uses.zero`
  [apply] `Lean.Meta.Grind.Arith.Linear.NatStruct.zero`
  [apply] `Lean.Meta.Grind.Arith.Linear.Struct.zero`
-/
#guard_msgs in #check .zero

/-!
No resolution.
-/
/--
error: Unknown constant `Nat.doesNotExist`

Note: Inferred this name from the expected resulting type of `.doesNotExist`:
  Nat
-/
#guard_msgs in #check (.doesNotExist : Nat)

/-!
Compound names are not allowed.
-/
def Nat.a.b : Nat := 0
/-- error: Invalid dotted identifier notation: The name `a.b` must be atomic -/
#guard_msgs in #check (.a.b : Nat)

/-!
Can look through abbreviations
-/
abbrev Nat' := Nat
/-- info: Nat.zero : Nat -/
#guard_msgs in #check (.zero : Nat')

/-!
Can make use of definitions in the abbreviation's namespace. (There is an unfolding loop during resolution.)
-/
def Nat'.one := 1
/-- info: Nat'.one : Nat -/
#guard_msgs in #check (.one : Nat')

/-!
Can unfold other definitions too.
-/
def Nat'' := Nat'
/-- info: Nat'.one : Nat -/
#guard_msgs in #check (.one : Nat'')
/-- info: Nat.zero : Nat -/
#guard_msgs in #check (.zero : Nat'')

/-!
When unfolding, reports all errors. Note: we may consider reporting just the first or last error.
-/
/--
error: Unknown constant `Nat''.doesNotExist`

Note: Inferred this name from the expected resulting type of `.doesNotExist`:
  Nat''
---
error: Unknown constant `Nat'.doesNotExist`

Note: Inferred this name from the expected resulting type of `.doesNotExist`:
  Nat''
---
error: Unknown constant `Nat.doesNotExist`

Note: Inferred this name from the expected resulting type of `.doesNotExist`:
  Nat''
-/
#guard_msgs in #check (.doesNotExist : Nat'')

/-!
Can `export` names. Exact matches take precedence over aliases (tested by `.a`)
-/
structure E where
def E.a : E := {}
namespace E
namespace Extra
def a : E := {}
def e : E := {}
end Extra
export Extra (a e)
end E
/-- info: E.a : E -/
#guard_msgs in #check (.a : E)
/-- info: E.e : E -/
#guard_msgs in #check (.e : E)

/-!
Follows `open` namespaces, like for generalized field notation.
-/
namespace MyLib.E
def f : E := {}
def a : E := {}
def e : E := {}
end MyLib.E
/--
error: Unknown constant `E.f`

Note: Inferred this name from the expected resulting type of `.f`:
  E
-/
#guard_msgs in #check (.f : E)
/-- info: E.f : E -/
#guard_msgs in open MyLib in #check (.f : E)

/-!
Exact matches take precedence over `open` names.
-/
/-- info: E.a : E -/
#guard_msgs in open MyLib in #check (.a : E)

/-!
With `open`, ambiguous terms are reported, if they can't otherwise be resolved by elaboration errors.
-/
/--
error: Ambiguous term
  .e
Possible interpretations:
  E.Extra.e : E
  ⏎
  MyLib.E.e : E
-/
#guard_msgs in open MyLib in #check (.e : E)

/-!
Public and private definitions on a public type.
-/
structure A where

def A.foo : A := {}
private def A.foo' : A := {}

/-- info: A.foo : A -/
#guard_msgs in #check (.foo : A)
/-- info: A.foo' : A -/
#guard_msgs in #check (.foo' : A)

/-!
Public and private definitions on an imported type.
-/
def Nat.baz : Nat := 0
private def Nat.baz' : Nat := 0

/-- info: Nat.baz : Nat -/
#guard_msgs in #check (.baz : Nat)
/-- info: Nat.baz' : Nat -/
#guard_msgs in #check (.baz' : Nat)

/-!
Imported private definition on an imported type does not resolve.
-/
/--
error: Unknown constant `Lean.Environment.mk`

Note: Inferred this name from the expected resulting type of `.mk`:
  Lean.Environment
-/
#guard_msgs in #check (.mk : Lean.Environment)

/-!
Public and private definitions on a private type.
A public definition like this does not make sense, but it doesn't hurt letting it resolve.
-/
private structure B where

def B.foo : B := {}
private def B.foo' : B := {}

/-- info: B.foo : B -/
#guard_msgs in #check (.foo : B)
/-- info: B.foo' : B -/
#guard_msgs in #check (.foo' : B)

/-!
No resolution, on a private structure.
-/
/--
error: Unknown constant `B.doesNotExist`

Note: Inferred this name from the expected resulting type of `.doesNotExist`:
  B
-/
#guard_msgs in #check (.doesNotExist : B)

/-!
Possibly there is an abbreviation to a private type, and unfolding leads to considering it.
We disallow this.
-/
elab "aPrivConst%" : term => do
  let c := Lean.mkPrivateNameCore `Lean.Structure `Lean.StructureState
  return Lean.Expr.const c []
/--
error: The private declaration `Lean.StructureState✝` is not accessible in the current context
-/
#guard_msgs in #check (.mk : aPrivConst%)
