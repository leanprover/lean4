/-!
# Tests for generalized field notation through aliases and "top-level" dot notation
https://github.com/leanprover/lean4/issues/3031
-/

/-!
Alias dot notation. There used to be a different kind of alias dot notation;
in the following example, it would have looked for an argument of type `Common.String`.
Now it looks for one of type `String`, allowing libraries to add "extension methods" from within their own namespaces.
-/
def Common.String.a (s : String) : Nat := s.length

export Common (String.a)

/-- info: String.a "x" : Nat -/
#guard_msgs in #check String.a "x"
/-- info: String.a "x" : Nat -/
#guard_msgs in #check "x".a

/-!
Declarations take precedence over aliases
-/
def String.a (s : String) : Nat := s.length + 100
/-- info: "x".a : Nat -/
#guard_msgs in #check "x".a
/-- info: 100 -/
#guard_msgs in #eval "".a

/-!
Private declarations take precedence over aliases
-/
private def String.b (s : String) : Nat := 0
def Common.String.b (s : String) : Nat := 1
export Common (String.b)
/-- info: 0 -/
#guard_msgs in #eval "".b

/-!
Multiple aliases is an error
-/
def Common.String.c (s : String) : Nat := 0
def Common'.String.c (s : String) : Nat := 0
export Common (String.c)
export Common' (String.c)
/--
error: invalid field notation 'c', the name 'String.c' is ambiguous, possible interpretations: 'Common'.String.c', 'Common.String.c'
-/
#guard_msgs in #eval "".c

/-!
Aliases work with inheritance
-/
namespace Ex1
structure A
structure B extends A
def Common.A.x (_ : A) : Nat := 0
export Common (A.x)
/-- info: fun b => A.x b.toA : B → Nat -/
#guard_msgs in #check fun (b : B) => b.x
end Ex1

/-!
`open` also works
-/
def Common.String.parse (_ : String) : List Nat := []

namespace ExOpen1
/--
error: invalid field 'parse', the environment does not contain 'String.parse'
  ""
has type
  String
-/
#guard_msgs in #check "".parse
section
open Common
/-- info: String.parse "" : List Nat -/
#guard_msgs in #check "".parse
end
section
open Common (String.parse)
/-- info: String.parse "" : List Nat -/
#guard_msgs in #check "".parse
end
end ExOpen1


namespace Ex2
class A (n : Nat) where
  x : Nat

/-!
Incidental fix: `@` for generalized field notation was failing if there were implicit arguments.
True projections were ok.
-/
def A.x' {n : Nat} (a : A n) := a.x

/-- info: fun a => a.x' : A 2 → Nat -/
#guard_msgs in #check fun (a : A 2) => @a.x'
end Ex2

namespace Ex3
variable (f : α → β) (g : β → γ)
/-!
Functions use the "top-level" dot notation rule: they use the first explicit argument, rather than the first function argument.
-/
/-- info: g ∘ f : α → γ -/
#guard_msgs in #check g.comp f
end Ex3
