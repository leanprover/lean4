/-!
# Error messages for matches with incorrect numbers of patterns

https://github.com/leanprover/lean4/issues/7170

Error messages for `match` expressions and definitions by pattern matching where an incorrect or
inconsistent number of patterns are supplied should indicate this issue and should only assert that
a given number of patterns is "incorrect" (rather than merely "inconsistent") when the number of
discriminants has been explicitly specified by the user.
-/

inductive Foo
  | foo
  | foo2

def correct : Foo → Foo → Prop
  | .foo => fun _ => True
  | .foo2 => fun _ => False

/--
error: inconsistent number of patterns in match alternatives: this alternative contains 2 patterns:
  .foo2, x
but a preceding alternative contains 1:
  .foo
-/
#guard_msgs in
def patCountMismatch : Foo → Foo → Prop
  | .foo => fun _ => True
  | .foo2, x => False

/--
error: cannot define a value of type
  Nat
by pattern matching

Only values of function types can be defined by pattern matching, but the type
  Nat
is not a function type.
-/
#guard_msgs in
def badType : Nat
  | 0 => 32

/--
error: too many patterns in match alternative: at most 2 patterns expected in a definition of type ⏎
  Foo → Foo → Prop
but found 3:
  f₁, f₂, f₃
-/
#guard_msgs in
def tooMany₁ : Foo → Foo → Prop
  | f₁, f₂, f₃ => True

/--
error: too many patterns in match alternative: at most 2 patterns expected in a definition of type ⏎
  Foo → Foo → Prop
but found 3:
  .foo, .foo, f
-/
#guard_msgs in
def tooMany₂ : Foo → Foo → Prop
  | .foo, .foo, f => True
  | .foo, .foo2 => True

/--
error: inconsistent number of patterns in match alternatives: this alternative contains 3 patterns:
  .foo, .foo, f
but a preceding alternative contains 2:
  .foo, .foo2
-/
#guard_msgs in
def tooMany₃ : Foo → Foo → Prop
  | .foo, .foo2 => True
  | .foo, .foo, f => True

/--
error: type mismatch
  True
has type
  Prop : Type
but is expected to have type
  Foo → Prop : Type
-/
#guard_msgs in
def tooFew₁ : Foo → Foo → Prop
  | _ => True

/--
error: inconsistent number of patterns in match alternatives: this alternative contains 2 patterns:
  .foo, .foo2
but a preceding alternative contains 1:
  .foo
-/
#guard_msgs in
def tooFew₂ : Foo → Foo → Prop
  | .foo => False
  | .foo, .foo2 => True

/--
error: inconsistent number of patterns in match alternatives: this alternative contains 1 pattern:
  _
but a preceding alternative contains 2:
  .foo, .foo
-/
#guard_msgs in
def tooFew₃ : Foo → Foo → Prop
  | .foo, .foo => True
  | _ => False

/--
error: inconsistent number of patterns in match alternatives: this alternative contains 1 pattern:
  _
but a preceding alternative contains 2:
  .foo, .foo
-/
#guard_msgs in
def tooFewFn : Foo → Foo → Prop
  | .foo, .foo => True
  | _ => fun f => True

def TyVal := Nat → String → Nat

def withTyValOK : TyVal
  | x, _ => x

/--
error: too many patterns in match alternative: at most 2 patterns expected in a definition of type ⏎
  TyVal
but found 3:
  x, y, z
-/
#guard_msgs in
def withTyValTooMany : TyVal
  | x, y, z =>
    let x := 34
    toString x ++ y ++ z

/--
error: inconsistent number of patterns in match alternatives: this alternative contains 1 pattern:
  _
but a preceding alternative contains 2:
  Nat.zero, ""
-/
#guard_msgs in
def noType
  | Nat.zero, "" => true
  | _ => false

/--
error: too many patterns in match alternative: expected 1, but found 2:
  .foo, .foo
-/
#guard_msgs in
def matchTooMany₁ (f : Foo) : Nat :=
  match f with
  | .foo, .foo => 32
  | _ => 41

/--
error: too many patterns in match alternative: expected 1, but found 2:
  .foo2, .foo2
-/
#guard_msgs in
def matchTooMany₂ (f : Foo) : Nat :=
  match f with
  | .foo => 41
  | .foo2, .foo2 => 32

/--
error: not enough patterns in match alternative: expected 2, but found 1:
  .foo
---
error: missing cases:
Foo.foo2, Foo.foo
-/
#guard_msgs in
def matchTooFew₁ (f : Foo) : Nat :=
  match f, f with
  | .foo => 41
  | .foo2, .foo2 => 32

/--
error: not enough patterns in match alternative: expected 2, but found 1:
  .foo
---
error: missing cases:
Foo.foo2, Foo.foo
-/
#guard_msgs in
def matchTooFew₂ (f : Foo) : Nat :=
  match f, f with
  | .foo2, .foo2 => 32
  | .foo => 41

/--
error: not enough patterns in match alternative: expected 2, but found 1:
  .(_)
---
error: type mismatch
  fun b => True
has type
  ?m.857 → Prop : Sort (max 1 ?u.856)
but is expected to have type
  Prop : Type
-/
#guard_msgs in
def matchTooFewFn : Foo → Foo → Prop :=
  λ a b =>
  match a, b with
  | _ => fun b => True

/--
error: missing cases:
Foo.foo2, Foo.foo
Foo.foo, Foo.foo2
-/
#guard_msgs in
def matchMissing : Foo → Foo → Prop :=
  λ a b => match a, b with
  | .foo, .foo => True
  | .foo2, .foo2 => True

/-- error: alternative 'foo2' has not been provided -/
#guard_msgs in
theorem induction_missing : Foo → Foo → True :=
  λ a b => by
  induction a with
  | foo => trivial

/-- error: alternative 'foo2' has not been provided -/
#guard_msgs in
theorem cases_missing : Foo → Foo → True :=
  λ a b => by
  cases a with
  | foo => trivial

inductive Three
  | one | two | three

/--
error: alternative 'two' has not been provided
---
error: alternative 'three' has not been provided
-/
#guard_msgs in
theorem induction_missing_multiple (t : Three) : True := by
  induction t with
  | one => trivial

/--
error: alternative 'two' has not been provided
---
error: alternative 'three' has not been provided
-/
#guard_msgs in
theorem cases_missing_multiple (t : Three) : True := by
  cases t with
  | one => trivial

def f x :=
  match x with
  | [] => 0
  | _ :: xs => 1 + f xs

def List.empty : List α → Bool
  | nil => true
  | cons x (q := 43) => false

inductive T where
| mk (k : Nat)


def List.empty' : List α → Bool
  | .nil => true
  | .cons => false

def foo (T : Type) (P : Prop) :=
  match (motive := Type → Prop → Bool) T, P with
  | Nat, True => true
  | _, _ => false

-- TODO: fix "invalid pattern" when using `@ctor` (e.g., `@nil`)
example := match [] with
  | @List.cons α x xs => True
  | @nil => false
