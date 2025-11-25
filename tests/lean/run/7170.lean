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
error: Inconsistent number of patterns in match alternatives: This alternative contains 2 patterns:
  .foo2, x
but a preceding alternative contains 1:
  .foo
-/
#guard_msgs in
def patCountMismatch : Foo → Foo → Prop
  | .foo => fun _ => True
  | .foo2, x => False

/--
error: Cannot define a value of type
  Nat
by pattern matching because it is not a function type
-/
#guard_msgs in
def badType : Nat
  | 0 => 32

/--
error: Too many patterns in match alternative: At most 2 patterns expected in a definition of type ⏎
  Foo → Foo → Prop
but found 3:
  f₁, f₂, f₃
-/
#guard_msgs in
def tooMany₁ : Foo → Foo → Prop
  | f₁, f₂, f₃ => True

/--
error: Too many patterns in match alternative: At most 2 patterns expected in a definition of type ⏎
  Foo → Foo → Prop
but found 3:
  .foo, .foo, f
-/
#guard_msgs in
def tooMany₂ : Foo → Foo → Prop
  | .foo, .foo, f => True
  | .foo, .foo2 => True

/--
error: Inconsistent number of patterns in match alternatives: This alternative contains 3 patterns:
  .foo, .foo, f
but a preceding alternative contains 2:
  .foo, .foo2
-/
#guard_msgs in
def tooMany₃ : Foo → Foo → Prop
  | .foo, .foo2 => True
  | .foo, .foo, f => True

/--
error: Type mismatch
  True
has type
  Prop
but is expected to have type
  Foo → Prop
-/
#guard_msgs in
def tooFew₁ : Foo → Foo → Prop
  | _ => True

/--
error: Inconsistent number of patterns in match alternatives: This alternative contains 2 patterns:
  .foo, .foo2
but a preceding alternative contains 1:
  .foo
-/
#guard_msgs in
def tooFew₂ : Foo → Foo → Prop
  | .foo => False
  | .foo, .foo2 => True

/--
error: Inconsistent number of patterns in match alternatives: This alternative contains 1 pattern:
  _
but a preceding alternative contains 2:
  .foo, .foo
-/
#guard_msgs in
def tooFew₃ : Foo → Foo → Prop
  | .foo, .foo => True
  | _ => False

/--
error: Inconsistent number of patterns in match alternatives: This alternative contains 1 pattern:
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
error: Too many patterns in match alternative: At most 2 patterns expected in a definition of type ⏎
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
error: Inconsistent number of patterns in match alternatives: This alternative contains 1 pattern:
  _
but a preceding alternative contains 2:
  Nat.zero, ""
-/
#guard_msgs in
def noType
  | Nat.zero, "" => true
  | _ => false

/--
error: Too many patterns in match alternative: Expected 1, but found 2:
  .foo, .foo
-/
#guard_msgs in
def matchTooMany₁ (f : Foo) : Nat :=
  match f with
  | .foo, .foo => 32
  | _ => 41

/--
error: Too many patterns in match alternative: Expected 1, but found 2:
  .foo2, .foo2
-/
#guard_msgs in
def matchTooMany₂ (f : Foo) : Nat :=
  match f with
  | .foo => 41
  | .foo2, .foo2 => 32

/--
error: Not enough patterns in match alternative: Expected 2, but found 1:
  .foo
---
error: Missing cases:
Foo.foo2, Foo.foo
-/
#guard_msgs in
def matchTooFew₁ (f : Foo) : Nat :=
  match f, f with
  | .foo => 41
  | .foo2, .foo2 => 32

/--
error: Not enough patterns in match alternative: Expected 2, but found 1:
  .foo
---
error: Missing cases:
Foo.foo2, Foo.foo
-/
#guard_msgs in
def matchTooFew₂ (f : Foo) : Nat :=
  match f, f with
  | .foo2, .foo2 => 32
  | .foo => 41

set_option pp.mvars false in
/--
error: Not enough patterns in match alternative: Expected 2, but found 1:
  .(_)
---
error: Type mismatch
  fun b => True
has type
  ?_ → Prop
but is expected to have type
  Prop
-/
#guard_msgs in
def matchTooFewFn : Foo → Foo → Prop := fun a b =>
  match a, b with
  | _ => fun b => True

/--
error: Inconsistent number of patterns in match alternatives: This alternative contains 1 pattern:
  n + 1
but a preceding alternative contains 2:
  x, 0
-/
#guard_msgs in
def checkCounterexampleMsg : Nat → Nat → Nat
  | x, 0 => x
  | 0, n + 1 => n
  | n + 1 => 42
