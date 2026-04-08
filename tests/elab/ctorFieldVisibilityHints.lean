module
/-!
# Visibility hints for fields and constructors

This test assess error message hints for fields and constructors with invalid visibilities where the
necessary correction is reasonably unambiguous.
-/

/--
error: Constructor must be `private` because one or more of this structure's fields are `private`

Hint: Mark constructor as `private`
  p̲r̲i̲v̲a̲t̲e̲ ̲protected mk ::
-/
#guard_msgs in
structure Foo where
  protected mk ::
  private foo : Nat

/--
error: Constructor must be `private` because one or more of this structure's fields are `private`

Hint: Mark constructor as `private`
  p̲r̲i̲v̲a̲t̲e̲ ̲mk ::
-/
#guard_msgs in
structure Foo where
  /-- doc -/
  mk ::
  private foo : Nat

/--
error: Constructor must be `private` because one or more of this structure's fields are `private`

Hint: Mark constructor as `private`
  p̲r̲i̲v̲a̲t̲e̲ ̲mk ::
-/
#guard_msgs in
structure Foo where
  mk ::
  private foo : Nat

/--
error: Field cannot be marked `private` because it is already in a `private` structure

Hint: Remove `private` modifier from field
  p̵r̵i̵v̵a̵t̵e̵ ̵bar : Nat
-/
#guard_msgs in
private structure Bar where
  private bar : Nat

/--
error: Constructor cannot be marked `private` because it is already in a `private` structure

Hint: Remove `private` modifier from constructor
  p̵r̵i̵v̵a̵t̵e̵ ̵mk ::
-/
#guard_msgs in
private structure Bar' where
  /-- doc -/
  private mk ::
  bar' : Nat

/--
error: Duplicate doc string
---
error: Constructor cannot be marked `private` because it is already in a `private` inductive datatype

Hint: Remove `private` modifier from constructor
  p̵r̵i̵v̵a̵t̵e̵ ̵baz
-/
#guard_msgs in
private inductive Baz where
  /-- doc -/ | /-- doc -/ private baz (x : Nat) : Baz
