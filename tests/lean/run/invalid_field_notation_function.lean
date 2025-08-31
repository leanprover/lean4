/-!
# Invalid field notation on expressions of function type

Ensure we produce correct field notation error messages for expressions of function type and not the
fallback "type is not of the form `C ...`" message.
-/

set_option pp.mvars false

def foo : α → α := id

/-- error: Unknown constant `foo.bar` -/
#guard_msgs in
example := foo.bar

/--
error: Invalid field `foo`: The environment does not contain `Function.foo`
  fun x => x
has type
  ?_ → ?_
-/
#guard_msgs in
example (f : α → α) := (fun x => x).foo

/--
error: Invalid field `foo`: The environment does not contain `Function.foo`
  f
has type
  α → α
-/
#guard_msgs in
example (f : α → α) := f.foo

/--
error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  f x
has type
  α
-/
#guard_msgs in
example (f : α → α) (x : α) := (f x).foo

/--
error: Invalid field `foo`: The environment does not contain `Function.foo`
  f x
has type
  α → α
-/
#guard_msgs in
example (f : α → α → α) (x : α) := (f x).foo

/--
error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  foo x
has type
  α
-/
#guard_msgs in
example (x : α) := (foo x).foo

def foo.bar := 32

/--
error: Invalid field `bar`: The environment does not contain `Function.bar`
  foo
has type
  α → α
-/
#guard_msgs in
example (foo : α → α) := foo.bar

/--
error: Invalid field `foo`: The environment does not contain `Function.foo`
  let x := id;
  x
has type
  ?_ → ?_
-/
#guard_msgs in
example := (let x := id; x).foo

/--
error: Invalid field `foo`: The environment does not contain `Function.foo`
  ?_
has type
  α → α
-/
#guard_msgs in
example {α} := (by intro h; exact h : α → α).foo

/-! Make sure we're not overzealously detecting fvars or implicitly-parameterized values in function position -/
/--
error: Invalid field `foo`: The environment does not contain `Nat.foo`
  n
has type
  Nat
-/
#guard_msgs in
example (n : Nat) := n.foo

/--
error: Invalid field `foo`: The environment does not contain `List.foo`
  []
has type
  List Nat
-/
#guard_msgs in
example (n : Nat) := (@List.nil Nat).foo
