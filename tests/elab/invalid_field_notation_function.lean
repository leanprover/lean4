/-!
# Invalid field notation on expressions of function type

Ensure we produce correct field notation error messages for expressions of function type and not the
fallback "type is not of the form `C ...`" message.
-/

set_option pp.mvars false

def foo : α → α := id

/--
@ +1:11...18
error: Unknown constant `foo.bar`
-/
#guard_msgs (positions := true) in
example := foo.bar

/--
error: Invalid field `foo`: The environment does not contain `Function.foo`, so it is not possible to project the field `foo` from an expression
  fun x => x
of type `?_ → ?_`
-/
#guard_msgs in
example (f : α → α) := (fun x => x).foo

/--
@ +1:25...28
error: Invalid field `foo`: The environment does not contain `Function.foo`, so it is not possible to project the field `foo` from an expression
  f
of type `α → α`
-/
#guard_msgs (positions := true) in
example (f : α → α) := f.foo

/--
@ +1:25...28
error: Invalid field `foo`: The environment does not contain `Function.foo`, so it is not possible to project the field `foo` from an expression
  f
of type `α → α`
-/
#guard_msgs (positions := true) in
example (f : α → α) := f.foo.bar

/--
error: Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  f x
has type `α` which does not have the necessary form.
-/
#guard_msgs in
example (f : α → α) (x : α) := (f x).foo

/--
error: Invalid field `foo`: The environment does not contain `Function.foo`, so it is not possible to project the field `foo` from an expression
  f x
of type `α → α`
-/
#guard_msgs in
example (f : α → α → α) (x : α) := (f x).foo

/--
error: Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  foo x
has type `α` which does not have the necessary form.
-/
#guard_msgs in
example (x : α) := (foo x).foo

def foo.bar := 32

/--
error: Invalid field `bar`: The environment does not contain `Function.bar`, so it is not possible to project the field `bar` from an expression
  foo
of type `α → α`
-/
#guard_msgs in
example (foo : α → α) := foo.bar

/--
error: Invalid field `foo`: The environment does not contain `Function.foo`, so it is not possible to project the field `foo` from an expression
  let x := id;
  x
of type `?_ → ?_`
-/
#guard_msgs in
example := (let x := id; x).foo

/--
error: Invalid field `foo`: The environment does not contain `Function.foo`, so it is not possible to project the field `foo` from an expression
  ?_
of type `α → α`
-/
#guard_msgs in
example {α} := (by intro h; exact h : α → α).foo

/-! Make sure we're not overzealously detecting fvars or implicitly-parameterized values in function position -/
/--
error: Invalid field `foo`: The environment does not contain `Nat.foo`, so it is not possible to project the field `foo` from an expression
  n
of type `Nat`
-/
#guard_msgs in
example (n : Nat) := n.foo

/--
error: Invalid field `foo`: The environment does not contain `List.foo`, so it is not possible to project the field `foo` from an expression
  []
of type `List Nat`
-/
#guard_msgs in
example (n : Nat) := (@List.nil Nat).foo

#check Nat.add.uncurry
