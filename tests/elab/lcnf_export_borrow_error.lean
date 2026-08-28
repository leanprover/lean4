module

/-! Assert that putting a borrow annotation on an export errors -/

/--
error:  Declaration bar is marked as `export` but some of its parameters have borrow annotations.
 Consider using `set_option compiler.ignoreBorrowAnnotation true in` to suppress the borrow annotations in its type.
 If the declaration is part of an `export`/`extern` pair make sure to also suppress the annotations at the `extern` declaration.
-/
#guard_msgs in
@[export foo]
public def bar (x : @& String) := x
