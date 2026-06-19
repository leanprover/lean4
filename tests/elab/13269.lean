set_option linter.unusedVariables true

class Foo

def bar [Foo] := 0

/--
warning: Variable name `x` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
def baz := let x := Foo.mk; bar -- unused variable `x`

/--
error: failed to synthesize instance of type class
  Foo

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def baz':=                  bar -- failed to synthesize instance of type class Foo
