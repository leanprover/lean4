set_option linter.unusedVariables true

/--
warning: This instance argument is unused.

The binding can be removed or given a `_`-prefixed name.

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example [Inhabited Nat] : 0 = 0 := rfl

def foo (α : Type) [Inhabited α] : α := default

/--
warning: This instance argument is unused.

The binding can be removed or given a `_`-prefixed name.

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
def foo' (α : Type) [Inhabited α] [Inhabited α] : α := default

section

variable {α : Type} [Inhabited α]

def bar : α := default
end
