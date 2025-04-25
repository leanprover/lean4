import Lean.Linter.Sets

register_option linter.foo1 : Bool := { defValue := false }
register_option linter.foo2 : Bool := { defValue := false }
register_option linter.foo_true : Bool := { defValue := true }

register_linter_set linter.set.foo := linter.foo1 linter.foo2 linter.foo_true

register_option linter.bar : Bool := { defValue := false }
register_linter_set linter.set.bar := linter.bar
