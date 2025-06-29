import Lean.Linter.Sets

register_option linter.foo1 : Bool := { defValue := false }
register_option linter.foo2 : Bool := { defValue := false }
register_option linter.foo_true : Bool := { defValue := true }

register_linter_set linter.set.foo := linter.foo1 linter.foo2 linter.foo_true

-- Note that we can register linter sets before their contents. Useful for `Init.lean`-style files.
register_linter_set linter.set.bar := linter.bar

register_option linter.bar : Bool := { defValue := false }
