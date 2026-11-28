module

-- Macros apply in every scope, unlike declarations from non-`public` imports.
macro_rules | `($a + $b) => `(Nat.add $b $a)
