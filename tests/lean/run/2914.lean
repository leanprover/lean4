/-
The DecidableEq deriving handler should succeed even if fields have types starting with implicit arguments.
-/

structure Foo where
  a : List Nat
  ha : ∀ {i}, i ∈ a → 0 < i
deriving DecidableEq
