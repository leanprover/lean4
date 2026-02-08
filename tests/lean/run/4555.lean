import Lean.Exception
/-!
# In pattern, `..` shouldn't make use of opt-params

https://github.com/leanprover/lean4/issues/4555
-/

open Lean

/-!
The `.internal` constructor has an opt-param, which caused this to be a non-exhaustive match.
-/
example (e : Exception) : Nat :=
  match e with
  | .internal .. => 0
  | .error .. => 1
