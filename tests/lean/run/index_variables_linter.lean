set_option linter.indexVariables true

#guard_msgs in
example (xs : List Nat) (i : Nat) (h) : xs[i] = xs[i] := rfl

/--
warning: Forbidden variable appearing as an index: use `i`, `j`, or `k`: m
note: this linter can be disabled with `set_option linter.indexVariables false`
---
warning: Forbidden variable appearing as an index: use `i`, `j`, or `k`: m
note: this linter can be disabled with `set_option linter.indexVariables false`
-/
#guard_msgs in
example (xs : List Nat) (m : Nat) (h) : xs[m] = xs[m] := rfl

#guard_msgs in
example (xs : List Nat) (i j : Nat) (h) : xs[i + j] = xs[i + j] := rfl

#guard_msgs in
example (xs : List Nat) (m n : Nat) (h) : xs[m + n] = xs[m + n] := rfl

#guard_msgs in
example (xs : List Nat) (i : Nat) : xs[i]? = xs[i]? := rfl

/--
warning: Forbidden variable appearing as an index: use `i`, `j`, or `k`: m
note: this linter can be disabled with `set_option linter.indexVariables false`
---
warning: Forbidden variable appearing as an index: use `i`, `j`, or `k`: m
note: this linter can be disabled with `set_option linter.indexVariables false`
-/
#guard_msgs in
example (xs : List Nat) (m : Nat) : xs[m]? = xs[m]? := rfl

#guard_msgs in
example (xs : List Nat) (i : Nat) : xs.take i = xs.take i := rfl

/--
warning: Forbidden variable appearing as an index: use `i`, `j`, or `k`: m
note: this linter can be disabled with `set_option linter.indexVariables false`
---
warning: Forbidden variable appearing as an index: use `i`, `j`, or `k`: m
note: this linter can be disabled with `set_option linter.indexVariables false`
-/
#guard_msgs in
example (xs : List Nat) (m : Nat) : xs.drop m = xs.drop m := rfl
