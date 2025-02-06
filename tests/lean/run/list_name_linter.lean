set_option linter.listName true

#guard_msgs in
example (l : List Nat) : l = l := rfl

#guard_msgs in
example (l' : List Nat) : l' = l' := rfl

#guard_msgs in
example (l₁ : List Nat) : l₁ = l₁ := rfl

#guard_msgs in
example (l₂ : List Nat) : l₂ = l₂ := rfl

/--
warning: Forbidden variable appearing as a `List` name: use `l` instead of l₃
note: this linter can be disabled with `set_option linter.listName false`
---
warning: Forbidden variable appearing as a `List` name: use `l` instead of l₃
note: this linter can be disabled with `set_option linter.listName false`
-/
#guard_msgs in
example (l₃ : List Nat) : l₃ = l₃ := rfl

#guard_msgs in
example (xs : List Nat) : xs = xs := rfl

/--
warning: Forbidden variable appearing as a `List` name: use `l` instead of ps
note: this linter can be disabled with `set_option linter.listName false`
---
warning: Forbidden variable appearing as a `List` name: use `l` instead of ps
note: this linter can be disabled with `set_option linter.listName false`
-/
#guard_msgs in
example (ps : List Nat) : ps = ps := rfl

/--
warning: Forbidden variable appearing as a `Array` name: use `l` instead of l
note: this linter can be disabled with `set_option linter.listName false`
---
warning: Forbidden variable appearing as a `Array` name: use `l` instead of l
note: this linter can be disabled with `set_option linter.listName false`
-/
#guard_msgs in
example (l : Array Nat) : l = l := rfl
