set_option linter.listVariable true

#guard_msgs in
example (l : List Nat) : l = l := rfl

#guard_msgs in
example (l' : List Nat) : l' = l' := rfl

#guard_msgs in
example (l₁ : List Nat) : l₁ = l₁ := rfl

#guard_msgs in
example (l₂ : List Nat) : l₂ = l₂ := rfl

/--
warning: Forbidden variable appearing as a `List` name: l₄
note: this linter can be disabled with `set_option linter.listVariable false`
---
warning: Forbidden variable appearing as a `List` name: l₄
note: this linter can be disabled with `set_option linter.listVariable false`
-/
#guard_msgs in
example (l₄ : List Nat) : l₄ = l₄ := rfl

#guard_msgs in
example (xs : List Nat) : xs = xs := rfl

/--
warning: Forbidden variable appearing as a `List` name: ps
note: this linter can be disabled with `set_option linter.listVariable false`
---
warning: Forbidden variable appearing as a `List` name: ps
note: this linter can be disabled with `set_option linter.listVariable false`
-/
#guard_msgs in
example (ps : List Nat) : ps = ps := rfl

/--
warning: Forbidden variable appearing as a `Array` name: l
note: this linter can be disabled with `set_option linter.listVariable false`
---
warning: Forbidden variable appearing as a `Array` name: l
note: this linter can be disabled with `set_option linter.listVariable false`
-/
#guard_msgs in
example (l : Array Nat) : l = l := rfl
