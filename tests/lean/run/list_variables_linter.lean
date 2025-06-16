set_option linter.listVariables true

#guard_msgs in
example (l : List Nat) : l = l := rfl

#guard_msgs in
example (l' : List Nat) : l' = l' := rfl

#guard_msgs in
example (l₁ : List Nat) : l₁ = l₁ := rfl

#guard_msgs in
example (l₂ : List Nat) : l₂ = l₂ := rfl

/--
warning: Forbidden variable appearing as a `List` name: l₅
note: this linter can be disabled with `set_option linter.listVariables false`
---
warning: Forbidden variable appearing as a `List` name: l₅
note: this linter can be disabled with `set_option linter.listVariables false`
-/
#guard_msgs in
example (l₅ : List Nat) : l₅ = l₅ := rfl

#guard_msgs in
example (xs : List Nat) : xs = xs := rfl

/--
warning: Forbidden variable appearing as a `List` name: ps
note: this linter can be disabled with `set_option linter.listVariables false`
---
warning: Forbidden variable appearing as a `List` name: ps
note: this linter can be disabled with `set_option linter.listVariables false`
-/
#guard_msgs in
example (ps : List Nat) : ps = ps := rfl

/--
warning: Forbidden variable appearing as a `Array` name: l
note: this linter can be disabled with `set_option linter.listVariables false`
---
warning: Forbidden variable appearing as a `Array` name: l
note: this linter can be disabled with `set_option linter.listVariables false`
-/
#guard_msgs in
example (l : Array Nat) : l = l := rfl
