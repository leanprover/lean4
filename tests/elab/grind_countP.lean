module
variable {α : Type u} {l : List α} {P Q : α → Bool}

attribute [grind =] List.countP_nil List.countP_cons

theorem List.countP_le_countP (hpq : ∀ x ∈ l, P x → Q x) :
    l.countP P ≤ l.countP Q := by
  induction l <;> grind

-- TODO: how to explain to the user that `l.countP P ≤ l.countP Q` is a bad pattern
grind_pattern List.countP_le_countP => l.countP P, l.countP Q

theorem List.countP_lt_countP (hpq : ∀ x ∈ l, P x → Q x) (y:α) (hx: y ∈ l) (hxP : P y = false) (hxQ : Q y) :
    l.countP P < l.countP Q := by
  induction l <;> grind

/--
info: List.countP_nil: [@List.countP #1 #0 (@List.nil _)]
---
info: List.countP_cons: [@List.countP #3 #2 (@List.cons _ #1 #0)]
-/
#guard_msgs (info) in
attribute [grind? =] List.countP_nil List.countP_cons
