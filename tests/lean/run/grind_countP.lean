set_option grind.warning false
variable {α : Type u} {l : List α} {P Q : α → Bool}

attribute [grind] List.countP_nil List.countP_cons

theorem List.countP_le_countP (hpq : ∀ x ∈ l, P x → Q x) :
    l.countP P ≤ l.countP Q := by
  induction l with
  | nil => grind
  | cons x xs ih =>
    grind

theorem List.countP_lt_countP (hpq : ∀ x ∈ l, P x → Q x) (y:α) (hx: y ∈ l) (hxP : P y = false) (hxQ : Q y) :
    l.countP P < l.countP Q := by
  induction l with
  | nil => grind
  | cons x xs ih =>
    have : xs.countP P ≤ xs.countP Q := countP_le_countP (by grind)
    grind
