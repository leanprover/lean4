theorem ex1 (p q : Prop) : p → q → p ∧ q := by
  intros
  apply And.intro
  exact ‹p›
  exact ‹q›

theorem ex2 (p q : Prop) : p → q → p ∧ q :=
  fun _ _ => And.intro ‹p› ‹q›

theorem ex3 (p q : Prop) : p → q → p ∧ q :=
  fun _ _ => ⟨‹p›, ‹q›⟩

theorem ex4 {a b c : Nat} : a = b → b = c → a = c :=
  fun _ _ => Eq.trans ‹a = _› ‹_ = c›
