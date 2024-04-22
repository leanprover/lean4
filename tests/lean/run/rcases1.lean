example (x : α × β × γ) : True := by
  rcases x with ⟨a, b, c⟩
  trivial

example (x : α × β × γ) : True := by
  rcases x with ⟨(a : α) : id α, -, c : id γ⟩
  fail_if_success have : β := by assumption
  trivial

example (x : (α × β) × γ) : True := by
  fail_if_success rcases x with ⟨_a, b, c⟩
  fail_if_success rcases x with ⟨⟨a:β, b⟩, c⟩
  rcases x with ⟨⟨a:α, b⟩, c⟩
  trivial

example : @Inhabited.{1} α × Option β ⊕ γ → True := by
  rintro (⟨⟨a⟩, _ | b⟩ | c)
  · trivial
  · trivial
  · trivial

example : cond false Nat Int → cond true Int Nat → Nat ⊕ Unit → True := by
  rintro (x y : Int) (z | u)
  · trivial
  · trivial

example (h : x = 3) (h₂ : x < 4) : x < 4 := by
  rcases h with ⟨⟩
  exact h₂

example : True := by
  obtain (h : True) | ⟨⟨⟩⟩ : True ∨ False
  · exact Or.inl trivial
  trivial

example : True := by
  obtain h | ⟨⟨⟩⟩ : True ∨ False := Or.inl trivial
  trivial

example : True := by
  obtain ⟨h, h2⟩ := And.intro trivial trivial
  trivial

example : True := by
  fail_if_success obtain ⟨h, h2⟩
  trivial

example (x y : α × β) : True := by
  rcases x, y with ⟨⟨a, b⟩, c, d⟩
  trivial

example (x y : α ⊕ β) : True := by
  rcases x, y with ⟨a|b, c|d⟩
  repeat trivial

example (i j : Nat) : (Σ' x, i ≤ x ∧ x ≤ j) → i ≤ j := by
  intro h
  rcases h' : h with ⟨x, h₀, h₁⟩
  apply Nat.le_trans h₀ h₁

example (x : Quot fun _ _ : α => True) (h : x = x): x = x := by
  rcases x with ⟨z⟩
  exact h

example (n : Nat) : True := by
  obtain _one_lt_n | _n_le_one : 1 < n + 1 ∨ n + 1 ≤ 1 := Nat.lt_or_ge 1 (n + 1)
  {trivial}; trivial

example (n : Nat) : True := by
  obtain _one_lt_n | (_n_le_one : n + 1 ≤ 1) := Nat.lt_or_ge 1 (n + 1)
  {trivial}; trivial
