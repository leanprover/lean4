

macro "obtain " p:term " from " d:term "; " body:term : term =>
`(match $d:term with | $p:term => $body:term)

theorem tst1 {p q r} (h : p ∧ q ∧ r) : q ∧ p ∧ r :=
match h with
| ⟨h₁, ⟨h₂, h₃⟩⟩ => ⟨h₂, ⟨h₁, h₃⟩⟩

theorem tst2 {p q r} (h : p ∧ q ∧ r) : q ∧ p ∧ r :=
obtain ⟨h₁, ⟨h₂, h₃⟩⟩ from h;
⟨h₂, ⟨h₁, h₃⟩⟩

macro "obtain " p:term " from " d:term : tactic =>
`(tactic| match $d:term with | $p:term => ?hole)

theorem tst3 {p q r} (h : p ∧ q ∧ r) : q ∧ p ∧ r := by
  obtain ⟨h₁, ⟨h₂, h₃⟩⟩ from h
  apply And.intro
  assumption
  apply And.intro
  assumption
  assumption
