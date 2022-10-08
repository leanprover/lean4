theorem not_mem_nil (a : Nat) : ¬ a ∈ [] := fun x => nomatch x

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬ p) :
  (∀ h' : p, q h') ↔ True := sorry

example (R : Nat → Prop) : (∀ (a' : Nat), a' ∈ [] → R a') := by
  simp only [forall_prop_of_false (not_mem_nil _)]
  exact fun _ => True.intro


def Not.elim {α : Sort _} (H1 : ¬a) (H2 : a) : α := absurd H2 H1
theorem iff_of_true (ha : a) (hb : b) : a ↔ b := ⟨fun _ => hb, fun _ => ha⟩
theorem iff_true_intro (h : a) : a ↔ True := iff_of_true h ⟨⟩

example {P : Prop} : ∀ (x : Nat) (_ : x ∈ []), P :=
by
  simp only [forall_prop_of_false (not_mem_nil _)]
  exact fun _ => True.intro
