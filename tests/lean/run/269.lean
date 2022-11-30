theorem have_with_subgoals {a b : α} : a = b ↔ b = a := by
    apply Iff.intro
    intro h
    have h' := h.symm
    exact h'
    intro h
    exact h.symm

theorem have_with_subgoals2 {a b : α} : a = b ↔ b = a := by {
    apply Iff.intro;
    intro h;
    have h' := h.symm;
    exact h';
    intro h; exact h.symm;
}
