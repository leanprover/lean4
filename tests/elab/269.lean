theorem haveWithSubgoals {a b : α} : a = b ↔ b = a := by
    apply Iff.intro
    intro h
    have h' := h.symm
    exact h'
    intro h
    exact h.symm

theorem haveWithSubgoals2 {a b : α} : a = b ↔ b = a := by {
    apply Iff.intro;
    intro h;
    have h' := h.symm;
    exact h';
    intro h; exact h.symm;
}
