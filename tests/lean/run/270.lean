class CommAddSemigroup (α : Type u) extends Add α where
    add_comm : {a b : α} → a + b = b + a
    add_assoc : {a b c : α} → a + b + c = a + (b + c)

open CommAddSemigroup

theorem add_comm3 [CommAddSemigroup α] {a b c : α} : a + b + c = a + c + b := by {
    have h : b + c = c + b := add_comm;
    have h' := congr_arg (a + ·) h;
    simp at h';
    rw [←add_assoc] at h';
    rw [←add_assoc (a := a)] at h';
    exact h';
}

theorem add_comm4 [CommAddSemigroup α] {a b c : α} : a + b + c = a + c + b := by {
    rw [add_assoc, add_assoc];
    rw [add_comm (a := b)];
}

theorem add_comm5 [CommAddSemigroup α] {a b c : α} : a + b + c = a + c + b := by {
    have h : b + c = c + b := add_comm;
    have h' := congr_arg (a + ·) h;
    simp at h';
    rw [←add_assoc] at h';
    rw [←@add_assoc (a := a)] at h';
    exact h';
}

theorem add_comm6 [CommAddSemigroup α] {a b c : α} : a + b + c = a + c + b := by {
    have h : b + c = c + b := add_comm;
    have h' := congr_arg (a + ·) h;
    simp at h';
    rw [←add_assoc] at h';
    rw [←add_assoc] at h';
    exact h';
}
