class CommAddSemigroup (α : Type u) extends Add α where
    addComm : {a b : α} → a + b = b + a
    addAssoc : {a b c : α} → a + b + c = a + (b + c)

open CommAddSemigroup

theorem addComm3 [CommAddSemigroup α] {a b c : α} : a + b + c = a + c + b := by {
    have h : b + c = c + b := addComm;
    have h' := congrArg (a + ·) h;
    simp at h';
    rw [←addAssoc] at h';
    rw [←addAssoc (a := a)] at h';
    exact h';
}

theorem addComm4 [CommAddSemigroup α] {a b c : α} : a + b + c = a + c + b := by {
    rw [addAssoc, addAssoc];
    rw [addComm (a := b)];
}

theorem addComm5 [CommAddSemigroup α] {a b c : α} : a + b + c = a + c + b := by {
    have h : b + c = c + b := addComm;
    have h' := congrArg (a + ·) h;
    simp at h';
    rw [←addAssoc] at h';
    rw [←addAssoc (a := a)] at h';
    exact h';
}

theorem addComm6 [CommAddSemigroup α] {a b c : α} : a + b + c = a + c + b := by {
    have h : b + c = c + b := addComm;
    have h' := congrArg (a + ·) h;
    simp at h';
    rw [←addAssoc] at h';
    rw [←addAssoc] at h';
    exact h';
}
