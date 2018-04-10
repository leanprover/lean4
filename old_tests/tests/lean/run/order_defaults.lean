example : preorder unit := {
    le := λ _ _, true,
    le_refl := λ _, trivial,
    le_trans := λ _ _ _ _ _, trivial,
}

example : partial_order unit := {
    le := λ _ _, true,
    le_refl := λ _, trivial,
    le_trans := λ _ _ _ _ _, trivial,
    le_antisymm := by intros a b; intros; cases a; cases b; refl
}

example : linear_order unit := {
    le := λ _ _, true,
    le_refl := λ _, trivial,
    le_trans := λ _ _ _ _ _, trivial,
    le_antisymm := by intros a b; intros; cases a; cases b; refl,
    le_total := λ _ _, or.inl trivial,
}
