theorem unused_intro: (n m: Nat) -> (m >= 0) :=
  by
    intro _ m; simp

theorem unused_intros: (n m: Nat) -> (m >= 0) :=
  by
    intros _ m; simp

theorem unused_intro': (n m: Nat) -> (m >= 0) :=
  by
    intro _ _; simp

theorem unused_intros': (n m: Nat) -> (m >= 0) :=
  by
    intros; simp
