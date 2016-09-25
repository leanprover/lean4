example : ∃ x : nat, x = x :=
Exists.intro 0 rfl

example : ∃ x : nat, x = x :=
exists.intro 0 rfl

lemma ex1 : ∃ x : nat, x = x :=
Exists.intro 0 rfl

lemma ex2 : ∃ x : nat, x = x :=
exists.intro 0 rfl

lemma ex3 : ∃ x y : nat, x = y :=
exists.intro 0 (exists.intro 0 rfl)

lemma ex4 : ∃ x y : nat, x = y + 1 :=
exists.intro 1 (exists.intro 0 rfl)

lemma ex5 : ∃ x y z : nat, x = y + z :=
exists.intro 1 (exists.intro 1 (exists.intro 0 rfl))

lemma ex6 : ∃ x : nat, x = x :=
⟨0, rfl⟩

lemma ex7 : ∃ x y z : nat, x = y + z :=
⟨1, 1, 0, rfl⟩

lemma ex8 : ∃ x y z : nat, x = y + z :=
(| 1, 1, 0, rfl |)

example : ∃ x : nat, x = x :=
⟨0, rfl⟩

example : ∃ x y z : nat, x = y + z :=
⟨1, 1, 0, rfl⟩
