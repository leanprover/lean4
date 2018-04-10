definition f1 (A : Type*) (a : A) :=
have has_add A, from has_add.mk (λ (a b : A), a),
a + a

definition f2 (A : Type*) (a : A) : has_add A → A :=
λ s, a + a

definition f3 (A : Type*) (a : A) :=
λ s : has_add A, a + a

definition f4 (A : Type*) [has_add A] (a : A) :=
a + a

definition g (A : Type*) (s : has_add A) (a : A) :=
a + a
