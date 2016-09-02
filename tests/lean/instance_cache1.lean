set_option new_elaborator true

definition f (A : Type) (a : A) :=
have has_add A, from has_add.mk (λ (a b : A), a),
a + a

definition f (A : Type) (a : A) : has_add A → A :=
λ s, a + a

definition f (A : Type) (a : A) :=
λ s : has_add A, a + a

definition f (A : Type) [has_add A] (a : A) :=
a + a

definition g (A : Type) (s : has_add A) (a : A) :=
a + a
