inductive imf {A B : Type} (f : A → B) : B → Type
| mk : ∀ (a : A), imf (f a)

definition g {A B : Type} {f : A → B} : ∀ {b : B}, imf f b → A
| .(f a) (imf.mk .(f) a)  := a

example {A B : Type} (f : A → B) (a : A) : g (imf.mk f a) = a :=
rfl

definition v₁ : imf nat.succ 1 :=
(imf.mk nat.succ 0)

definition v₂ : imf (λ x, 1 + x) 1 :=
(imf.mk (λ x, 1 + x) 0)

example : g v₁ = 0 :=
rfl

example : g v₂ = 0 :=
rfl

lemma ex1 (A : Type) : ∀ (a b : A) (H : a = b), b = a
| a .(a) rfl := rfl

lemma ex2 (A : Type) : ∀ a b : A, a = b → b = a
| a .(a) (eq.refl .(a)) := rfl

lemma ex3 (A : Type) : ∀ a b : A, a = b → b = a
| a ._ (eq.refl ._) := rfl
