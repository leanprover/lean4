inductive is_equiv [class] (A B : Type) (f : A → B) : Type
definition inverse (A B : Type) (f : A → B) [H : is_equiv A B f] := Type
definition foo (A : Type) (B : A → Type) (h : A → A) (g : Π(a : A), B a → B a)
               [H : Π(a : A), is_equiv _ _ (g a)] (x : A) : Type :=
inverse (B (h x)) (B (h x)) (g (h x))
