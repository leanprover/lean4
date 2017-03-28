theorem ex {A : Type} : ∀ {a a' : A}, a == a' → a = a'
| a .(a) (heq.refl .(a)) := eq.refl a
