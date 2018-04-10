constant Foo : ((Σu:nat, nat) → nat) → Prop
constant Foo2 : ((Σu:nat, nat) → nat) → Prop

noncomputable instance : decidable (Foo (λ ⟨a, b⟩, a)) := -- ERROR
sorry

instance I1 : decidable (Foo (λ ⟨a, b⟩, a)) :=
sorry

instance I2 : decidable (Foo2 (λ ⟨a, b⟩, a)) :=
sorry

def test (f : ((Σu:nat, nat) → nat) → nat) : f (λ ⟨a, b⟩, a) = f (λ⟨a, b⟩, a) :=
eq.refl (f ((λ ⟨a, b⟩, a : (Σu:nat, nat) → nat)))
