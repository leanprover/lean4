open nat

def below (n : nat) : nat → Prop :=
λ i, i < n

def f {n : nat} (v : subtype (below n)) : nat :=
v + 1

universe variable u

instance pred2subtype {A : Type u} : has_coe_to_sort (A → Prop) :=
⟨Type u, (λ p : A → Prop, subtype p)⟩

instance coesubtype {A : Type u} {p : A → Prop} : has_coe (@coe_sort _ pred2subtype p) A :=
⟨λ s, subtype.elt_of s⟩

def g {n : nat} (v : below n) : nat :=
v + 1

print g
