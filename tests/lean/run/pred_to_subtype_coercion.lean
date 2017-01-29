universe variables u

attribute [instance]
definition pred2subtype {A : Type u} : has_coe_to_sort (A → Prop) :=
⟨Type u, λ p : A → Prop, subtype p⟩

definition below (n : nat) : nat → Prop :=
λ i, i < n

check λ x : below 10, x

definition f : below 10 → nat
| ⟨a, h⟩ := a

lemma zlt10 : 0 < 10 :=
sorry

check f ⟨0, zlt10⟩

definition g (a : below 10) : nat :=
subtype.elt_of a
