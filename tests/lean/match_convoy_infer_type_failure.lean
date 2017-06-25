constant p : nat → Type
constant q : p 1 → Prop

lemma ex : ∀ a : p 1, q a :=
match q, p with
| q, p := sorry
end
