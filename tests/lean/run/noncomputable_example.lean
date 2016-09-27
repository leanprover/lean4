open classical sum

noncomputable example (A : Type _) (h : (A → false) → false) : A :=
match type_decidable A with
| (inl ha) := ha
| (inr hna) := false.rec _ (h hna)
end
