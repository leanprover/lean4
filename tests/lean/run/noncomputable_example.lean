open classical sum
universe variable u
noncomputable example (A : Type u) (h : (A → empty) → false) : A :=
match type_decidable A with
| (inl ha) := ha
| (inr hna) := false.rec _ (h hna)
end
