open classical psum
universe variable u
noncomputable example (A : Type u) (h : (A → false) → false) : A :=
match type_decidable A with
| (inl ha) := ha
| (inr hna) := false.rec _ (h hna)
end
