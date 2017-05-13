universe u
open classical psum

variables (A : Type u) (h : (A → false) → false)

-- both noncomputable example...
noncomputable example : A :=
match type_decidable A with
| (inl ha) := ha
| (inr hna) := false.rec _ (h hna)
end

-- ... and noncomputable theory should work
noncomputable theory
example : A :=
match type_decidable A with
| (inl ha) := ha
| (inr hna) := false.rec _ (h hna)
end