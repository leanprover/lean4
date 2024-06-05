example {A B : Prop} {p : Prop} [Decidable p] (h : if p then A else B) :
   A ∨ B := by
  split at h
  · exact .inl h
  · exact .inr h

example {A B : Type} {p : Prop} [Decidable p] (h : if p then A else B) :
    Sum A B := by
  split at h
  · exact .inl h
  · exact .inr h

example {A B : Type} (h : match b with | true => A | false => B) :
    Sum A B := by
  split at h
  · exact .inl h
  · exact .inr h

open Int in
theorem bmod_add_bmod_congr : Int.bmod (Int.bmod x n + y) n = Int.bmod (x + y) n := by
  rw [bmod_def x n]
  split -- `split` now generates the more meaningful `isTrue` and `isFalse` tags.
  case isTrue p =>
    simp only [emod_add_bmod_congr]
  case isFalse p =>
    rw [Int.sub_eq_add_neg, Int.add_right_comm, ←Int.sub_eq_add_neg]
    simp
