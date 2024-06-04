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
