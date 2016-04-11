lemma eq_rect (A : Type) (x : A) (P : A → Type) (f : P x) (y : A) (e : x = y) : P y :=
  @@eq.rec_on (λ (y : A), P y) e f
