variables {a r : Type}

definition f a := Πr, (a -> r) -> r

lemma blah2 (sa : f a) (k : (a -> r)) :
  sa r k = sa r k :=
  sorry

lemma blah3 (sa : f a) (k : (a -> r)) :
  sa r k = sa r k :=
  rfl
