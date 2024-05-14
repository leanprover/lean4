axiom f : Nat → Nat
axiom g : Nat → Nat
axiom P : Nat → Prop
axiom a : Nat
axiom f_1 : f a = 42
axiom f_2 (x : Nat): f x = g x

-- non-confluent simp setup to see if the more specific lemma
-- is tried first

example (h : P 42): P (f a)  := by
  simp [f_1, f_2]
  exact h

example (h : P 42): P (f a)  := by
  simp [f_2, f_1]
  exact h
