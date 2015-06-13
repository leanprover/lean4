open equiv

constants (A B : Type₀) (f : A → B) (g : B → A) (p : Πb, f (g b) = b) (q : Πa, g (f a) = a)

definition e [constructor] : A ≃ B :=
equiv.MK f g p q

example (b : B) : g (f (g b)) = g b :=
by rewrite [to_right_inv e b]

example (b : B) : g (f (g b)) = g b :=
by xrewrite [to_right_inv e b]

example (b : B) : g (f (g b)) = g b :=
by krewrite [to_right_inv e b]

example (b : B) : g (f (g b)) = g b :=
begin
  let H := to_right_inv e b,
  esimp at H,
  rewrite H
end
