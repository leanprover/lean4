open tactic

meta def c : tactic unit :=
do l ← local_context,
   try_lst (l.map (λ h, cases h >> skip))

structure X (U : Type) :=
  (f : U → U)
  (w : ∀ u : U,  f u = u . c)
