open tactic
meta def c := abstract `[assumption]

structure B (U : Type) :=
  (f : U → U)
  (w : ∀ u : U, f u = u . c)
