/-!
`decide` on bounded quantifiers must not need more recursion depth per element than before
#15371. Checking whether the major premise of `Decidable.rec` is a proof used to infer the type of
the unreduced instance, which gains a β-redex at every step of `Nat.decidableBallLT`. At the
deepest step, that inference added depth proportional to the bound.
-/

example : ∀ i, i < 100 → i + 0 = i := by decide

example : ∀ i : Fin 100, i.val + 0 = i.val := by decide

-- Before #15371, the default `maxRecDepth` sufficed up to a bound of 165.
example : ∀ i, i < 150 → i + 0 = i := by decide
