/-!
Local E-matching theorems must use the preprocessed type of the hypothesis. Unfolding `≠` does not
produce a proof term, so the theorem for `h` used to be built from the original type `∀ x y, x ≠ y`,
and with the `Sym.simp` normalizer the instance `c ≠ c` was normalized to `¬c = c` instead of `False`.
-/

set_option backward.grind.normalizer false

/--
trace: [grind.assert] ∀ (x y : α), ¬x = y
[grind.assert] False
-/
#guard_msgs in
example {α} (c : α) (h : ∀ x y : α, x ≠ y) : False := by
  have : c ≠ c := h c c
  set_option trace.grind.assert true in
  grind
