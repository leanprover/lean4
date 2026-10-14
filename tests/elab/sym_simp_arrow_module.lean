module

/-!
Regression test: `Sym.simp` rewrites a non-dependent arrow telescope by converting it to
`Lean.Arrow`, and the resulting proof bridges `p → q` and `Arrow p q` with `Eq.refl`.
In a `module`, that `Eq.refl` is only kernel-checkable if `Arrow` is exposed. Reported by
Sebastian Graf.
-/

example (x y : Nat) (p : Prop) (h : x = y → p) : x + 0 = y → p := by
  sym => simp [Nat.add_zero]; exact h

example (x y : Nat) (p q : Prop) (h : x = y → q → p) : x + 0 = y → q → p := by
  sym => simp [Nat.add_zero]; exact h

example (x y : Nat) (p : Prop) : x + 0 = y → True := by
  sym => simp [Nat.add_zero]

example (x : Nat) (p : Prop) : True → x + 0 = x := by
  sym => simp [Nat.add_zero]
