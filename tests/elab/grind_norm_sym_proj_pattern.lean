/-!
E-matching patterns are normalized at attribute time, where the ambient transparency is
`.default`. The `Sym.simp`-based normalizer must still reduce a projection only when the
structure argument is a constructor application at `.reducible` transparency, like `simp`:
otherwise `(mkP n).a` unfolds `mkP` and the pattern collapses to the variable `n`
("invalid pattern, (non-forbidden) application expected").
-/

structure P where
  a : Nat
  b : Nat

def mkP (n : Nat) : P := ⟨n, n + 1⟩

set_option backward.grind.normalizer false

@[grind =] theorem mkP_a (n : Nat) : (mkP n).a = n := rfl
@[grind =] theorem mkP_b (n : Nat) : (mkP n).b = n + 1 := rfl

example (n : Nat) (h : (mkP n).a = 5) : n = 5 := by grind
example (n : Nat) : (mkP n).b = (mkP n).a + 1 := by grind
example (n : Nat) : (⟨n, n⟩ : P).a = n := by grind
