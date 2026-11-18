module

/-!
Equation lemmas of a definition with an exposed body that mentions a private auxiliary proof.

The `variable` binder `x` contains a `by decide` proof, which becomes a private auxiliary
declaration of the module. The body of `f` reuses that proof, while the equation lemmas of `f`
are public.
-/

@[expose] public section

def bounded (n : Nat) (_ : n ≤ 2) : Nat := n

variable (x : Fin (bounded 1 (by decide) + 1))

def f (b : Bool) : Nat :=
  match b with
  | true => bounded 1 (by decide) + x.val
  | false => 0

theorem f_false : f x false = 0 := by simp [f]

end
