inductive Foo (α : Type) (x : α) where
| c1 : Foo α x
| c2 : Foo α x

def Foo.mk (n : Nat) : Foo (Fin (n + 1)) 0 :=
  match n with
  | .zero => .c1
  | .succ _ => .c1

def Foo.num {α : Type} {x : α} (f : Foo α x) : Nat :=
  0

/--
Issue #12140: `closeGoalWithValuesEq` must check that the two interpreted values
have the same type before calling `mkEqProof`. When equivalence classes contain
heterogeneous equalities (e.g., `0 : Fin 3` and `0 : Fin 2` merged via `HEq`),
`mkEqProof` would fail with an internal error.
-/
theorem foo (n : Nat) : (Foo.mk n).num = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    fail_if_success grind [Foo.mk]
    sorry
