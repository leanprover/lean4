example (p q r s: Prop) (h1: p -> s) (h2: q -> s) (h3: r -> s)
    : ((p \/ q) -> s) /\ (r -> s) := by {
  constructor <;> intro h <;>
  (try (apply Or.elim h <;> intro h)) <;>
  revert h <;> assumption;
}

example (p q r s: Prop) (h1: p -> s) (h2: q -> s) (h3: r -> s)
    : ((p \/ q) -> s) /\ (r -> s) := by {
  constructor <;> intro h <;>
  (try (apply h.elim <;> intro h)) <;>
  revert h <;> assumption;
}

/-!
Verify that `withoutRecover` is not necessary for `apply`.
This is because `first` enables it itself.
-/
example (p : Prop) (h : p) : p := by
  first | apply bogusTerm | assumption
