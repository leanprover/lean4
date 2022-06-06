inductive T: Type
| mk: Nat -> T

theorem T.zero_bad: T -> T
:= by {
  intro H;
  induction H with
  | mk _ => exact T.mk 0
}
