/-!
`Sym.isDefEqS` must not assign `?m := s` when `?m` occurs in `s`.
-/

/--
error: `apply` failed, rule is not applicable
-/
#guard_msgs in
example : ∃ n : Nat, n = n * n := by
  sym =>
    apply Exists.intro
    apply Eq.refl

/--
error: `apply` failed, rule is not applicable
-/
#guard_msgs in
example : ∃ n : Nat, n = Nat.succ n := by
  sym =>
    apply Exists.intro
    apply Eq.refl

/--
error: `apply` failed, rule is not applicable
-/
#guard_msgs in
example : ∃ f : Nat → Nat, (fun a => f a) = (fun a => Nat.succ (f a)) := by
  sym =>
    apply Exists.intro
    apply Eq.refl

example : ∃ n : Nat, n * 2 = 3 * 2 := by
  sym =>
    apply Exists.intro
    apply Eq.refl

example : ∃ f : Nat → Nat, (fun a => f a) = (fun a => Nat.succ a) := by
  sym =>
    apply Exists.intro
    apply Eq.refl
