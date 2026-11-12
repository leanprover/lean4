/-!
Tests that `Sym` unification performs the occurs check when assigning a metavariable.
`?n =?= ?n * ?n` used to assign `?n := ?n * ?n`, and `sym` would loop.
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
example : ∃ n : Nat, n * n = n := by
  sym =>
    apply Exists.intro
    apply Eq.refl

-- The metavariable occurs in the value only after instantiating `?n := ?m`.
/--
error: `apply` failed, rule is not applicable
-/
#guard_msgs in
example : ∃ n m : Nat, n = m ∧ m = n * n := by
  sym =>
    apply Exists.intro
    apply Exists.intro
    apply And.intro
    apply Eq.refl
    apply Eq.refl

-- The metavariable is applied to a bound variable.
/--
error: `apply` failed, rule is not applicable
-/
#guard_msgs in
example : ∃ f : Nat → Nat, (fun x => f x) = (fun x => f x + 1) := by
  sym =>
    apply Exists.intro
    apply Eq.refl

-- The occurs check must not block assignments whose value contains other metavariables.
example : ∃ n m : Nat, n = m * m := by
  sym =>
    apply Exists.intro
    apply Exists.intro
    apply Eq.refl
    exact 2

opaque P : (Nat → Nat) → (Nat → Nat) → Prop
opaque F : Nat → Nat
opaque G : Nat → Nat
opaque H : Nat → Nat
axiom pIntro (q : Nat → Nat) : P (fun a => F (q a)) (fun a => H (q a))

-- The value assigned to the pattern variable `q` contains an older metavariable.
example : ∃ n : Nat, P (fun a => F (a + n)) (fun a => H (a + n)) := by
  sym =>
    apply Exists.intro
    apply pIntro
    exact 0

-- `?r := fun a => F (?q a)` is assigned first, and then `?q a =?= G (?r a)` must fail: `?q` occurs
-- in the value of `?r`.
/--
error: `apply` failed, rule is not applicable
-/
#guard_msgs in
example : ∃ r : Nat → Nat, P r (fun a => H (G (r a))) := by
  sym =>
    apply Exists.intro
    apply pIntro
