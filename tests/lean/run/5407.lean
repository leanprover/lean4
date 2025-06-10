/-!
# Suggestion tactics should not return invalid tactics

https://github.com/leanprover/lean4/issues/5407

The "suggestion" tactics `exact?`, `apply?`, `show_term`, and `rw?` should not suggest proof terms
that do not compile. They should use `expose_names` where possible to render suggestions valid. If
an invalid proof is generated, these tactics should instead provide users with appropriate feedback.
-/

/-! Discards unprintable implicit argument to lambda -/
inductive Odd : Nat → Prop
  | one : Odd 1
  | add_two : Odd n → Odd (n + 2)

theorem odd_iff {n : Nat} : Odd n ↔ n % 2 = 1 := by
  refine ⟨fun h => by induction h <;> omega, ?_⟩
  match n with
  | 0 => simp
  | 1 => exact fun _ => Odd.one
  | n + 2 => exact fun _ => Odd.add_two (odd_iff.mpr (by omega))

/--
error: found a proof, but the corresponding tactic failed:
  (expose_names; exact fun a => (fun {n} => odd_iff.mpr) a)

It may be possible to correct this proof by adding type annotations, explicitly specifying implicit arguments, or eliminating unnecessary function abstractions.
-/
#guard_msgs in
example {n : Nat} : n % 2 = 1 → Odd n :=
  by exact?


/-! Detects shadowed variables -/
opaque A : Type
opaque B : Type
opaque C : Prop
axiom imp : A → B → C
axiom a : A
axiom b : B
/-- info: Try this: (expose_names; exact imp h_1 h) -/
#guard_msgs in
example : C := by
  have h : A := a
  have h : B := b
  exact?


/-! Detects lambdas with insufficient explicit binder types -/
inductive EqExplicit {α} : α → α → Prop
  | intro : (a b : α) → a = b → EqExplicit a b
/--
error: found a proof, but the corresponding tactic failed:
  (expose_names; exact EqExplicit.intro (fun f => (fun g x => g x) f) id rfl)

It may be possible to correct this proof by adding type annotations, explicitly specifying implicit arguments, or eliminating unnecessary function abstractions.
-/
#guard_msgs in
example : EqExplicit (fun (f : α → β) => (fun g x => g x) f) id := by
  exact?


/-! Suggests `expose_names` if a name in the syntax contains macro scopes -/
/-- info: Try this: (expose_names; exact h) -/
#guard_msgs in
example {P : Prop} : P → P := by
  intro
  exact?


/-! Does *not* suggest `expose_names` when the inaccessible name is an implicit argument. -/
opaque D : Nat → Type
axiom c_of_d {n : Nat} : D n → C
/-- info: Try this: exact c_of_d x -/
#guard_msgs in
example : (n : Nat) → D n → C := by
  intro
  intro x
  exact?


/-! `apply?` logs info instead of erroring -/
opaque E : Prop
axiom option1 : A → E
axiom option2 {_ : B} : E
/--
info: Try this: refine option1 ?_
---
info: found a partial proof, but the corresponding tactic failed:
  (expose_names; refine option2)

It may be possible to correct this proof by adding type annotations, explicitly specifying implicit arguments, or eliminating unnecessary function abstractions.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : E := by apply?


/-!
This `apply?` erroneously reports a failure if suggesting tactics with dot-focusing notation instead
of parenthesized sequencing.
-/
opaque R : A → B → Prop
axiom rImp (b : B) : R a b → R a b
/--
info: Try this: (expose_names; refine rImp b ?_)
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : (b : B) → R a b := by
  intro
  apply?


/-! `show_term` exhibits the same behavior as `exact?` -/
/-- info: Try this: (expose_names; exact h) -/
#guard_msgs in
example : E → E := by
  intro
  show_term assumption
/--
info: found a partial proof, but the corresponding tactic failed:
  (expose_names; refine option2)

It may be possible to correct this proof by adding type annotations, explicitly specifying implicit arguments, or eliminating unnecessary function abstractions.
---
error: unsolved goals
a✝ : B
⊢ B
-/
#guard_msgs in
example : B → E := by
  intro
  show_term apply option2
/-- info: Try this: exact c_of_d d -/
#guard_msgs in
example : (n : Nat) → D n → C := by
  intro _ d
  show_term apply c_of_d d


/-! `rw?` exhibits the same behavior as above. -/
namespace Rw

opaque A : Type
@[instance] axiom inst : Inhabited A
opaque Foo (a a' : A) : Prop

noncomputable opaque a : A
axiom eq (a' : A) : a = a'

/--
info: Try this: (expose_names; rw [eq a'])
-- Foo a' a'
---
error: unsolved goals
a'✝ : A
⊢ Foo a'✝ a'✝
-/
#guard_msgs in
example : (a' : A) → Foo a a' := by
  intro
  rw?

noncomputable opaque a₁ : A
axiom eq_imp {a' : A} : a₁ = a'
/--
info: found an applicable rewrite lemma, but the corresponding tactic failed:
  (expose_names; rw [eq_imp])
  -- Foo a' a'

It may be possible to correct this proof by adding type annotations, explicitly specifying implicit arguments, or eliminating unnecessary function abstractions.
---
error: unsolved goals
a'✝ : A
⊢ Foo a'✝ a'✝
-/
#guard_msgs in
example : (a' : A) → Foo a₁ a' := by
  intro
  rw?
