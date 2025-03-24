/-!
# Library search should not return invalid tactics

https://github.com/leanprover/lean4/issues/5407

The library-search tactics `exact?` and `apply?` should not suggest proof terms that do not
compile. If such proof terms are generated, these tactics should instead provide users with
appropriate feedback.
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
  exact fun a => (fun {n} => odd_iff.mpr) a
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
/--
info: Try this: (expose_names; exact imp h_1 h)
-/
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
  exact EqExplicit.intro (fun f => (fun g x => g x) f) id rfl
-/
#guard_msgs in
example : EqExplicit (fun (f : α → β) => (fun g x => g x) f) id := by
  exact?

/-! `apply?` logs info instead of erroring -/
opaque D : Prop
axiom option1 : A → D
axiom option2 {_ : B} : D
/--
info: Try this: refine option1 ?_
---
info: found a partial proof, but the corresponding tactic failed:
  refine option2
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : D := by apply?
