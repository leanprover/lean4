import Std.Tactic.Do
import Std

open Std Do

set_option grind.warning false
set_option mvcgen.warning false

def nodup (l : List Int) : Bool := Id.run do
  let mut seen : HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct_vanilla (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 =>
    exact Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  all_goals mleave; grind

theorem nodup_correct_invariants (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · Invariant.withEarlyReturn
   (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝) -- minimal indentation here is part of the test
   (onContinue := fun traversalState seen =>
   ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  all_goals grind

theorem nodup_correct_invariants_with_pretac (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  with grind

theorem nodup_correct_invariants_with_cases (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  with
  | vc1 => grind
  | vc2 => grind
  | vc3 => grind
  | vc4 => grind
  | vc5 => grind

theorem nodup_correct_invariants_with_pretac_cases (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  with mleave -- mleave is a no-op here, but we are just testing the grammar
  | vc1 => grind
  | vc2 | vc3 | vc4 => grind
  | vc5 => grind

theorem nodup_correct_invariants_with_cases_error (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  with mleave -- mleave is a no-op here, but we are just testing the grammar
  | vc1 => grind
  | vc2 | vc3 | vc4 => grind
  | vc5 => grind

theorem test_with_pretac {m : Option Nat} (h : m = some 4) :
  ⦃⌜True⌝⦄
  (match m with
  | some n => (set n : StateM Nat PUnit)
  | none => set 0)
  ⦃⇓ r s => ⌜s = 4⌝⦄ := by
  mvcgen with simp_all

theorem test_with_cases {m : Option Nat} (h : m = some 4) :
  ⦃⌜True⌝⦄
  (match m with
  | some n => (set n : StateM Nat PUnit)
  | none => set 0)
  ⦃⇓ r s => ⌜s = 4⌝⦄ := by
  mvcgen
  with
  | vc1 => grind
  | vc2 => grind

theorem test_with_pretac_cases {m : Option Nat} (h : m = some 4) :
  ⦃⌜True⌝⦄
  (match m with
  | some n => (set n : StateM Nat PUnit)
  | none => set 0)
  ⦃⇓ r s => ⌜s = 4⌝⦄ := by
  mvcgen
  with simp -- `simp` is a no-op on some goals, but it should not fail
  | vc1 => grind
  | vc2 => grind

def nodup_twice (l : List Int) : Bool := Id.run do
  let mut seen : HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  let mut seen2 : HashSet Int := ∅
  for x in l do
    if x ∈ seen2 then
      return false
    seen2 := seen2.insert x
  return true

theorem nodup_twice_correct_invariants_with (l : List Int) : nodup_twice l ↔ l.Nodup := by
  generalize h : nodup_twice l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  with grind

theorem nodup_twice_correct_invariants_multiple_with (l : List Int) : nodup_twice l ↔ l.Nodup := by
  generalize h : nodup_twice l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  with grind

/--
error: Lacking definitions for the following invariants.

  Invariant l (MProd (Option Bool) (HashSet Int)) PostShape.pure
-/
#guard_msgs in
theorem nodup_twice_missing_one_invariant (l : List Int) : nodup_twice l ↔ l.Nodup := by
  generalize h : nodup_twice l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  with grind

/--
error: Lacking definitions for the following invariants.

  Invariant l (MProd (Option Bool) (HashSet Int)) PostShape.pure
  ⏎
  Invariant l (MProd (Option Bool) (HashSet Int)) PostShape.pure
-/
#guard_msgs in
theorem nodup_twice_missing_two_invariants (l : List Int) : nodup_twice l ↔ l.Nodup := by
  generalize h : nodup_twice l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  with grind
