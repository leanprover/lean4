import Std

/-!
  `mvcgen with grind` should behave like `induction ... with grind` and fail if `grind` fails on
  one of the goals.
-/

open Std.Do

set_option mvcgen.warning false
set_option warn.sorry false

variable {α : Type}

@[grind]
def List.last? (as : List α) : Option α :=
  match as with
  | [] => none
  | [a] => some a
  | _ :: bs => last? bs

open List

example (as bs : List α) (h : bs ≠ []) :
  (as ++ bs).last? = bs.last? := by
  fail_if_success induction bs generalizing as with simp
  sorry

def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct_invariants_with_pretac (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  fail_if_success mvcgen with grind
  sorry
