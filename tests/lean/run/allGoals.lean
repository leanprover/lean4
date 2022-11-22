inductive Weekday where
  | sunday    : Weekday
  | monday    : Weekday
  | tuesday   : Weekday
  | wednesday : Weekday
  | thursday  : Weekday
  | friday    : Weekday
  | saturday  : Weekday

def Weekday.next : Weekday -> Weekday :=
  fun d => match d with
    | sunday    => monday
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => saturday
    | saturday  => sunday

def Weekday.previous : Weekday -> Weekday
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

theorem Weekday.nextOfPrevious (d : Weekday) : next (previous d) = d := by
  cases d
  all_goals rfl

theorem Weekday.nextOfPrevious' (d : Weekday) : previous (next d) = d ∧ next (previous d) = d := by
  apply And.intro
  cases d <;> rfl
  cases d <;> rfl

theorem Weekday.nextOfPrevious'' (d : Weekday) : previous (next d) = d ∧ next (previous d) = d := by
  apply And.intro <;> cases d <;> rfl

open Lean.Parser.Tactic in
macro "rwd " x:term : tactic => `(tactic| (rw [$x:term]; done))

theorem ex (a b c : α) (h₁ : a = b) (h₂ : a = c) : b = a ∧ c = a := by
  apply And.intro <;> first | rwd h₁ | rwd h₂

theorem idEq (a : α) : id a = a :=
  rfl

theorem Weekday.test (d : Weekday) : next (previous d) = id d := by
  cases d
  trace_state
  all_goals rw [idEq]
  trace_state
  all_goals rfl

theorem Weekday.test2 (d : Weekday) : next (previous d) = id d := by
  cases d <;> rw [idEq]
  trace_state
  all_goals rfl

def bug {a b c : Nat} (h₁ : a = b) (h₂ : b = c) : a = c := by
  apply Eq.trans <;> assumption
