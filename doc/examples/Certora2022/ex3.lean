/- Enumerated types -/

inductive Weekday where
  | sunday | monday | tuesday | wednesday
  | thursday | friday | saturday

#check Weekday.sunday
-- Weekday

open Weekday
#check sunday

def natOfWeekday (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

def Weekday.next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def Weekday.previous : Weekday → Weekday
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

/- Proving theorems using tactics -/

theorem Weekday.next_previous (d : Weekday) : d.next.previous = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

theorem Weekday.next_previous' (d : Weekday) : d.next.previous = d := by -- switch to tactic mode
  cases d -- Creates 7 goals
  rfl; rfl; rfl; rfl; rfl; rfl; rfl

theorem Weekday.next_previous'' (d : Weekday) : d.next.previous = d := by
  cases d <;> rfl
