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

/--
info: case sunday
⊢ Weekday.sunday.previous.next = id Weekday.sunday

case monday
⊢ Weekday.monday.previous.next = id Weekday.monday

case tuesday
⊢ Weekday.tuesday.previous.next = id Weekday.tuesday

case wednesday
⊢ Weekday.wednesday.previous.next = id Weekday.wednesday

case thursday
⊢ Weekday.thursday.previous.next = id Weekday.thursday

case friday
⊢ Weekday.friday.previous.next = id Weekday.friday

case saturday
⊢ Weekday.saturday.previous.next = id Weekday.saturday
---
info: case sunday
⊢ Weekday.sunday.previous.next = Weekday.sunday

case monday
⊢ Weekday.monday.previous.next = Weekday.monday

case tuesday
⊢ Weekday.tuesday.previous.next = Weekday.tuesday

case wednesday
⊢ Weekday.wednesday.previous.next = Weekday.wednesday

case thursday
⊢ Weekday.thursday.previous.next = Weekday.thursday

case friday
⊢ Weekday.friday.previous.next = Weekday.friday

case saturday
⊢ Weekday.saturday.previous.next = Weekday.saturday
-/
#guard_msgs in
theorem Weekday.test (d : Weekday) : next (previous d) = id d := by
  cases d
  trace_state
  all_goals rw [idEq]
  trace_state
  all_goals rfl

/--
info: case sunday
⊢ Weekday.sunday.previous.next = Weekday.sunday

case monday
⊢ Weekday.monday.previous.next = Weekday.monday

case tuesday
⊢ Weekday.tuesday.previous.next = Weekday.tuesday

case wednesday
⊢ Weekday.wednesday.previous.next = Weekday.wednesday

case thursday
⊢ Weekday.thursday.previous.next = Weekday.thursday

case friday
⊢ Weekday.friday.previous.next = Weekday.friday

case saturday
⊢ Weekday.saturday.previous.next = Weekday.saturday
-/
#guard_msgs in
theorem Weekday.test2 (d : Weekday) : next (previous d) = id d := by
  cases d <;> rw [idEq]
  trace_state
  all_goals rfl

def bug {a b c : Nat} (h₁ : a = b) (h₂ : b = c) : a = c := by
  apply Eq.trans <;> assumption
