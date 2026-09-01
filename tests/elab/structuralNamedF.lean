-- Test that structural recursion creates a named `_f` helper definition
-- for the functional passed to `brecOn`.

-- Simple case: single function
def addAdjacent : List Nat → List Nat
  | []       => []
  | [a]      => [a]
  | a::b::as => (a+b) :: addAdjacent as

-- The `_f` helper should exist in the environment
/-- info: addAdjacent._f : (x : List Nat) → List.below x → List Nat -/
#guard_msgs in #check @addAdjacent._f

-- Verify computation still works
/-- info: [3, 7] -/
#guard_msgs in #eval addAdjacent [1, 2, 3, 4]

-- Mutual recursion: each function gets its own `_f`
mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n

  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end

/-- info: even._f : (x : Nat) → Nat.below x → Bool -/
#guard_msgs in #check @even._f

/-- info: odd._f : (x : Nat) → Nat.below x → Bool -/
#guard_msgs in #check @odd._f

/-- info: true -/
#guard_msgs in #eval even 4

/-- info: true -/
#guard_msgs in #eval odd 3

-- With fixed parameters
def myMap (f : α → β) : List α → List β
  | []    => []
  | x::xs => f x :: myMap f xs

/-- info: @myMap._f : {α : Type u_1} → {β : Type u_2} → (α → β) → (x : List α) → List.below x → List β -/
#guard_msgs in #check @myMap._f

-- The `_f` helper shows up with a helpful name in kernel diagnostics
def fib (n : Nat) :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib x + fib (x+1)
termination_by structural n

/--
trace: [diag] Diagnostics
  [reduction] unfolded declarations (max: 79, num: 4):
    [reduction] Nat.rec ↦ 79
    [reduction] Add.add ↦ 41
    [reduction] HAdd.hAdd ↦ 41
    [reduction] fib ↦ 40
  [reduction] unfolded reducible declarations (max: 79, num: 1):
    [reduction] Nat.casesOn ↦ 79
  [kernel] unfolded declarations (max: 80, num: 6):
    [kernel] Nat.rec ↦ 80
    [kernel] Nat.casesOn ↦ 77
    [kernel] fib._f ↦ 39
    [kernel] fib.match_1 ↦ 39
    [kernel] Add.add ↦ 36
    [kernel] HAdd.hAdd ↦ 36
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 10 in
theorem fib_20 : fib 20 = 10946 := rfl
