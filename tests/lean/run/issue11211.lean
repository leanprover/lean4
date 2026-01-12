/-!
Checks that splitters have `Unit →` thunks and that nothing is confused because of that.
-/

set_option linter.unusedVariables false


-- set_option trace.Meta.Match.matchEqs true

def f (xs : List Nat) : Nat :=
  match xs with
  | [] => 1
  | _ => 2

/--
info: def f.match_1.{u_1} : (motive : List Nat → Sort u_1) →
  (xs : List Nat) → (Unit → motive []) → ((x : List Nat) → motive x) → motive xs
-/
#guard_msgs in
#print sig f.match_1

/--
info: private def f.match_1.splitter.{u_1} : (motive : List Nat → Sort u_1) →
  (xs : List Nat) → (Unit → motive []) → ((x : List Nat) → (x = [] → False) → motive x) → motive xs
-/
#guard_msgs(pass trace, all) in
#print sig f.match_1.splitter


/--
info: theorem f.match_1.congr_eq_1.{u_1} : ∀ (motive : List Nat → Sort u_1) (xs : List Nat) (h_1 : Unit → motive [])
  (h_2 : (x : List Nat) → motive x),
  xs = [] →
    (match xs with
      | [] => h_1 ()
      | x => h_2 x) ≍
      h_1 ()
-/
#guard_msgs(pass trace, all) in
#print sig f.match_1.congr_eq_1

--  set_option trace.split.debug true

theorem test1: f n ≤ 2 := by
  unfold f
  split <;> grind


theorem test2 : f n ≤ 2 := by
  unfold f
  grind

/--
info: theorem f.fun_cases : ∀ (motive : List Nat → Prop),
  motive [] → (∀ (xs : List Nat), (xs = [] → False) → motive xs) → ∀ (xs : List Nat), motive xs
-/
#guard_msgs(pass trace, all) in
#print sig f.fun_cases

def Option_map (f : α → β) : Option α → Option β
  | some x => some (f x)
  | none   => none

/--
info: def Option_map.match_1.{u_1, u_2} : {α : Type u_1} →
  (motive : Option α → Sort u_2) → (x : Option α) → ((x : α) → motive (some x)) → (Unit → motive none) → motive x
-/
#guard_msgs in
#print sig Option_map.match_1

/--
info: private def Option_map.match_1.splitter.{u_1, u_2} : {α : Type u_1} →
  (motive : Option α → Sort u_2) → (x : Option α) → ((x : α) → motive (some x)) → (Unit → motive none) → motive x :=
@Option_map.match_1
-/
#guard_msgs in
#print Option_map.match_1.splitter

/--
info: theorem Option_map.fun_cases.{u_1} : ∀ {α : Type u_1} (motive : Option α → Prop),
  (∀ (x : α), motive (some x)) → motive none → ∀ (x : Option α), motive x
-/
#guard_msgs(pass trace, all) in
#print sig Option_map.fun_cases

def List_map (f : α → β) (l : List α) : List β := match _ : l with
  | x::xs => f x :: List_map f xs
  | []   => []
termination_by l

def foo₁ (a : Nat) (ha : a = 37) :=
    (match h : a with | 42 => 23 | n => n) = 37

/--
info: private def foo₁.match_1.splitter.{u_1} : (motive : Nat → Sort u_1) →
  (a : Nat) → (a = 42 → motive 42) → ((n : Nat) → (n = 42 → False) → a = n → motive n) → motive a
-/
#guard_msgs in
#print sig foo₁.match_1.splitter
