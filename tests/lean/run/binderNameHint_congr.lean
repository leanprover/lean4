section no_congr
/--
error: tactic 'fail' failed
xs : List Nat
⊢ xs = List.map (fun y => 1 + y) xs
-/
#guard_msgs in
example : xs = List.map (fun y => 1 + (y + 1 - 1)) xs := by
  simp
  fail

end no_congr

section with_congr

/--
info: List.map_congr_left.{u_1, u_2} {α✝ : Type u_1} {l : List α✝} {α✝¹ : Type u_2} {f g : α✝ → α✝¹}
  (h : ∀ (a : α✝), a ∈ l → f a = g a) : List.map f l = List.map g l
-/
#guard_msgs in
#check List.map_congr_left

attribute [local congr] List.map_congr_left

/--
error: tactic 'fail' failed
xs : List Nat
⊢ xs = List.map (fun a => 1 + a) xs
-/
#guard_msgs in
example : xs = List.map (fun y => 1 + (y + 1 - 1)) xs := by
  simp -- NB: Changes variable name!
  fail

end with_congr

section with_congr_hint

-- Trying to use the binderNameHint on a congruence rule

theorem List.map_congr_left'' {f g : α → β}
  (h : ∀ (a : α), a ∈ l → binderNameHint a f (f a) = g a) :
  List.map f l = List.map g l  := List.map_congr_left h

attribute [local congr] List.map_congr_left''

-- set_option trace.Debug.Meta.Tactic.simp true
-- set_option pp.instantiateMVars false
-- set_option trace.Debug.Meta.Tactic.simp.congr true

/--
error: tactic 'fail' failed
xs : List Nat
⊢ xs = List.map (fun y => 1 + y) xs
-/
#guard_msgs in
example : xs = List.map (fun y => 1 + (y + 1 - 1)) xs := by
  simp
  fail

end with_congr_hint
