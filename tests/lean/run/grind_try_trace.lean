module
@[expose] public section -- TODO: remove after we fix congr_eq
reset_grind_attrs%

/--
info: Try these:
  [apply] simp
  [apply] simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs (info) in
example : [1, 2] ≠ [] := by
  try?

/--
info: Try these:
  [apply] simp +arith
  [apply] simp +arith only [ge_iff_le]
  [apply] grind
  [apply] grind only
-/
#guard_msgs (info) in
example : 4 + x + y ≥ 1 + x  := by
  try?

/--
info: Try these:
  [apply] simp +arith
  [apply] grind
-/
#guard_msgs (info) in
example : 4 + x + y ≥ 1 + x  := by
  try? -only

/--
info: Try these:
  [apply] grind
  [apply] grind only
-/
#guard_msgs (info) in
example (f : Nat → Nat) : f a = b → a = c → f c = b := by
  try?

public def f : Nat → Nat
  | 0 => 1
  | _ => 2

/--
info: Try these:
  [apply] solve_by_elim
  [apply] grind [= f]
  [apply] grind only [f]
  [apply] grind => instantiate only [f]
-/
#guard_msgs (info) in
example : f (f 0) > 0 := by
  try?

/--
info: Try these:
  [apply] grind [= f.eq_def]
  [apply] grind only [= f.eq_def, #6818]
  [apply] grind only [= f.eq_def]
  [apply] grind =>
    instantiate only [= f.eq_def]
    instantiate only
    cases #6818 <;> instantiate only
-/
#guard_msgs (info) in
example : f x > 0 := by
  try?

def app : List α → List α → List α
  | [], bs => bs
  | a::as, bs => a :: app as bs

/--
info: Try these:
  [apply] rfl
  [apply] grind [= app]
  [apply] grind only [app]
  [apply] grind =>
    instantiate only [app]
    instantiate only [app]
    instantiate only [app]
-/
#guard_msgs (info) in
example : app [a, b] [c] = [a, b, c] := by
  try?

/--
info: Try these:
  [apply] (fun_induction app as bs) <;> grind [= app]
  [apply] (fun_induction app as bs) <;> grind only [app]
  [apply] (fun_induction app as bs) <;> grind => instantiate only [app]
-/
#guard_msgs (info) in
example : app (app as bs) cs = app as (app bs cs) := by
  try?

/--
info: Try this:
  [apply] (fun_induction app as bs) <;> grind [= app]
-/
#guard_msgs (info) in
example : app (app as bs) cs = app as (app bs cs) := by
  try? (max := 1)

/--
info: Try these:
  [apply] · expose_names; fun_induction app as bs_1 <;> grind [= app]
  [apply] · expose_names; fun_induction app as bs_1 <;> grind only [app]
  [apply] · expose_names; fun_induction app as bs_1 <;> grind => instantiate only [app]
-/
#guard_msgs (info) in
example : app (app as bs) cs = app as (app bs cs) := by
  have bs := 20 -- shadow variable in the goal
  try?

/--
info: Try these:
  [apply] · expose_names; fun_induction app as bs <;> grind [= app]
  [apply] · expose_names; fun_induction app as bs <;> grind only [app]
  [apply] · expose_names; fun_induction app as bs <;> grind => instantiate only [app]
-/
#guard_msgs (info) in
example : app (app as bs) cs = app as (app bs cs) := by
  revert as bs cs
  intro _ _ _
  -- `as`, `bs`, and `cs` now have inaccessible names.
  try?

def concat : List α → α → List α
  | .nil,       b => .cons b .nil
  | .cons a as, b => .cons a (concat as b)

attribute [simp] concat

/--
info: Try these:
  [apply] (fun_induction concat) <;> simp_all
  [apply] (fun_induction concat) <;> simp [*]
  [apply] ·
    fun_induction concat
    · rfl
    · solve_by_elim
  [apply] ·
    fun_induction concat
    · grind
    · solve_by_elim
-/
#guard_msgs (info) in
example (as : List α) (a : α) : concat as a = as ++ [a] := by
  try? -only

/--
info: Try these:
  [apply] (fun_induction concat) <;> simp_all
  [apply] ·
    fun_induction concat
    · simp
    · simp [*]
  [apply] ·
    fun_induction concat
    · rfl
    · solve_by_elim
  [apply] ·
    fun_induction concat
    · grind
    · solve_by_elim
-/
#guard_msgs (info) in
example (as : List α) (a : α) : concat as a = as ++ [a] := by
  try? -only -merge

def map (f : α → β) : List α → List β
  | [] => []
  | x::xs => f x :: map f xs

/--
info: Try these:
  [apply] (fun_induction map f xs) <;> grind [= map]
  [apply] (fun_induction map f xs) <;> grind only [map]
  [apply] (fun_induction map f xs) <;> grind => instantiate only [map]
-/
#guard_msgs (info) in
theorem map_map (f : α → β) (g : β → γ) xs :
  map g (map f xs) = map (fun x => g (f x)) xs := by
  try?


def foo : Nat → Nat
  | 0   => 1
  | x+1 => foo x - 1

/--
info: Try these:
  [apply] ·
    fun_induction foo
    · solve_by_elim
    · sorry
  [apply] ·
    fun_induction foo
    · simp
    · sorry
  [apply] ·
    fun_induction foo
    · grind
    · sorry
  [apply] ·
    fun_induction foo
    · simp_all
    · sorry
-/
#guard_msgs (info) in
example : foo x > 0 := by
  try? +missing -only -- `try?` does not solve all subgoals.
  sorry

/--
error: Tactic `try?` failed: consider using `grind` manually, or `try? +missing` for partial proofs containing `sorry`

x : Nat
⊢ foo x > 0
-/
#guard_msgs (error) in
example : foo x > 0 := by
  try?

@[simp] def bla : List Nat → List Nat → List Nat
  | [],    ys => ys.reverse
  | _::xs, ys => bla xs ys

attribute [grind] List.length_reverse bla

/--
info: Try these:
  [apply] (fun_induction bla) <;> grind
  [apply] (fun_induction bla) <;> simp_all
  [apply] (fun_induction bla) <;> simp [*]
  [apply] (fun_induction bla) <;> simp only [List.length_reverse, *]
  [apply] (fun_induction bla) <;> grind only [= List.length_reverse]
-/
#guard_msgs (info) in
example : (bla xs ys).length = ys.length := by
  try?
