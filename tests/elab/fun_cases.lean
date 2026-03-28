/--
info: Option.map.fun_cases.{u_1} {α : Type u_1} (motive : Option α → Prop) (case1 : ∀ (x : α), motive (some x))
  (case2 : motive none) (x✝ : Option α) : motive x✝
-/
#guard_msgs(pass trace, all) in
#check Option.map.fun_cases

example (x : Option Nat) (f : Nat → Nat) : (x.map f).isSome = x.isSome := by
  cases x using Option.map.fun_cases
  case case1 x => simp
  case case2 =>   simp

/--
info: List.map.fun_cases.{u_1} {α : Type u_1} (motive : List α → Prop) (case1 : motive [])
  (case2 : ∀ (head : α) (tail : List α), motive (head :: tail)) (x✝ : List α) : motive x✝
-/
#guard_msgs in
#check List.map.fun_cases

/--
info: List.find?.fun_cases.{u} {α : Type u} (p : α → Bool) (motive : List α → Prop) (case1 : motive [])
  (case2 : ∀ (a : α) (as : List α), p a = true → motive (a :: as))
  (case3 : ∀ (a : α) (as : List α), p a = false → motive (a :: as)) (x✝ : List α) : motive x✝
-/
#guard_msgs in
#check List.find?.fun_cases


-- This tests shows that its not so easy to post-hoc recognize that `x` could be a parameter, but
-- `y` should be a target of the `fun_cases` principle (or the other way around)
def areTheseTargetsUnchanged (x y : Nat) : Bool :=
  if _ : x = y then
    true
  else
    false

/--
info: areTheseTargetsUnchanged.fun_cases (x y : Nat) (motive : Prop) (case1 : x = y → motive) (case2 : ¬x = y → motive) :
  motive
-/
#guard_msgs in
#check areTheseTargetsUnchanged.fun_cases
