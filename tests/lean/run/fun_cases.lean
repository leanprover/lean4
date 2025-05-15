/--
info: Option.map.fun_cases.{u_1, u_2} (motive : {α : Type u_1} → {β : Type u_2} → (α → β) → Option α → Prop)
  (case1 : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (x : α), motive f (some x))
  (case2 : ∀ {α : Type u_1} {β : Type u_2} (f : α → β), motive f none) {α : Type u_1} {β : Type u_2} (f : α → β)
  (x✝ : Option α) : motive f x✝
-/
#guard_msgs in
#check Option.map.fun_cases

example (x : Option Nat) (f : Nat → Nat) : (x.map f).isSome = x.isSome := by
  cases f, x using Option.map.fun_cases
  case case1 x => simp
  case case2 =>   simp

/--
info: List.map.fun_cases.{u, v} (motive : {α : Type u} → {β : Type v} → (α → β) → List α → Prop)
  (case1 : ∀ {α : Type u} {β : Type v} (f : α → β), motive f [])
  (case2 : ∀ {α : Type u} {β : Type v} (f : α → β) (a : α) (as : List α), motive f (a :: as)) {α : Type u} {β : Type v}
  (f : α → β) (x✝ : List α) : motive f x✝
-/
#guard_msgs in
#check List.map.fun_cases

/--
info: List.find?.fun_cases.{u} (motive : {α : Type u} → (α → Bool) → List α → Prop)
  (case1 : ∀ {α : Type u} (p : α → Bool), motive p [])
  (case2 : ∀ {α : Type u} (p : α → Bool) (a : α) (as : List α), p a = true → motive p (a :: as))
  (case3 : ∀ {α : Type u} (p : α → Bool) (a : α) (as : List α), p a = false → motive p (a :: as)) {α : Type u}
  (p : α → Bool) (x✝ : List α) : motive p x✝
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
info: areTheseTargetsUnchanged.fun_cases (motive : Nat → Nat → Prop) (case1 : ∀ (y : Nat), motive y y)
  (case2 : ∀ (x y : Nat), ¬x = y → motive x y) (x y : Nat) : motive x y
-/
#guard_msgs in
#check areTheseTargetsUnchanged.fun_cases
