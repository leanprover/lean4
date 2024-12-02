/--
info: Option.map.fun_cases.{u_1, u_2} (motive : Prop) {α : Type u_1} {β : Type u_2} (f : α → β) (x✝ : Option α)
  (case1 : ∀ (x : α), x✝ = some x → motive) (case2 : x✝ = none → motive) : motive
-/
#guard_msgs in
#check Option.map.fun_cases

example (x : Option Nat) (f : Nat → Nat) : (x.map f).isSome = x.isSome := by
  apply Option.map.fun_cases _ f x
  case case1 => intro y hx; simp [-Option.isSome_map', hx]
  case case2 => intro hx; simp [-Option.isSome_map', hx]

/--
info: List.map.fun_cases.{u, v} (motive : Prop) {α : Type u} {β : Type v} (f : α → β) (x✝ : List α) (case1 : x✝ = [] → motive)
  (case2 : ∀ (a : α) (as : List α), x✝ = a :: as → motive) : motive
-/
#guard_msgs in
#check List.map.fun_cases

/--
info: List.find?.fun_cases.{u} (motive : Prop) {α : Type u} (p : α → Bool) (x✝ : List α) (case1 : x✝ = [] → motive)
  (case2 : ∀ (a : α) (as : List α), x✝ = a :: as → p a = true → motive)
  (case3 : ∀ (a : α) (as : List α), x✝ = a :: as → p a = false → motive) : motive
-/
#guard_msgs in
#check List.find?.fun_cases
