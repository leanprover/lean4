/--
info: Option.map.cases.{u_1, u_2} (motive : Prop) {α : Type u_1} {β : Type u_2} (f : α → β) (x✝ : Option α)
  (case1 : ∀ (x : α), x✝ = some x → motive) (case2 : x✝ = none → motive) : motive
-/
#guard_msgs in
#check Option.map.cases

example (x : Option Nat) (f : Nat → Nat) : (x.map f).isSome = x.isSome := by
  apply Option.map.cases _ f x
  case case1 =>
    intro y hx
    simp [-Option.isSome_map', hx]
  case case2 =>
    intro hx
    simp [-Option.isSome_map', hx]
