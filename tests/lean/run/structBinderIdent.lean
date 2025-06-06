structure Δ n where
  val : Fin (n + 1)
  deriving Inhabited

/--
info: Δ (n : Nat) : Type
-/
#guard_msgs in
#check Δ

structure Prod₃ α β γ : Type u extends toProd : α × β where
  trd : (γ : Type u)

/--
info: Prod₃.{u} (α β γ : Type u) : Type u
-/
#guard_msgs in
#check Prod₃
