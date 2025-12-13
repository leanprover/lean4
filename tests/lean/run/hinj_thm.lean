opaque double : Nat → Nat
def P (n : Nat) : Prop := n >= 0
theorem pax (n : Nat) : P n := by grind [P]
def T (n : Nat) : Type := Vector Nat n

inductive Foo' (α β : Type u) : (n : Nat) → P n -> Type u
  | even (a : α) (n : Nat) (v : T n) (h : P n) : Foo' α β (double n) (pax _)
  | odd  (b : β) (n : Nat) (v : T n) : Foo' α β (Nat.succ (double n)) (pax _)

/--
info: Foo'.even.hinj.{u} {α β : Type u} {a : α} {n : Nat} {v : T n} {h : P n} {a✝ : α} {n✝ : Nat} {v✝ : T n✝} {h✝ : P n✝} :
  double n = double n✝ → ⋯ ≍ ⋯ → Foo'.even a n v h ≍ Foo'.even a✝ n✝ v✝ h✝ → a = a✝ ∧ n = n✝ ∧ v ≍ v✝
-/
#guard_msgs in
#check Foo'.even.hinj

/--
info: Foo'.odd.hinj.{u} {α β : Type u} {b : β} {n : Nat} {v : T n} {b✝ : β} {n✝ : Nat} {v✝ : T n✝} :
  (double n).succ = (double n✝).succ → ⋯ ≍ ⋯ → Foo'.odd b n v ≍ Foo'.odd b✝ n✝ v✝ → b = b✝ ∧ n = n✝ ∧ v ≍ v✝
-/
#guard_msgs in
#check Foo'.odd.hinj
