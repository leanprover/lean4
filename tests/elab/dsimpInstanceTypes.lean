/-!
Tests for `backward.dsimp.instanceTypes`: `dsimp` and `simp` do not rewrite arguments
definitionally if that makes the type of an instance argument stop matching its expected type at
`.instances` transparency. Other rewrites still happen.
-/

class MyAdd (α : Type) where
  add : α → α → α

instance : MyAdd Nat := ⟨Nat.add⟩

def Foo := Nat

instance instMyAddFoo : MyAdd Foo := inferInstanceAs (MyAdd Nat)

def P {α : Type} (_ : α) : Prop := True

def Q (_ : Foo) : Prop := True

/-! Unfolding `Foo` in `@MyAdd.add Foo instMyAddFoo a b` would leave `instMyAddFoo : MyAdd Foo`
where an instance of `MyAdd Nat` is expected. -/

/-- error: `dsimp` made no progress -/
#guard_msgs in
example (a b : Foo) : Q (MyAdd.add a b) := by
  dsimp only [Foo]

/-- error: `simp` made no progress -/
#guard_msgs in
example (a b : Foo) : Q (MyAdd.add a b) := by
  simp only [Foo]

/-! The type argument of `P` has no instance depending on it, so it is unfolded. -/

example (a b : Foo) : P (MyAdd.add a b) := by
  dsimp only [Foo]
  guard_target =ₛ @P Nat (@MyAdd.add Foo instMyAddFoo a b)
  trivial

example (a b : Foo) : P (MyAdd.add a b) := by
  simp only [Foo]
  guard_target =ₛ @P Nat (@MyAdd.add Foo instMyAddFoo a b)
  trivial

example (a b : Foo) : P (MyAdd.add a b) := by
  set_option backward.dsimp.instanceTypes false in
  dsimp only [Foo]
  guard_target =ₛ @P Nat (@MyAdd.add Nat instMyAddFoo a b)
  trivial

example (a b : Foo) : P (MyAdd.add a b) := by
  set_option backward.dsimp.instanceTypes false in
  simp only [Foo]
  guard_target =ₛ @P Nat (@MyAdd.add Nat instMyAddFoo a b)
  trivial

/-! Rewrites that repair an instance argument, or leave it as wrong as it was, are kept. -/

example (inst : MyAdd Nat) (a b : Foo) : P (@MyAdd.add Foo inst a b) := by
  dsimp only [Foo]
  guard_target =ₛ @P Nat (@MyAdd.add Nat inst a b)
  trivial

def Bar := Nat

example (inst : MyAdd Bar) (a b : Foo) : P (@MyAdd.add Foo inst a b) := by
  dsimp only [Foo]
  guard_target =ₛ @P Nat (@MyAdd.add Nat inst a b)
  trivial
