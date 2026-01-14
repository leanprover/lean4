import Init.Tactics

set_option autoImplicit true
set_option linter.missingDocs false

-- testing that the attribute is recognized
@[symm] def eq_symm {α : Type} (a b : α) : a = b → b = a := Eq.symm

example (a b : Nat) : a = b → b = a := by intros; symm; assumption
example (a b : Nat) : a = b → True → b = a := by intro h _; symm at h; assumption

def sameParity : Nat → Nat → Prop
  | n, m => n % 2 = m % 2

@[symm] def sameParity_symm (n m : Nat) : sameParity n m → sameParity m n := Eq.symm

example (a b : Nat) : sameParity a b → sameParity b a := by intros; symm; assumption

def MyEq (n m : Nat) := ∃ k, n + k = m ∧ m + k = n

@[symm] theorem MyEq.symm {n m : Nat} (h : MyEq n m) : MyEq m n := by
  rcases h with ⟨k, h1, h2⟩
  exact ⟨k, h2, h1⟩

example {n m : Nat} (h : MyEq n m) : MyEq m n := by
  symm
  assumption
