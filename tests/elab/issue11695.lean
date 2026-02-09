/-! Regression tests from working on PR 11695 -/

set_option linter.unusedVariables false

-- set_option trace.Meta.Match.match true

def dependent : (n : Nat) → (m : Fin n) → Nat
 | 0, i => Fin.elim0 i
 | .succ 0, 0 => 0
 | .succ (.succ n), 0 => 1
 | .succ (.succ n), ⟨.succ m, h⟩ => 2


inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def f1 : {n : Nat} → (v : Vec α n) → Nat
  | 0, _          => 0
  | _, .cons x xs => 1

def f2 : {n : Nat} → (v : Vec α n) → Nat
  | _, Vec.nil   => 0
  | .succ n, _   => 1
