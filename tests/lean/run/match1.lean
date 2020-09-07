new_frontend

def f (xs : List Nat) : List Bool :=
xs.map fun
  | 0 => true
  | _ => false

#eval f [1, 2, 0, 2]

theorem ex1 : f [1, 0, 2] = [false, true, false] :=
rfl

#check f

def g (xs : List Nat) : List Bool :=
xs.map $ by {
  intro
    | 0 => exact true
    | _ => exact false
}

theorem ex2 : g [1, 0, 2] = [false, true, false] :=
rfl

theorem ex3 {p q r : Prop} : p ∨ q → r → (q ∧ r) ∨ (p ∧ r) :=
by intro
 | Or.inl hp, h => { apply Or.inr; apply And.intro; assumption; assumption }
 | Or.inr hq, h => { apply Or.inl; exact ⟨hq, h⟩ }

inductive C
| mk₁ : Nat → C
| mk₂ : Nat → Nat → C

def C.x : C → Nat
| C.mk₁ x   => x
| C.mk₂ x _ => x
